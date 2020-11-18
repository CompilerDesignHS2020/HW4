open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let debug = false in
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
          if debug then print_endline@@ "found label: "^l;
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> if debug then print_endline@@ "found terminator"; (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> if debug then print_endline@@ "found insn with uid: "^uid ; (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) -> if debug then print_endline@@ "found gid with: "^gid; ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> if debug then print_endline@@ "found e with uid: "^uid; (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | CNull(r) -> 
    let uid = gensym "null_const" in 
    (I64,Ll.Id(uid), [I(uid, Binop(Add, Ptr(cmp_rty r), Const(0L), Const(0L)))] )

  | CBool(bo) -> 
    let b = if bo then 1L else 0L in 
    let uid = gensym "bool_const" in
      (I1,Ll.Id(uid), [I(uid, Binop(Add, I1, Const(0L), Const(b)))] )

  | CInt(i) -> 
    let uid = gensym "int_const" in 
    (I64,Ll.Id(uid), [I(uid, Binop(Add, I64, Const(0L), Const(i)))] )

  | CStr(s) -> 
    let gid = gensym "global_string_const" in            
    let uid = gensym "string_ptr" in 
    (Ptr(I8),Ll.Id(uid), 
    [
      G(gid, (Array(String.length s +1, I8), GString(s)));
      I(uid, Gep(Ptr(Array(String.length s +1, I8)), Ll.Gid(gid), [Const(0L); Const(0L)]))
    ])

  | NewArr(arr_ty, size_exp) ->
    (*%_raw_array5 = call i64*  @oat_alloc_array(i64 3)  *)
    (*%_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }* *)
    let (_, ll_size_id, size_exp_stream) = cmp_exp c size_exp in
    let (alloc_ty, arr_alloc_id, arr_alloc_stream) = oat_alloc_array arr_ty ll_size_id in

    (* %_x7 = alloca { i64, [0 x i64] }*  *)
    (*
    let ll_arr_pointer_id = gensym "arr_id" in
    let ptr_alloc_stream = [I(ll_arr_pointer_id ,Alloca(alloc_ty))] in
    *)

    (* store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7 *)
    (*
    let arr_store_stream = [I(ll_arr_pointer_id ,Store(alloc_ty, arr_alloc_id, Ll.Id(ll_arr_pointer_id)))] in
    *)
    (*print_endline @@ string_of_ty alloc_ty;*)
    (*arr_alloc_stream and ptr_Alloc ist other way round than in doc, but should work*)
    (alloc_ty, arr_alloc_id, size_exp_stream@(List.rev arr_alloc_stream))

  | CArr(arr_ty, arr_elems) -> 
    let arr_elem_length = List.length arr_elems in

    (*create empty array of size length(arr_elems)*)
    let size_exp = CInt (Int64.of_int (arr_elem_length)) in
    let (new_arr_ty, new_arr_id, new_arr_stream) = cmp_exp c (no_loc (NewArr (arr_ty, no_loc size_exp))) in

    (* we iterate over the (2)) and (3) for every assn of an array elem:
      (1) %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7 
      (2) %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
          { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2
      (3) store i64 3, i64* %_index_ptr11 *)

    let base_uid = gensym "arr_base_uid" in
    let load_stream = [I(base_uid , Load(new_arr_ty, new_arr_id))] in
    
    (*return ll_ty, ll_op, ll_stream*)
    
    let rec assn_rem_elems rem_elems act_ind =
      begin match rem_elems with
        | (h::tl) -> 
          let (act_exp_ty, act_exp_op, act_exp_stream) = cmp_exp c h in
          let act_elem_id = gensym "act_elem_id" in
          let ind_list = [Const(0L)]@[Const(Int64.of_int act_ind)] in
          
          act_exp_stream@
          [I(act_elem_id, Gep(new_arr_ty, Ll.Id(base_uid), ind_list))]@
          [I(gensym "store_uid", Store(act_exp_ty, act_exp_op, Ll.Id(act_elem_id)))]@
          (assn_rem_elems tl (act_ind + 1))
        | [] -> [] 
      end 
    in
    let assn_stream = assn_rem_elems arr_elems 0 in
    (cmp_ty arr_ty, new_arr_id, new_arr_stream@load_stream@assn_stream)

  | Index (arr_exp, ind_exp) ->
    (*  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr   *)
    let (arr_ty, arr_base_ptr, arr_stream) = cmp_exp c arr_exp in
    (*
    let base_uid = gensym "arr_base_uid" in
    let load_arr_ptr_stream = [I(base_uid , Load(arr_ty, arr_id))] in
    *)

    (* %_index_ptr14 = getelementptr { i64, [0 x i64] }, 
     { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  *)
    let (_, ind_uid, ind_stream) = cmp_exp c ind_exp in
    let ind_ptr_id = gensym "ind_ptr_id" in
    let gep_stream = [I(ind_ptr_id, Gep(arr_ty, arr_base_ptr, [Const(0L); Const(1L); ind_uid]))] in

    (*  %_index15 = load i64, i64* %_index_ptr14  *)
    let elem_id = gensym "elem_id" in
    (*print_endline @@ string_of_ty arr_ty;*)
    let inner_type = 
    begin match arr_ty with
      | Ptr(Struct([I64; Array(n,t)])) -> t 
      | _ -> failwith "wrong inner type"
    end 
    in
    let load_elem_stream = [I(elem_id , Load(Ptr(inner_type) , Ll.Id(ind_ptr_id)))] in

    (inner_type, Ll.Id(elem_id), arr_stream@ind_stream@gep_stream@load_elem_stream)
  
  | Call (e1, arg_list) -> 
      (* lookup function label and type*)
      let (ll_ty, ll_lbl) = 
        begin match e1.elt with
          | Id(i) -> Ctxt.lookup_function i c
          | _ -> failwith "SCall didn't get an Id"
        end
      in

      (* get function ret value *)
      let (arg_types, ret_type) = 
      begin match ll_ty with
      | Ptr (t) -> 
        begin match t with
          | Fun(arg_types, ret_type) -> arg_types, ret_type
          | _ -> failwith "ptr has not type function"
        end
      | Fun (ts,t)  -> (ts,t)
      | _ -> failwith "function has not type function or ptr"
       end
      in

      let ll_fun_type = Fun(arg_types, ret_type)  in

      let (arg_ty_exp_li, arg_stream) = cmp_exps c arg_list in
      let ret_uid = gensym "call_ret_uid" in
      (ret_type, Ll.Id(ret_uid), arg_stream@[I(ret_uid, Ll.Call(ret_type, ll_lbl, arg_ty_exp_li))])
      
  | Id(i) ->
    let (ll_ty, ll_operand) = Ctxt.lookup i c in
    let uid = gensym (i^"_content") in 
    (ll_ty, Ll.Id(uid),[
      I(uid, Load(Ptr(ll_ty), ll_operand))
    ])

  | Bop((ast_bop, e1, e2)) -> 
      (*convert ast binop to ast binop or ast binop*)
      
      (*rec call, compile both operands first*)
      let (ll_ty1, ll_o1, ll_stream1) = cmp_exp c e1 in
      let (ll_ty2, ll_o2, ll_stream2) = cmp_exp c e2 in
      let uid = gensym "bop_res" in 

      (*compiling ast binop gives us either an ll binop or an ll icmp instruction
      we need to match on the operand & opcode types to decide
      *)
      let ast_types = typ_of_binop ast_bop in
      let (ll_ret_ty, _, _) = ast_types in
      begin match ast_types with
        | (TInt, TInt, TInt) -> let ll_bop = 
          begin match ast_bop with
            | Add -> (Ll.Add)
            | Sub -> (Ll.Sub)
            | Mul -> (Ll.Mul)
            | IAnd -> (Ll.And)
            | IOr -> (Ll.Or)
            | Shl -> (Ll.Shl)
            | Shr -> (Ll.Lshr)
            | Sar -> (Ll.Ashr)
            | _ -> failwith "ll_ret_ty doesn't match ll opcode"
          end in
          (I64 , Ll.Id(uid), ll_stream1@ll_stream2@[I(uid, Binop(ll_bop , cmp_ty ll_ret_ty, ll_o1, ll_o2))])

        | (TBool, TBool, TBool) -> let ll_bop = 
          begin match ast_bop with
            | And -> (Ll.And)
            | Or -> (Ll.Or)
            | _ -> failwith "ll_ret_ty doesn't match ll opcode"
          end in
          (I1 , Ll.Id(uid),ll_stream1@ll_stream2@[I(uid, Binop(ll_bop , cmp_ty ll_ret_ty, ll_o1, ll_o2))])

        | (TInt, TInt, TBool) -> let ll_cnd = 
          begin match ast_bop with
            | Eq -> (Ll.Eq)
            | Neq -> (Ll.Ne)
            | Lt -> (Ll.Slt)
            | Lte -> (Ll.Sle)
            | Gt -> (Ll.Sgt)
            | Gte -> (Ll.Sge)
            | _ -> failwith "ll_ret_ty doesn't match ll opcode"
          end in
          (I1 , Ll.Id(uid),ll_stream1@ll_stream2@[I(uid, Icmp(ll_cnd , cmp_ty ll_ret_ty, ll_o1, ll_o2))])   
        | _ -> failwith "there are unmatched ast_types cases"
        end

  | Uop(uop, e) ->  
    let (ll_ty, ll_o, ll_stream) = cmp_exp c e in
    let uid = gensym "uop_res" in
      begin match uop with
      | Neg -> (I64, Ll.Id(uid), ll_stream@[I(uid, Binop(Ll.Sub, I64, Const(0L), ll_o))])
      | Bitnot -> (I64, Ll.Id(uid), ll_stream@[I(uid, Binop(Ll.Xor, I64, Const(-1L), ll_o))])
      | Lognot -> (I1, Ll.Id(uid), ll_stream@[I(uid, Binop(Ll.And, I1, Const(0L), ll_o))])
      end

and cmp_exps (c:Ctxt.t) (exps:Ast.exp node list) : ((Ll.ty * Ll.operand) list) * stream =
  begin match exps with
    | h::tl -> 
      let ((rec_ty_op_li), rec_stream_li) = cmp_exps c tl in
      let (new_ret_ty, new_op, new_stream) = cmp_exp c h in
      ([new_ret_ty, new_op]@rec_ty_op_li, new_stream@rec_stream_li)
    | [] -> ([], [])
  end

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  begin match stmt.elt with
    | Ret e -> begin match e with
      | None -> (c, [T(Ll.Ret(rt, None))])
      | Some e -> let (ty, uid, stream) = cmp_exp c e in
        (c, stream@[T(Ll.Ret(rt, Some uid))])
    end

    | Decl (id, e) -> let (decl_ty, result_uid, stream) = cmp_exp c e in
      let store_id = gensym (id^"_var") in
      let new_context = Ctxt.add c id (decl_ty, Ll.Id store_id) in
      (new_context, 
        [E (store_id, Alloca(decl_ty))]@
        stream@
        [I (gensym "sucuk", Store(decl_ty, result_uid, Ll.Id store_id))])

    | If (e, if_block, else_block) -> 
      let (cnd_op_ty, cnd_op_uid, cnd_stream) = cmp_exp c e in
      begin match cnd_op_ty with
      | I1 -> 
        (*then and else blocks are added to ctxt*)
        let (_, then_stream) = cmp_block c rt (if_block) in
        let (_, else_stream) = cmp_block c rt (else_block) in 

        let option_id = gensym "if_compare_res" in
        let then_lbl = gensym "then" in 
        let else_lbl = gensym "else" in 
        let merge_lbl = gensym "merge" in 

        (c, cnd_stream@[I (option_id, Icmp(Eq, cnd_op_ty, cnd_op_uid, Ll.Const(1L)))]@
          [T (Ll.Cbr(Ll.Id (option_id), then_lbl, else_lbl))]@
          (*then block*)
          [L(then_lbl)]@
          then_stream@
          [T (Ll.Br(merge_lbl))]@
          (*else block*)
          [L(else_lbl)]@
          else_stream@
          [T (Ll.Br(merge_lbl))]@
          (*merge*)
          [L(merge_lbl)])
      | _ -> failwith "cnd operand is not Boolean"
    end

    | SCall (e1, arg_list) -> 
    (* lookup function label and type*)
    let (ll_ty, ll_op) = 
      begin match e1.elt with
        | Id(i) -> Ctxt.lookup_function i c
        | _ -> failwith "SCall didn't get an Id"
      end
    in

    (* get function ret value *)
    let (arg_types, ret_type) = 
    begin match ll_ty with
    | Ptr (t) -> 
      begin match t with
        | Fun(arg_types, ret_type) -> arg_types, ret_type
        | _ -> failwith "ptr has not type function"
      end
    | Fun (ts,t)  -> (ts,t)
    | _ -> failwith "function has not type function or ptr"
     end
    in

    let ll_fun_type = Fun(arg_types, ret_type)  in

    let (arg_ty_exp_li, arg_streams) = cmp_exps c arg_list in
    (c, arg_streams@
      [I (gensym "sucuk", Ll.Call(ret_type, ll_op, arg_ty_exp_li))])

    | Assn (e1, e2) -> 

      let (exp_ty, exp_uid, exp_stream) = cmp_exp c e2 in
      begin match e1.elt with
        | Id(store_uid) -> 
          let (ty, ptr_op) = Ctxt.lookup store_uid c in
            (c, exp_stream@
            [I (gensym "sucuk", Store(exp_ty, exp_uid, ptr_op))])
        | Index(arr_exp, ind_exp) -> 
          (*  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr   *)
          let (arr_ty, arr_base_ptr, arr_stream) = cmp_exp c arr_exp in

          (* %_index_ptr14 = getelementptr { i64, [0 x i64] }, 
          { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  *)
          let (_, ind_uid, ind_stream) = cmp_exp c ind_exp in
          let ind_ptr_id = gensym "ind_ptr_id" in
          let gep_stream = [I(ind_ptr_id, Gep(arr_ty, arr_base_ptr, [Const(0L); Const(1L); ind_uid]))] in

          (*  %_index15 = load i64, i64* %_index_ptr14  *)

          let inner_type = 
          begin match arr_ty with
            | Ptr(Struct([I64; Array(n,t)])) -> t 
            | _ -> failwith "wrong inner type"
          end 
          in

          (c, exp_stream@arr_stream@ind_stream@gep_stream@[I (gensym "sucuk", Store(inner_type, exp_uid, Ll.Id(ind_ptr_id)))])
        | _ -> failwith "cannot assign to right hand op"
      end 



    | While (e, body_bl) -> 
      let (cnd_op_ty, cnd_op_uid, cnd_stream) = cmp_exp c e in
      begin match cnd_op_ty with
      | I1 -> 
        let (_, body_stream) = cmp_block c rt (body_bl) in

        let option_id = gensym "sucuk" in
        let pre_lbl = gensym "while_pre" in 
        let body_lbl = gensym "while_body" in 
        let post_lbl = gensym "while_post" in 

        (*concatenating insns together*)
        (c, [T (Ll.Br(pre_lbl))]@
          [L(pre_lbl)]@
          cnd_stream@[I (option_id, Icmp(Eq, cnd_op_ty, cnd_op_uid, Ll.Const(1L)))]@
          [T (Ll.Cbr(Ll.Id (option_id), body_lbl, post_lbl))]@
          (*body block*)
          [L(body_lbl)]@
          body_stream@
          [T (Ll.Br(pre_lbl))]@
          (*post*)
          [L(post_lbl)])
      | _ -> failwith "cnd operand is not Boolean"
    end

    | For (vdecl_list, cnd_exp, inc, body_bl) ->
      (*compile decl list*)
      let rec cmp_vdecls rem_vdecl = 
        let (old_ctxt, rem_vdecl_list) = rem_vdecl in
        begin match rem_vdecl_list with
          | h::tl -> 
            let (act_ctxt, this_decl_stream) = cmp_stmt old_ctxt rt (no_loc (Decl(h))) in
            let (new_ctxt, rem_stream) = cmp_vdecls (act_ctxt, tl) in
            (new_ctxt, this_decl_stream@rem_stream)
          | [] -> (old_ctxt, [])
        end
      in
      let (ctxt, vdecls_stream) = cmp_vdecls (c, vdecl_list) in

      (*compile cnd expression, set true if no expression given*)
      let (cnd_op_ty, cnd_op_uid, cnd_stream) = 
      begin match cnd_exp with
        | Some(e) -> cmp_exp ctxt e
        | None -> let rand_id = gensym "sucuk" in
          (I1, Ll.Id(rand_id),  [I(rand_id, Binop(Add, I1, Const(1L), Const(0L)))])
      end in

      (* compile increment, note: context is not updated*)
      let inc_stream = 
      begin match inc with
        | None -> []
        | Some inc_stmt -> let (inc_ctxt, stream) = cmp_stmt ctxt rt inc_stmt in stream
      end
      in
      begin match cnd_op_ty with
      | I1 -> 
        (*body block is added to ctxt*)
        let (_, body_stream) = cmp_block ctxt rt (body_bl) in

        let option_id = gensym "sucuk" in
        let pre_lbl = gensym "for_pre" in 
        let body_lbl = gensym "for_body" in 
        let post_lbl = gensym "for_post" in 

        (*concatenating insns together*)
        (ctxt, vdecls_stream@
          [T (Ll.Br(pre_lbl))]@
          [L(pre_lbl)]@
          cnd_stream@[I (option_id, Icmp(Eq, cnd_op_ty, cnd_op_uid, Ll.Const(1L)))]@
          [T (Ll.Cbr(Ll.Id (option_id), body_lbl, post_lbl))]@
          (*body block*)
          [L(body_lbl)]@
          body_stream@
          inc_stream@
          [T (Ll.Br(pre_lbl))]@
          (*post*)
          [L(post_lbl)])
    
      | _ -> failwith "cnd operand is not Boolean"
    end
    | _ -> failwith "stmt not implemented"
  end 

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code @ stmt_code
    ) (c,[]) (stmts)



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

let ast_type_of_ast_exp (e:Ast.exp) : Ast.ty =
  match e with
  | CNull rty -> TRef rty
  | CBool bool -> TBool
  | CInt int -> TInt
  | CStr string -> TRef RString
  | CArr(t, el) -> TRef (RArray t)
  | _ -> TInt
    
(* Populate a context with bindings for global variables 
mapping OAT identifiers to LLVMlite gids and their types.

Only a small subset of OAT expressions can be used as global initializers
in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  let rec rec_gctxt (rem_prog:Ast.prog) :Ctxt.t =
    begin match rem_prog with
      | h::tl -> 
        let new_decl = begin match h with
          | Gvdecl n -> [(n.elt.name, (cmp_ty (ast_type_of_ast_exp n.elt.init.elt), Gid n.elt.name))]
          | Gfdecl n -> []
        end
      in new_decl@(rec_gctxt tl)
      | [] -> []
    end
  in

  (rec_gctxt p)@c 



(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  
  (* creates a list of Ll.ty form Ast.ty arguments *)
  let rec create_arg_types rem_args = 
    begin match rem_args with
    | h::tl -> 
      let (arg_type, arg_name) = h in
      [(cmp_ty arg_type)]@(create_arg_types tl)
      | [] -> []
    end
  in
  
  let arg_types = ((create_arg_types f.elt.args), (cmp_ret_ty f.elt.frtyp)) in
  
  (* fill Oat arg variable names into a list to use them as uids later *)
  let rec create_arg_uids rem_args = 
    begin match rem_args with
    | h::tl -> 
      let (arg_type, arg_name) = h in
      [(arg_name)]@(create_arg_uids tl)
      | [] -> []
    end
  in
  
  let arg_uids = create_arg_uids f.elt.args in
  
  
  (* fills the context with newly generated uid and arg variable name tuple e.g. (%arg_1, a) *)
  let rec add_args_to_ctxt c rem_args = 
    match rem_args with
    | [] -> c
    | h::tl -> 
      let (arg_type, arg_name) = h in
      let ptr = gensym f.elt.fname in
      let new_ctxt = Ctxt.add c arg_name (cmp_ty arg_type, Ll.Id(ptr)) in
      add_args_to_ctxt new_ctxt tl
  in
  let ctxt_with_args = add_args_to_ctxt c f.elt.args in
    

  
  (* generates a stream, that returns the instructions to copy the args to the stack.
  The pointers to the args have already been assigned in the context *)
  
  let rec arg_loop rem_args = 
    
    begin match rem_args with
    | [] -> []
    | h::tl -> 
      let (ast_ty, ast_id) = h in
      let (ll_ty,ptr_to_arg) = Ctxt.lookup ast_id ctxt_with_args in (* Pointer to arg variable *)
      let uid_of_arg = 
        match ptr_to_arg with
        | Ll.Id(uid) -> uid
        | _ -> failwith "Arg operand was no uid"
      in
      let stream_of_this_args = [
        I(uid_of_arg, Alloca(ll_ty));
        I(gensym f.elt.fname, Store(ll_ty, Ll.Id(ast_id), ptr_to_arg ))
        ] in
        let stream_of_other_args = arg_loop tl in
        stream_of_this_args@stream_of_other_args
      end
    in
  
  let args_stream = arg_loop f.elt.args in

  let (some_ctxt, body_stream) = cmp_block ctxt_with_args (cmp_ret_ty f.elt.frtyp) (f.elt.body) in

  let (body,globals) = cfg_of_stream ( List.rev (args_stream@body_stream)) in

  ({f_ty = arg_types; f_param = arg_uids; f_cfg = body},globals)

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp (c:Ctxt.t) (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =

  let main_ty =
    match e.elt with
    | CStr(s) -> Array((String.length s) +1, I8)
    | element -> cmp_ty (ast_type_of_ast_exp element)
    
  in

  let (main_ginit, ginit_list) = 
    match e.elt with
    | CNull(n) -> GNull, []
    | CBool(b) -> if b then GInt(1L), [] else GInt(0L), []
    | CInt(i) -> GInt(i), []
    | CStr(s) -> GString(s), []
    | CArr(t,es) ->  
      let rec cmp_gexps rem_gexp =
        begin match rem_gexp with
          | h::tl -> 
            let (elem_gdecls, cmped_elems) = cmp_gexp c h in
            let (rem_gdecls, rem_elems) = cmp_gexps tl in
              (rem_gdecls (*??*),cmped_elems@rem_elems)
          | [] -> ([] ,[])
        end
      in 
      let this_ginit_list = cmp_gexps es in
      (GArray(t, es), )
    | _ ->  failwith "tried to initalize global variable with a non constant expression"
  in  

  let main_gdecl =
    (main_ty, main_ginit)
  in

  (main_gdecl, ginit_list)

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
