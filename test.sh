#!/bin/sh

clang -c runtime.c -o runtime.o

./main.native --execute-x86 $1 runtime.o

rm runtime.o