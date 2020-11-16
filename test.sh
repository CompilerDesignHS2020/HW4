#!/bin/sh

clang -c runtime.c -o runtime.o

./main.native $1 runtime.o

rm runtime.o