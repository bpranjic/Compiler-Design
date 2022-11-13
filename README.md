# Compiler Design
This repository contains our solution for the project in the course Compiler Design at ETH Zurich
## HW1: Hellocaml
This assignment provides an introduction to OCaml programming and some warm-up exercises involving tree manipulation and recursive programming.

## HW2: X86lite
In this assignment we implemented an assembler and simulator for a small idealized subset of the X86-64 platform that serves as the target language for the compilers we build in the later assignments.

## HW3: Compiling LLVMlite
In this assignment we implemented a non-optimizing compiler for a subset of the LLVM IR language. The source language consists of a 64-bit, simplified subset of the LLVM IR that we call LLVMlite. The target language is X86lite as defined in HW2.

## HW4: Oat v.1 Compiler
In this assignment we implemented a compiler frontend for a simple imperative language that has boolean, int, string, and array types as well as top-level, mutually-recursive functions and global variables.

## HW5: Oat v.2 Compiler
In this assignment we upgraded our compiler from HW4. We implemented a compiler typechecker for an extended version of Oat that has boolean, int, string, array, struct and function pointer types as well as "possibly null" and "definitely not null" references.

## HW6: Dataflow Analysis and Optimizations
In this assignment we implemented several simple dataflow analyses and some optimizations at the level of our LLVMlite intermediate representation in order to improve code size and speed
