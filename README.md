# Calculating compilers for register machines

This repository contains a Coq formalisation of compiler calculations
for register machines along with the full Haskell source code of the
calculated compilers.

## Coq formalisation

The Coq formalisation is located in the [coq](coq) subfolder. Below we
list the relevant Coq files for the calculations:

 - [Arith.v](coq/Arith.v): arithmetic expressions 
 - [Exception.v](coq/Exception.v): arithmetic expressions + exceptions
 - [State.v](coq/State.v): global state
 - [LocalState.v](coq/LocalState.v): local state
 - [LambdaBad.v](coq/LambdaBad.v): call-by-value lambda calculus without a
   stack which yields an unsatisfactory compiler and machine
 - [Lambda.v](coq/Lambda.v): call-by-value lambda calculus with
   a stack which yields a much more realistic compiler and machine
 - [LambdaTruncate.v](coq/LambdaTruncate.v): variant of
   [Lambda.v](coq/Lambda.v) is more realistic as it only copies
   a bounded set of registers to the stack (via truncation)
 - [LambdaException.v](coq/LambdaException.v): lambda calculus +
   exceptions, based on [LambdaTruncate.v](coq/LambdaTruncate.v)

The remaining files are used to define the Coq tactics to support
reasoning in calculation style and to provide auxiliary concepts:

 - [Tactics.v](coq/Tactics.v): tactics for calculation style proofs
 - [Machine.v](coq/Machine.v): auxiliary definitions and tactics for
    virtual machines 
 - [Memory.v](coq/Memory.v): the (axiomatic) memory model
 - [LinearMemory.v](coq/LinearMemory.v): instantiation of the memory
   model (thus proving its consistency)
 - [ListIndex.v](coq/ListIndex.v): definitions to index elements in a list

## Haskell code

The [haskell](haskell) subfolder contains the source code of the three
compilers calculated in the paper:

 - [arith.lhs](haskell/arith.lhs): arithmetic expressions
 - [except.lhs](haskell/except.lhs): arithmetic expressions + exceptions
 - [lambda.lhs](haskell/lambda.lhs): lambda calculus
