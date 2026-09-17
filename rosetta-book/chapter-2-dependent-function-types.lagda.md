# Chapter 2 Dependent function types

```agda
module chapter-2-dependent-function-types where

open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import exercise-2-1-judgmental-extensionality
open import exercise-2-2-right-unit-law
open import exercise-2-3-constant-maps
open import exercise-2-4-swapping-variables
```

A fundamental concept of dependent type theory is that of a dependent function.
A dependent function is a function of which the type of the output may depend on the input.
For example, when we concatenate a vector of length `m` with a vector of length `n`, we obtain a vector of length `m + n`.
Dependent functions are a generalization of ordinary functions, because an ordinary function `f : A → B` is a function of which the output `f(x)` has type `B` regardless of the value of `x`.
