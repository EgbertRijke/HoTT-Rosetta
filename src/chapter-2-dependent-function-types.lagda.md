# Chapter 2 Dependent function types

A fundamental concept of dependent type theory is that of a dependent function. A dependent function is a function of which the type of the output may depend on the input. For example, when we concatenate a vector of length `m` with a vector of length `n`, we obtain a vector of length `m + n`. Dependent functions are a generalization of ordinary functions, because an ordinary function `f : A → B` is a function of which the output `f(x)` has type `B` regardless of the value of `x`.
