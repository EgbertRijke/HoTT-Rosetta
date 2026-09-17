# Exercise 18.14

```agda
module exercise-18-14-exercise where

```

## Problem statement

In this exercise we extend the definition of the binomial types to `‖𝒰‖_0` as follows: For a type `X:𝒰` and `k:‖𝒰‖_0`, we define
```text
binom(X, k)≔ Σ(Y:fib(η, k)) Y↪ᵈ X.
```
Furthermore, for `(Y,i):binom(X, k)`, define
```text
X\setminus Y ≔ Σ(x:X) ¬(fib(i, x)).
\complement{i} ≔ pr 1.
```
Now consider a type `X` and two type families `A` and `B` over `X`, and let `𝒰` be a universe containing `X`, `A`, and `B`.
Show that the type `Π(x:X) A(x)+B(x)` is equivalent to the type
```text
Σ(k:‖𝒰‖_0) Σ((Y,i):binom(X, k)) (Π(y:Y) A(i(y)))×(Π(y:X\setminus Y) B(\complement{i}(y))).
```

## Solution

No formalization has been curated yet.
