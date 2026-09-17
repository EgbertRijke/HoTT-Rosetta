# Exercise 17.14

```agda
module exercise-17-14-binomial-theorem where

```

## Problem statement

For any `(X,i):binom(A, B)`, we define `A\setminus(X,i)≔ (A\setminus X,A\setminus i):binom(A, B)`, where
```text
A\setminus X ≔ Σ(a:A) ¬(fib(i, a))
A\setminus i ≔ pr 1.
```
Now consider a finite type `X` and two arbitrary types `A` and `B`.
Construct an equivalence
```text
(A+B)^X≃Σ(k:ℕ) Σ((Y,i):\dbinomtype{X}{Fin{k}}) A^Y× B^{X\setminus Y}.
```

## Solution

No formalization has been curated yet.
