# Exercise 17.14 Binomial theorem

```agda
module exercise-17-14-binomial-theorem where
```

## Problem statement

For any `(X, i) : binom(A, B)`, we define
`A \ (X, i) := (A \ X, A \ i) : binom(A, B)`, where

```text
  A \ X := Σ(a : A) ¬ fib(i, a)
  A \ i := pr1.
```

Now consider a finite type `X` and two arbitrary types `A` and `B`.
Construct an equivalence

```text
  (A + B)^X ≃
  Σ(k : ℕ) Σ((Y, i) : binom(X, Fin(k))) A^Y × B^{X \ Y}.
```

## Solution
