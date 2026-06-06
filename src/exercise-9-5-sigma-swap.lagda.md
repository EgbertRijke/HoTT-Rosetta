# Exercise 9.5 Sigma swap

```agda
module exercise-9-5-sigma-swap where
```

## Problem statement

Let `A` and `B` be types, and let `C` be a family over `x : A, y : B`.
Construct an equivalence

```text
  (Σ(x : A) Σ(y : B) C(x, y)) ≃
  (Σ(y : B) Σ(x : A) C(x, y)).
```

## Solution

## Problem statement

Let `A` be a type, and let `B` and `C` be type families over `A`.
Construct an equivalence

```text
  (Σ(u : Σ(x : A) B(x)) C(pr1(u))) ≃
  (Σ(v : Σ(x : A) C(x)) B(pr1(v))).
```

## Solution
