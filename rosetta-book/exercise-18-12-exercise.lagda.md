# Exercise 18.12

```agda
module exercise-18-12-exercise where

```

## Problem statement

Show that every finite inhabited type is uniquely a product of finitely many finite types of prime cardinality, in the sense that the type

```text
  Σ(X : 𝔽) Σ(Y : X → Σ(p : prime) BSₚ) ‖A ≃ Π(x : X) Y(x)‖
```

is connected for every finite inhabited type `A`.

## Solution

BENCHMARK PROBLEM
