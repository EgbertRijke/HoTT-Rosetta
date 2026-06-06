# Exercise 10.6 Dependent pair types with contractible base

```agda
module exercise-10-6-dependent-pair-contractible-base where
```

## Problem statement

Let `A` be a contractible type with center of contraction `a : A`.
Furthermore, let `B` be a type family over `A`.
Show that the map

```text
  y ↦ (a, y) : B(a) → Σ(x : A) B(x)
```

is an equivalence.

## Solution
