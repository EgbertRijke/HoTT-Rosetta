# Exercise 22.3

```agda
module exercise-22-3-exercise where

```

## Problem statement

The **(twisted) double cover** of the circle is defined as the type family `T ≔ D(bool,neg-bool) : S¹ → 𝒰`, where `neg-bool : bool ≃ bool` is the negation equivalence of Example 9.2.4.

Show that `¬(Π(t : S¹) T(t))`.

Construct an equivalence `e : S¹ ≃ Σ(t : S¹) T(t)` for which the triangle

```text
  [S¹] -------e-----> [Σ(t : S¹) T(t)]
      \                 /
deg(2)  \             / pr1
          V         V
             [S¹]
```
commutes.

## Solution

BENCHMARK PROBLEM
