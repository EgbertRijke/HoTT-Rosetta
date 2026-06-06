# Exercise 9.9 Finitely cyclic maps

```agda
module exercise-9-9-finitely-cyclic-maps where
```

## Problem statement

A map `f : X → X` is said to be **finitely cyclic** if it comes equipped with an
element of type

```text
  is-finitely-cyclic(f) := Π(x y : X) Σ(k : ℕ) f^k(x) = y.
```

Show that any finitely cyclic map is an equivalence.

## Solution

## Problem statement

Show that `succ-Fin : Fin(k) → Fin(k)` is finitely cyclic for any `k : ℕ`.

## Solution
