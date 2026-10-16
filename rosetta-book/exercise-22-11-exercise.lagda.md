# Exercise 22.11

```agda
module exercise-22-11-exercise where

```

## Problem statement

Consider the type `C` of families `A : S¹ → Set` of sets over the circle equipped with a point `a₀ : A(base)`, such that the total space
```text
Σ(t : S¹) A(t)
```
is connected.

For any type family `A` over the circle equipped with `a₀ : A(base)`, show that the total space `Σ(t : S¹) A(t)` is connected if and only if `tr_A(loop) : A(base) → A(base)` has a single orbit in the sense that the map `k ↦ tr_A(loop)^k(a₀) : ℤ → A(base)` is surjective.

Let `(A,a₀)` and `(B,b₀)` be in `C`.
Show that the type
```text
((A,a₀) ≤ (B,b₀)) ≔ Σ(f : Π(t : S¹) A(t) → B(t)) f(base,a₀) = b₀
```
is a proposition.
Furthermore, show that this inequality relation gives `C` the structure of a poset.

Show that the poset `C` is isomorphic to the poset of subgroups of `ℤ`.

## Solution

BENCHMARK PROBLEM
