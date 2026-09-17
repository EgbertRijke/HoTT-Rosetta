# Exercise 22.11

```agda
module exercise-22-11-exercise where

```

## Problem statement

Consider the type `C` of families `A:S^1→Set` of sets over the circle equipped with a point `a_0:A(base)`, such that the total space
```text
Σ(t:S^1) A(t)
```
is connected.

For any type family `A` over the circle equipped with `a_0:A(base)`, show that the total space `Σ(t:S^1) A(t)` is connected if and only if `tr_A(loop):A(base)→ A(base)` has a single orbit in the sense that the map `k↦ tr_A(loop)^k(a_0):ℤ→ A(base)` is surjective.

Let `(A,a_0)` and `(B,b_0)` be in `C`.
Show that the type
```text
((A,a_0)≤ (B,b_0))≔ Σ(f:Π(t:S^1) A(t)→ B(t)) f(base,a_0)=b_0
```
is a proposition.
Furthermore, show that this inequality relation gives `C` the structure of a poset.

Show that the poset `C` is isomorphic to the poset of subgroups of `ℤ`.

## Solution

No formalization has been curated yet.
