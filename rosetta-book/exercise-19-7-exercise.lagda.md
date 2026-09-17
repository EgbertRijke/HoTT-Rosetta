# Exercise 19.7

```agda
module exercise-19-7-exercise where

```

## Problem statement

Consider an abelian group `A`, and let `D_A≔ A+A` be the set equipped with `1≔inl(0)`, the binary operation `{_}·{_}:D_A→ (D_A→ D_A)` defined by
```text
inl(x)·inl(y) ≔ inl(x+y)
inl(x)·inr(y) ≔ inr(-x+y)
inr(x)·inl(y) ≔ inr(x+y)
inr(x)·inr(y) ≔ inl(-x+y),
```
and the unary operation `(_)^{-1}:D_A→ D_A` defined by
```text
inl(x)^{-1} ≔ inl(-x)
inr(x)^{-1} ≔ inr(x).
```
Show that `D_A` equipped with these operations is a group.
The group `D_A` is called the **generalized dihedral group** on `A`.
The (ordinary) **dihedral group** `D_k` is defined to be `D_k≔ D_{ℤ/k}`.

## Solution

No formalization has been curated yet.
