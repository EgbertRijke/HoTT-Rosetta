# Exercise 19.4

```agda
module exercise-19-4-exercise where

```

## Problem statement

Let `X` be a set.
Show that the map from `(X = X)` to `(X ≃ X)` sending `p` to `equiv-eq(inv p)` is a group isomorphism.

## Solution

```agda
open import section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics
  using (iso-symmetric-group-loop-group-Set)
```
