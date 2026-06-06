# Exercise 12.12 Total maps truncated

```agda
module exercise-12-12-total-maps-truncated where
```

## Problem statement

Let `f : Π(x : A) B(x) → C(x)` be a family of maps.
Show that the following are equivalent:

1. For each `x : A` the map `f(x)` is `k`-truncated.
2. The induced map

```text
  tot(f) : (Σ(x : A) B(x)) → (Σ(x : A) C(x))
```

is `k`-truncated.

## Solution
