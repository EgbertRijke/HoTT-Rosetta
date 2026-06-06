# Exercise 12.13 Fiber inclusions truncated

```agda
module exercise-12-13-fiber-inclusions-truncated where
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is `(k + 1)`-truncated.
2. For any type family `B` over `A` and any `a : A`, the **fiber inclusion**

```text
  i_a : B(a) → Σ(x : A) B(x)
```

given by `y ↦ (a, y)` is a `k`-truncated map.

In particular, if `A` is a set then any fiber inclusion
`i_a : B(a) → Σ(x : A) B(x)` is an embedding.

## Solution
