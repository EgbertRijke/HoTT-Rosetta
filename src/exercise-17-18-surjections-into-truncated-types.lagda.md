# Exercise 17.18 Surjections into truncated types

```agda
module exercise-17-18-surjections-into-truncated-types where
```

## Problem statement

For any type `A` and any `k ≥ -1`, show that the type

```text
  Σ(X : Type^{≤ k}) A ↠ X
```

of `k`-truncated types `X` equipped with a surjective map `A ↠ X` is
`k`-truncated, even though the type `Type^{≤ k}` itself is `(k + 1)`-truncated.

## Solution
