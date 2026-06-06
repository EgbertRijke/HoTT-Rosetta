# Exercise 13.18 Retracts as limits

```agda
module exercise-13-18-retracts-as-limits where
```

## Problem statement

Consider a section-retraction pair

```text
       i       r
  A ------> X -----> A
```

with `H : r ∘ i ~ id` and define `f := i ∘ r`.
Construct an equivalence

```text
  A ≃ Σ(x : ℕ → X) Π(n : ℕ) f(x_{n+1}) = x_n.
```

## Solution
