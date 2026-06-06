# Exercise 8.3 Finite choice for decidable families

```agda
module exercise-8-3-finite-choice-decidable where
```

## Problem statement

For any family `P` of decidable types indexed by `Fin(k)`, construct a function

```text
  ¬ (Π(x : Fin(k)) P(x)) → Σ(x : Fin(k)) ¬ P(x).
```

## Solution
