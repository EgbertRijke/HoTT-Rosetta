# Exercise 8.5 Characterization of prime numbers

```agda
module exercise-8-5-characterization-prime where
```

## Problem statement

For any natural number `n`, show that

```text
  is-prime(n) ↔
  (2 ≤ n) × Π(x : ℕ) (x | n) → (x = 1) + (x = n).
```

## Solution
