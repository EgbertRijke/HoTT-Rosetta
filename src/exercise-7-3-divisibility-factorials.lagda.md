# Exercise 7.3 Divisibility of factorials

```agda
module exercise-7-3-divisibility-factorials where
```

## Problem statement

Construct a dependent function

```text
  Π(x : ℕ) (x ≠ 0) → ((x ≤ n) → (x | n!))
```

for every `n : ℕ`.

## Solution
