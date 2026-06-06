# Exercise 8.15 Cofibonacci sequence

```agda
module exercise-8-15-cofibonacci-sequence where
```

## Problem statement

Let `F : ℕ → ℕ` be the Fibonacci sequence.
Construct the **cofibonacci sequence**, i.e., the function `G : ℕ → ℕ` such that

```text
  (G_m | n) ↔ (m | F_n)
```

for all `m, n : ℕ`.
Hint: for `m > 0`, `G_m` is the least `x > 0` such that `m | F_x`.

## Solution
