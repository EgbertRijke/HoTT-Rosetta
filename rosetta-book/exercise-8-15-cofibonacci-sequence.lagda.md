# Exercise 8.15

```agda
module exercise-8-15-cofibonacci-sequence where

```

## Problem statement

Let `F : ℕ → ℕ` be the Fibonacci sequence.
Construct the **cofibonacci sequence**, i.e., the function `G : ℕ → ℕ` such that
```text
(Gₘ | n) ↔ (m | Fₙ)
```
for all `m,n : ℕ`.
Hint: for `m > 0`, `Gₘ` is the least `x > 0` such that `m | Fₓ`.

## Solution

BENCHMARK PROBLEM
