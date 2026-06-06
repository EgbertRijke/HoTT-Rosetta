# Exercise 6.4 Strict order on the natural numbers

```agda
module exercise-6-4-strict-order-natural-numbers where
```

## Problem statement

The strict ordering relation `<` on `ℕ` is defined recursively by

```text
  (0 < 0)       := ∅      (0 < n + 1)       := 𝟙
  (m + 1 < 0)   := ∅      (m + 1 < n + 1)   := (m < n).
```

Show that the strict ordering relation is antireflexive, antisymmetric, and
transitive.

## Solution

## Problem statement

Show that `n < n + 1` and

```text
  (m < n) → (m < n + 1)
```

for any `m, n : ℕ`.

## Solution

## Problem statement

Show that

```text
  (m < n) ↔ (m + 1 ≤ n)
  (m < n) ↔ (n ≰ m)
```

for any `m, n : ℕ`.

## Solution
