# Exercise 6.5 Distance on the natural numbers

```agda
module exercise-6-5-distance-natural-numbers where
```

## Problem statement

The **distance function**

```text
  dist-ℕ : ℕ → (ℕ → ℕ)
```

is defined recursively by

```text
  dist-ℕ(0, 0)       := 0       dist-ℕ(0, n + 1)       := n + 1
  dist-ℕ(m + 1, 0)   := m + 1   dist-ℕ(m + 1, n + 1)   := dist-ℕ(m, n).
```

In other words, the distance between two natural numbers is the *symmetric
difference* between them.
Show that `dist-ℕ` satisfies the axioms of a metric:

1. `(m = n) ↔ (dist-ℕ(m, n) = 0)`.
2. `dist-ℕ(m, n) = dist-ℕ(n, m)`.
3. `dist-ℕ(m, n) ≤ dist-ℕ(m, k) + dist-ℕ(k, n)`.

## Solution

## Problem statement

Show that `dist-ℕ(m, n) = dist-ℕ(m, k) + dist-ℕ(k, n)` if and only if either
both `m ≤ k` and `k ≤ n` hold or both `n ≤ k` and `k ≤ m` hold.

## Solution

## Problem statement

Show that `dist-ℕ` is translation invariant and linear:

```text
  dist-ℕ(a + m, a + n)   = dist-ℕ(m, n)
  dist-ℕ(k · m, k · n)   = k · dist-ℕ(m, n).
```

## Solution

## Problem statement

Show that `x + dist-ℕ(x, y) = y` for any `x ≤ y`.

## Solution
