# Exercise 6.3 Order on the natural numbers

```agda
module exercise-6-3-order-natural-numbers where
```

## Problem statement

The ordering relation `≤` on `ℕ` is defined recursively by

```text
  (0 ≤ 0)       := 𝟙      (0 ≤ n + 1)       := 𝟙
  (m + 1 ≤ 0)   := ∅      (m + 1 ≤ n + 1)   := (m ≤ n).
```

Show that `≤` satisfies the axioms of a *poset*, i.e., show that `≤` is
reflexive, antisymmetric, and transitive.

## Solution

## Problem statement

Show that

```text
  (m ≤ n) + (n ≤ m)
```

for any `m, n : ℕ`.

## Solution

## Problem statement

Show that

```text
  (m ≤ n) ↔ (m + k ≤ n + k)
```

holds for any `m, n, k : ℕ`.

## Solution

## Problem statement

Show that

```text
  (m ≤ n) ↔ (m · (k + 1) ≤ n · (k + 1))
```

holds for any `m, n, k : ℕ`.

## Solution

## Problem statement

Show that `k ≤ min(m, n)` holds if and only if both `k ≤ m` and `k ≤ n` hold,
and show that `max(m, n) ≤ k` holds if and only if both `m ≤ k` and `n ≤ k`
hold.

## Solution
