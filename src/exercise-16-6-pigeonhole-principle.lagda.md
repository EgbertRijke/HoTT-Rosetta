# Exercise 16.6 Pigeonhole principle

```agda
module exercise-16-6-pigeonhole-principle where
```

## Problem statement

Consider two finite types `X` and `Y` with `m` and `n` elements, respectively,
and let `f : X → Y` be a map.
Show that

```text
  is-inj(f) → (m ≤ n).
```

## Solution

## Problem statement

Prove the **pigeonhole principle**, i.e., show that

```text
  (n > m) → ∃(x x' : X), (x ≠ x') × (f(x) = f(x')).
```

## Solution

## Problem statement

Show that there is no embedding `ℕ ↪ Fin(k)`, for any `k : ℕ`.

## Solution
