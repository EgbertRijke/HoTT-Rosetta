# Exercise 16.6

```agda
module exercise-16-6-pigeonhole-principle where

```

## Problem statement

Consider two finite types `X` and `Y` with `m` and `n` elements, respectively, and let `f : X → Y` be a map.

### Exercise 16.6(a)

Show that

```text
  is-inj(f) → (m ≤ n).
```

### Exercise 16.6(b)

Prove the **pigeonhole principle**, i.e., show that

```text
  (n > m) → ∃_{(x, x' : X)} (x ≠ x') × (f(x) = f(x')).
```

### Exercise 16.6(c)

Show that there is no embedding `ℕ ↪ Fin_{k}`, for any `k : ℕ`.

## Solution
