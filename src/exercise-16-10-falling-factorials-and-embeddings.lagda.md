# Exercise 16.10 Falling factorials and embeddings

```agda
module exercise-16-10-falling-factorials-and-embeddings where
```

## Problem statement

For any two types `A` and `B`, construct an equivalence

```text
  ((A + unit) ↪ᵈ (B + unit)) ≃ (unit ↪ᵈ (B + unit)) × (A ↪ᵈ B).
```

## Solution

## Problem statement

Construct an equivalence `Fin((n)_m) ≃ (Fin(m) ↪ Fin(n))`, where `(n)_m` is the
**m-th falling factorial** of `n`, which is defined recursively by

```text
  (0)_0         := 1
  (0)_{m + 1}   := 0
  (n + 1)_0     := 1
  (n + 1)_{m+1} := (n + 1)(n)_m.
```

Conclude that if `A` and `B` are finite with cardinality `m` and `n`, then the
type `A ↪ B` is finite with cardinality `(n)_m`.

## Solution
