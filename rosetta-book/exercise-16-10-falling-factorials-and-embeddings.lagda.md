# Exercise 16.10

```agda
module exercise-16-10-falling-factorials-and-embeddings where

```

## Problem statement

### Exercise 16.10(a)

For any two types `A` and `B`, construct an equivalence

```text
  ((A + unit) ↪ᵈ (B + unit)) ≃ (unit ↪ᵈ (B + unit)) × (A ↪ᵈ B).
```

### Exercise 16.10(b)

Construct an equivalence `Fin{nₘ} ≃ (Fin{m} ↪ Fin{n})`, where `nₘ` is the **`m`-th falling factorial** of `n`, which is defined recursively by

```text
           0₀ ≔ 1
        0ₘ₊₁ ≔ 0
     (n + 1)₀ ≔ 1
  (n + 1)ₘ₊₁ ≔ (n+1)nₘ.
```

Conclude that if `A` and `B` are finite with cardinality `m` and `n`, then the type `A ↪ B` is finite with cardinality `nₘ`.

## Solution

BENCHMARK PROBLEM
