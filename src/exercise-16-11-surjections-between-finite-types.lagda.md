# Exercise 16.11 Surjections between finite types

```agda
module exercise-16-11-surjections-between-finite-types where
```

## Problem statement

Consider an arbitrary type `A` and a type `B` with decidable equality.
Construct an equivalence

```text
  ((A + unit) ↠ (B + unit)) ≃
  (B + unit) × (A ↠ B) + (A ↠ B + unit).
```

## Solution

## Problem statement

Construct an equivalence `Fin(S(m, n)) ≃ (Fin(m) ↠ Fin(n))`, where
`S(m, n)` is defined recursively by

```text
  S(0, 0)             := 1
  S(0, n + 1)         := 0
  S(m + 1, 0)         := 0
  S(m + 1, n + 1)     := (n + 1) S(m, n) + S(m, n + 1).
```

Conclude that if `A` and `B` are finite with cardinality `m` and `n`, then the
type `A ↠ B` is finite with cardinality `S(m, n)`.
Note: the number `S(m, n)` is `n! Stirling(m, n)`, where `Stirling(m, n)` is
the **Stirling number of the second kind** at `(m, n)`.

## Solution
