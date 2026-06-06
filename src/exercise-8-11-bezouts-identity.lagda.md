# Exercise 8.11 Bezout's identity

```agda
module exercise-8-11-bezouts-identity where
```

## Problem statement

For any three natural numbers `x`, `y`, and `z`, show that the type

```text
  Σ(k : ℕ) Σ(l : ℕ) dist-ℕ(kx, ly) = z
```

is decidable.

## Solution

## Problem statement

For any two natural numbers `x` and `y`, construct two natural numbers `k` and
`l` equipped with an identification

```text
  dist-ℕ(kx, ly) = gcd(x, y).
```

This is Bézout's identity.

## Solution
