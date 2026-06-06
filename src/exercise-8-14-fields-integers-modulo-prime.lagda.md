# Exercise 8.14 Fields of integers modulo primes

```agda
module exercise-8-14-fields-integers-modulo-prime where
```

## Problem statement

Show that for each prime `p`, the ring `ℤ/p` of integers modulo `p` is a field,
i.e., construct a multiplicative inverse

```text
  (_)^-1 : Π(x : ℤ/p) → (x ≠ 0) → ℤ/p
```

equipped with identifications

```text
  x^-1 x = 1
  x x^-1 = 1.
```

## Solution
