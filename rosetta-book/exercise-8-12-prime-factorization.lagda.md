# Exercise 8.12

```agda
module exercise-8-12-prime-factorization where

```

## Problem statement

### Exercise 8.12(a)

Show that every natural number `n ≥ 2` has a prime factor.

### Exercise 8.12(b)

Define a function
```text
prime-factors : (Σ(n : ℕ) 2 ≤ n) → list(ℕ)
```
such that `prime-factors(n)` is an increasing list of primes, and `n` is the product of the primes in the list `prime-factors(n)`.

### Exercise 8.12(c)

Show that any increasing list `l` of primes of which the product is `n` is equal to the list `prime-factors(n)`.

## Solution

BENCHMARK PROBLEM
