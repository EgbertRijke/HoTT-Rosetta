# Exercise 8.10

```agda
module exercise-8-10-maximal-elements where

```

## Problem statement

Consider a decidable type family `P` over `ℕ` equipped with an upper bound `m`.

### Exercise 8.10(a)

Show that the type `Σ(n : ℕ) P(n)` is decidable.

### Exercise 8.10(b)

Construct a function
```text
(Σ(n : ℕ) P(n)) → (Σ(n : ℕ) P(n) × is-upper-bound_P(n)).
```

### Exercise 8.10(c)

Use the function of part (b) to give a second construction of the greatest common divisor, and verify that it satisfies the specification of Definition 8.4.1.

## Solution

BENCHMARK PROBLEM
