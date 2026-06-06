# Exercise 8.10 Maximal elements

```agda
module exercise-8-10-maximal-elements where
```

## Problem statement

Consider a decidable type family `P` over `ℕ` equipped with an upper bound `m`.
Show that the type `Σ(n : ℕ) P(n)` is decidable.

## Solution

## Problem statement

Construct a function

```text
  (Σ(n : ℕ) P(n)) →
  (Σ(n : ℕ) P(n) × is-upper-bound_P(n)).
```

## Solution

## Problem statement

Use the function of the previous part to give a second construction of the
greatest common divisor, and verify that it satisfies the specification of
Definition 8.4.1.

## Solution
