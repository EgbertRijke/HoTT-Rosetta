# Exercise 12.8

```agda
module exercise-12-8-retracts-of-truncated-types where

```

## Problem statement

### Exercise 12.8(a)

Consider a section-retraction pair

```text
      i        r
  A -----> B -----> A
```

with `H : r ∘ i ~ id`.
Show that `x = y` is a retract of `i(x) = i(y)`.

### Exercise 12.8(b)

Use Exercise 10.2 to show that if `A` is a retract of a `k`-type `B`, then `A` is also a `k`-type.

## Solutions

### Exercise 12.8(a)

```agda
open import section-12-4-general-truncation-levels using
  ( is-injective-retraction; retract-eq)
```

### Exercise 12.8(b)

```agda
open import section-12-4-general-truncation-levels using
  ( is-trunc-retract-of)
```
