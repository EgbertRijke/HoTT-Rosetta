# Exercise 12.8

```agda
module exercise-12-8-retracts-of-truncated-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
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
