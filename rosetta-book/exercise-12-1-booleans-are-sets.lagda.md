# Exercise 12.1

```agda
module exercise-12-1-booleans-are-sets where

open import universe-levels
open import exercise-4-2-boolean-operations
open import section-4-6-dependent-pair-types
open import exercise-6-2-observational-equality-booleans
open import section-12-1-propositions
open import section-12-3-sets
```

## Problem statement

Show that `bool` is a set by applying Theorem 12.3.4 with the observational equality on `bool` defined in Exercise 6.2.

## Solution

```agda
abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = is-prop-unit
  is-prop-Eq-bool true false = is-prop-empty
  is-prop-Eq-bool false true = is-prop-empty
  is-prop-Eq-bool false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool =
    is-set-prop-in-id
      ( Eq-bool)
      ( is-prop-Eq-bool)
      ( refl-Eq-bool)
      ( λ x y → eq-Eq-bool)

bool-Set : Set lzero
bool-Set = bool , is-set-bool
```
