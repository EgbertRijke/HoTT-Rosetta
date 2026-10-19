# Exercise 7.1

```agda
module exercise-7-1-divisibility-three-for-two where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-1-the-curry-howard-interpretation
```

## Problem statement

Complete the proof of Proposition 7.1.5.

## Solution

```agda
open import section-7-1-the-curry-howard-interpretation using
  (div-left-summand-ℕ; div-right-summand-ℕ)
```
