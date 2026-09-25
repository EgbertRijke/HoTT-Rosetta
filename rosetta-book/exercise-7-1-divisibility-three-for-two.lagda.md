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
div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (x +ℕ y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (x +ℕ_) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) =
  is-injective-right-add-ℕ (m *ℕ (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( m *ℕ (succ-ℕ d))
            ( (dist-ℕ m n) *ℕ (succ-ℕ d))))) ∙
      ( ( ap
          ( _*ℕ (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( reflects-leq-mul-ℕ d m n
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (x +ℕ_) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (x +ℕ y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1
    ( concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```
