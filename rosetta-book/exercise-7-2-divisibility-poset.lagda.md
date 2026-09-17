# Exercise 7.2

```agda
module exercise-7-2-divisibility-poset where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-1-injectivity-addition-multiplication
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
```

## Problem statement

Show that the divisibility relation satisfies the axioms of a poset, i.e., that it is reflexive, antisymmetric, and transitive.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-antisymmetric : UU (l1 ⊔ l2)
  is-antisymmetric = (x y : A) → R x y → R y x → x ＝ y
```

```agda
abstract
  is-one-is-left-unit-mul-ℕ :
    (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ succ-ℕ y → is-one-ℕ x
  is-one-is-left-unit-mul-ℕ x y p =
    is-injective-right-mul-succ-ℕ y (p ∙ inv (left-unit-law-mul-ℕ (succ-ℕ y)))
```

```agda
refl-div-ℕ : is-reflexive div-ℕ
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

abstract
  antisymmetric-div-ℕ : is-antisymmetric div-ℕ
  antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
  antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
    inv (right-zero-law-mul-ℕ k) ∙ p
  antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
    inv q ∙ right-zero-law-mul-ℕ l
  antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
    ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
    ( ( ap
        ( _*ℕ (succ-ℕ x))
        ( inv
          ( is-one-right-is-one-mul-ℕ l k
            ( is-one-is-left-unit-mul-ℕ (l *ℕ k) x
              ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
                ( ap (l *ℕ_) p ∙ q)))))) ∙
      ( p))

  transitive-div-ℕ : is-transitive div-ℕ
  pr1 (transitive-div-ℕ x y z (pair l q) (pair k p)) = l *ℕ k
  pr2 (transitive-div-ℕ x y z (pair l q) (pair k p)) =
    associative-mul-ℕ l k x ∙ (ap (l *ℕ_) p ∙ q)
```
