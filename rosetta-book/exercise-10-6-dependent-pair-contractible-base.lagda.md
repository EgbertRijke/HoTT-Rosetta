# Exercise 10.6

```agda
module exercise-10-6-dependent-pair-contractible-base where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-2-singleton-induction
```

## Problem statement

Let `A` be a contractible type with center of contraction `a:A`.
Furthermore, let `B` be a type family over `A`.
Show that the map
```text
y↦(a,y):B(a)→Σ(x:A) B(x)
```
is an equivalence.

## Solution

<!-- rosetta-item: exercise-10-6 -->

<!-- rosetta-agda-block: exercise-10-6-contractible-base -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = a
  pr2 (map-inv-left-unit-law-Σ-is-contr b) = b

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr =
    ind-Σ (ind-singleton a C (λ x → B x → B a) (id))

  is-section-map-inv-left-unit-law-Σ-is-contr :
    map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr ~ id
  is-section-map-inv-left-unit-law-Σ-is-contr b =
    ap
      ( λ (f : B a → B a) → f b)
      ( compute-ind-singleton a C (λ x → B x → B a) id)

  is-retraction-map-inv-left-unit-law-Σ-is-contr :
    map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr ~ id
  is-retraction-map-inv-left-unit-law-Σ-is-contr =
    ind-Σ
      ( ind-singleton a C
        ( λ x →
          ( y : B x) →
          map-inv-left-unit-law-Σ-is-contr
            ( map-left-unit-law-Σ-is-contr (x , y)) ＝
          ( x , y))
        ( λ y → ap
          ( map-inv-left-unit-law-Σ-is-contr)
          ( ap (λ f → f y) ( compute-ind-singleton a C (λ x → B x → B a) id))))

  is-equiv-map-left-unit-law-Σ-is-contr :
    is-equiv map-left-unit-law-Σ-is-contr
  is-equiv-map-left-unit-law-Σ-is-contr =
    is-equiv-is-invertible
      map-inv-left-unit-law-Σ-is-contr
      is-section-map-inv-left-unit-law-Σ-is-contr
      is-retraction-map-inv-left-unit-law-Σ-is-contr

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = map-left-unit-law-Σ-is-contr
  pr2 left-unit-law-Σ-is-contr = is-equiv-map-left-unit-law-Σ-is-contr

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr =
      is-equiv-is-invertible
        map-left-unit-law-Σ-is-contr
        is-retraction-map-inv-left-unit-law-Σ-is-contr
        is-section-map-inv-left-unit-law-Σ-is-contr

  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = map-inv-left-unit-law-Σ-is-contr
  pr2 inv-left-unit-law-Σ-is-contr = is-equiv-map-inv-left-unit-law-Σ-is-contr
```
