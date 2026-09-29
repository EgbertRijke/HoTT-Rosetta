# Exercise 14.3

```agda
module exercise-14-3-products-of-propositional-truncations where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-7-product-functor-equivalences
open import section-10-1-contractible-types
open import section-12-1-propositions
open import exercise-12-7-truncated-products
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-3-universal-properties
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
```

## Problem statement

Consider two maps `f : A → P` and `g : B → Q` into propositions `P` and `Q`.
Show that if both `f` and `g` are propositional truncations then the map `f × g : A × B → P × Q` is also a propositional truncation.
Conclude that

```text
  ‖A × B‖ ≃ ‖A‖ × ‖B‖.
```

## Solution

```agda
abstract
  is-propositional-truncation-product :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
    {A' : UU l3} (P' : Prop l4) (f' : A' → type-Prop P') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-propositional-truncation (product-Prop P P') (map-product f f')
  is-propositional-truncation-product P f P' f' is-ptr-f is-ptr-f' Q =
    is-equiv-top-is-equiv-bottom-square
      ( ev-pair)
      ( ev-pair)
      ( precomp (map-product f f') (type-Prop Q))
      ( λ h a a' → h (f a) (f' a'))
      ( refl-htpy)
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-equiv-comp
        ( λ h a a' → h a (f' a'))
        ( λ h a p' → h (f a) p')
        ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-hom-Prop P' Q)))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a → is-ptr-f' Q)))

equiv-product-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( product-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-product-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( product-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-product unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-product
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A × B ║₋₁ → ║ A ║₋₁ × ║ B ║₋₁
map-distributive-trunc-product-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( ║ A ║₋₁ × ║ B ║₋₁)
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-product unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A ║₋₁ × ║ B ║₋₁ → ║ A × B ║₋₁
map-inv-distributive-trunc-product-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

abstract
  is-equiv-map-distributive-trunc-product-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-distributive-trunc-product-Prop {A = A} {B = B})
  is-equiv-map-distributive-trunc-product-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( map-inv-distributive-trunc-product-Prop)

distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ║ A × B ║₋₁ ≃ ║ A ║₋₁ × ║ B ║₋₁
pr1 distributive-trunc-product-Prop = map-distributive-trunc-product-Prop
pr2 distributive-trunc-product-Prop =
  is-equiv-map-distributive-trunc-product-Prop

abstract
  is-equiv-map-inv-distributive-trunc-product-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-inv-distributive-trunc-product-Prop {A = A} {B = B})
  is-equiv-map-inv-distributive-trunc-product-Prop =
    is-equiv-has-converse-is-prop
      ( is-prop-product is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-distributive-trunc-product-Prop)

inv-distributive-trunc-product-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( ║ A ║₋₁ × ║ B ║₋₁) ≃ ║ A × B ║₋₁
pr1 inv-distributive-trunc-product-Prop =
  map-inv-distributive-trunc-product-Prop
pr2 inv-distributive-trunc-product-Prop =
  is-equiv-map-inv-distributive-trunc-product-Prop
```
