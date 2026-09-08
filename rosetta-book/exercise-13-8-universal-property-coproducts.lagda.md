# Exercise 13.8

```agda
module exercise-13-8-universal-property-coproducts where

open import universe-levels
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-13-1-equivalent-forms-of-function-extensionality
```

## Problem statement

Consider two types `A` and `B`.
Show that the map
```text
(Π(z:A+B) P(z))→(Π(x:A) P(inl(x)))×(Π(y:B) P(inr(b)))
```
given by `f↦ (f∘ inl,f∘ inr)` is an equivalence for any type family `P` over `A+B`.
This property is the **dependent universal property of the coproduct of `A` and `B`**.
Conclude that the map
```text
(A+B→ X)→ (A→ X)× (B→ X)
```
given by `f↦ (f∘ inl,f∘ inr)` is an equivalence for any type `X`.
This latter property is the **universal property of the coproduct of `A` and `B`**.

## Solution

<!-- rosetta-item: exercise-13-8 -->

<!-- rosetta-agda-block: exercise-13-8-universal-property-coproduct -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : A + B → Type l3) →
    ((t : A + B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  pr1 (ev-inl-inr P s) x = s (inl x)
  pr2 (ev-inl-inr P s) y = s (inr y)

  dependent-universal-property-coproduct :
    {l3 : Level} (P : A + B → Type l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coproduct P =
    is-equiv-is-invertible
      ( λ p → ind-coproduct P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → refl))
      ( λ s → eq-htpy (ind-coproduct _ refl-htpy refl-htpy))

  equiv-dependent-universal-property-coproduct :
    {l3 : Level} (P : A + B → Type l3) →
    ((x : A + B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coproduct P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coproduct P) =
    dependent-universal-property-coproduct P

  abstract
    universal-property-coproduct :
      {l3 : Level} (X : Type l3) → is-equiv (ev-inl-inr (λ _ → X))
    universal-property-coproduct X =
      dependent-universal-property-coproduct (λ _ → X)

  equiv-universal-property-coproduct :
    {l3 : Level} (X : Type l3) → (A + B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coproduct X =
    equiv-dependent-universal-property-coproduct (λ _ → X)
```
