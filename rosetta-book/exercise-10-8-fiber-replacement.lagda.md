# Exercise 10.8

```agda
module exercise-10-8-fiber-replacement where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-3-contractible-maps
```

## Problem statement

Construct for any map `f : A → B` an equivalence `e : A ≃ Σ(y : B) fib(f,y)` and a homotopy `H : f ~ pr1 ∘ e` witnessing that the triangle

```text

       e
  A ------> Σ(y : B) fib(f,y)
   \       /
  f \     / pr1
     \   /
      ∨ ∨ 
       B
```

commutes.
The projection `pr1 : (Σ(y : B) fib(f,y)) → B` is sometimes also called the **fibrant replacement** of `f`, because first projection maps are fibrations in the homotopy interpretation of type theory.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber : Σ B (fiber f) → A
  map-equiv-total-fiber t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber : pr1 ~ f ∘ map-equiv-total-fiber
  triangle-map-equiv-total-fiber t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fiber : A → Σ B (fiber f)
  map-inv-equiv-total-fiber x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber :
    is-retraction map-equiv-total-fiber map-inv-equiv-total-fiber
  is-retraction-map-inv-equiv-total-fiber (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber :
    is-section map-equiv-total-fiber map-inv-equiv-total-fiber
  is-section-map-inv-equiv-total-fiber x = refl

  abstract
    is-equiv-map-equiv-total-fiber : is-equiv map-equiv-total-fiber
    is-equiv-map-equiv-total-fiber =
      is-equiv-is-invertible
        map-inv-equiv-total-fiber
        is-section-map-inv-equiv-total-fiber
        is-retraction-map-inv-equiv-total-fiber

    is-equiv-map-inv-equiv-total-fiber : is-equiv map-inv-equiv-total-fiber
    is-equiv-map-inv-equiv-total-fiber =
      is-equiv-is-invertible
        map-equiv-total-fiber
        is-retraction-map-inv-equiv-total-fiber
        is-section-map-inv-equiv-total-fiber

  equiv-total-fiber : Σ B (fiber f) ≃ A
  pr1 equiv-total-fiber = map-equiv-total-fiber
  pr2 equiv-total-fiber = is-equiv-map-equiv-total-fiber

  inv-equiv-total-fiber : A ≃ Σ B (fiber f)
  pr1 inv-equiv-total-fiber = map-inv-equiv-total-fiber
  pr2 inv-equiv-total-fiber = is-equiv-map-inv-equiv-total-fiber

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber' : Σ B (fiber' f) → A
  map-equiv-total-fiber' t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber' : pr1 ~ f ∘ map-equiv-total-fiber'
  triangle-map-equiv-total-fiber' t = pr2 (pr2 t)

  map-inv-equiv-total-fiber' : A → Σ B (fiber' f)
  map-inv-equiv-total-fiber' x = (f x , x , refl)

  is-retraction-map-inv-equiv-total-fiber' :
    is-retraction map-equiv-total-fiber' map-inv-equiv-total-fiber'
  is-retraction-map-inv-equiv-total-fiber' (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber' :
    is-section map-equiv-total-fiber' map-inv-equiv-total-fiber'
  is-section-map-inv-equiv-total-fiber' x = refl

  is-equiv-map-equiv-total-fiber' : is-equiv map-equiv-total-fiber'
  is-equiv-map-equiv-total-fiber' =
    is-equiv-is-invertible
      ( map-inv-equiv-total-fiber')
      ( is-section-map-inv-equiv-total-fiber')
      ( is-retraction-map-inv-equiv-total-fiber')

  is-equiv-map-inv-equiv-total-fiber' : is-equiv map-inv-equiv-total-fiber'
  is-equiv-map-inv-equiv-total-fiber' =
    is-equiv-is-invertible
      map-equiv-total-fiber'
      is-retraction-map-inv-equiv-total-fiber'
      is-section-map-inv-equiv-total-fiber'

  equiv-total-fiber' : Σ B (fiber' f) ≃ A
  pr1 equiv-total-fiber' = map-equiv-total-fiber'
  pr2 equiv-total-fiber' = is-equiv-map-equiv-total-fiber'

  inv-equiv-total-fiber' : A ≃ Σ B (fiber' f)
  pr1 inv-equiv-total-fiber' = map-inv-equiv-total-fiber'
  pr2 inv-equiv-total-fiber' = is-equiv-map-inv-equiv-total-fiber'
```
