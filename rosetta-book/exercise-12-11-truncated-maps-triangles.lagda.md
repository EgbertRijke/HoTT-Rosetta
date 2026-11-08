# Exercise 12.11

```agda
module exercise-12-11-truncated-maps-triangles where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-10-3-contractible-maps
open import section-12-4-general-truncation-levels
open import exercise-12-6-truncated-sigma-types
```

## Problem statement

Consider a commuting triangle

```text
       h
  A ------> B
   \       /
  f \     / g
     \   /
      ∨ ∨
       X
```

with `H : f ~ g ∘ h`, and suppose that `g` is `k`-truncated.
Show that `f` is `k`-truncated if and only if `h` is `k`-truncated.

## Solution

```agda
abstract
  is-trunc-map-top-map-triangle :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-top-map-triangle k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → g (h z) ＝ g b))
        ( map-compute-fiber-comp g h (g b))
        ( is-equiv-map-compute-fiber-comp g h (g b))
        ( is-trunc-map-htpy k (inv-htpy H) is-trunc-f (g b)))
      ( b , refl)

abstract
  is-trunc-map-comp :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k (g ∘ h)
  is-trunc-map-comp k g h is-trunc-g is-trunc-h x =
    is-trunc-is-equiv k
        ( Σ (fiber g x) (λ t → fiber h (pr1 t)))
        ( map-compute-fiber-comp g h x)
        ( is-equiv-map-compute-fiber-comp g h x)
        ( is-trunc-Σ
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t)))

comp-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {X : UU l3} (g : trunc-map k B X) (h : trunc-map k A B) →
  trunc-map k A X
pr1 (comp-trunc-map k g h) = pr1 g ∘ pr1 h
pr2 (comp-trunc-map k g h) =
  is-trunc-map-comp k (pr1 g) (pr1 h) (pr2 g) (pr2 h)

abstract
  is-trunc-map-left-map-triangle :
    {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-left-map-triangle k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k H
      ( is-trunc-map-comp k g h is-trunc-g is-trunc-h)
```
