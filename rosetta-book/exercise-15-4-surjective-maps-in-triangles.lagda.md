# Exercise 15.4

```agda
module exercise-15-4-surjective-maps-in-triangles where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-3-contractible-maps
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
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

with `H : f ~ g ∘ h`.

### Exercise 15.4(a)

Show that if `f` is surjective, then `g` is surjective.

### Exercise 15.4(b)

Show that if both `g` and `h` are surjective, then `f` is surjective.

### Exercise 15.4(c)

As a converse to Exercise 12.11, show that if `f` and `h` are `k`-truncated, then `g` is also `k`-truncated.

## Solution

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-right-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
      is-surjective f → is-surjective g
    is-surjective-right-map-triangle f g h H is-surj-f x =
      apply-universal-property-trunc-Prop
        ( is-surj-f x)
        ( trunc-Prop (fiber g x))
        ( λ where (a , refl) → unit-trunc-Prop (h a , inv (H a)))

  is-surjective-left-factor :
    {g : B → X} (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor {g} h =
    is-surjective-right-map-triangle (g ∘ h) g h refl-htpy
```

### Exercise 15.4(b)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-left-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-left-map-triangle f g h H is-surj-g is-surj-h x =
      apply-universal-property-trunc-Prop
        ( is-surj-g x)
        ( trunc-Prop (fiber f x))
        ( λ where
          ( b , refl) →
            apply-universal-property-trunc-Prop
              ( is-surj-h b)
              ( trunc-Prop (fiber f (g b)))
              ( λ where (a , refl) → unit-trunc-Prop (a , H a)))

  is-surjective-comp :
    {g : B → X} {h : A → B} →
    is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp {g} {h} =
    is-surjective-left-map-triangle (g ∘ h) g h refl-htpy

  comp-surjection : B ↠ X → A ↠ B → A ↠ X
  comp-surjection (g , G) (h , H) = g ∘ h , is-surjective-comp G H
```

### Exercise 15.4(c)

Note: This exercise is false as stated. For instance, take `A := ∅` and `g` any map. The exercise would imply that `g` is always an embedding, which is certainly not always the case.

## Supplement

### The composite of a surjective map before an equivalence is surjective

```agda
is-surjective-left-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) {f : A → B} → is-surjective f → is-surjective (map-equiv e ∘ f)
is-surjective-left-comp-equiv e =
  is-surjective-comp (is-surjective-map-equiv e)
```

### The composite of a surjective map after an equivalence is surjective

```agda
is-surjective-right-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-surjective f → (e : A ≃ B) → is-surjective (f ∘ map-equiv e)
is-surjective-right-comp-equiv H e =
  is-surjective-comp H (is-surjective-map-equiv e)
```
