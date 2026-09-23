# Exercise 9.3

```agda
module exercise-9-3-homotopic-equivalences where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
```

## Problem statement

Consider two functions `f, g : A → B` and a homotopy `H : f ~ g`.
Then

```text
  is-equiv(f) ↔ is-equiv(g).
```

Show that for any two homotopic equivalences `e, e' : A ≃ B`, their inverses are also homotopic.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-section-map-inv-is-invertible-htpy :
    {f f' : A → B} (H : f' ~ f) (F : is-invertible f) →
    is-section f' (map-inv-is-invertible F)
  is-section-map-inv-is-invertible-htpy H (g , S , R) = H ·r g ∙h S

  is-retraction-map-inv-is-invertible-htpy :
    {f f' : A → B} (H : f' ~ f) (F : is-invertible f) →
    is-retraction f' (map-inv-is-invertible F)
  is-retraction-map-inv-is-invertible-htpy H (g , S , R) = g ·l H ∙h R

  is-invertible-htpy :
    {f f' : A → B} → f' ~ f → is-invertible f → is-invertible f'
  is-invertible-htpy H F =
    ( map-inv-is-invertible F ,
      is-section-map-inv-is-invertible-htpy H F ,
      is-retraction-map-inv-is-invertible-htpy H F)

  is-invertible-inv-htpy :
    {f f' : A → B} → f ~ f' → is-invertible f → is-invertible f'
  is-invertible-inv-htpy H = is-invertible-htpy (inv-htpy H)

  htpy-map-inv-is-invertible :
    {f g : A → B} (H : f ~ g) (F : is-invertible f) (G : is-invertible g) →
    map-inv-is-invertible F ~ map-inv-is-invertible G
  htpy-map-inv-is-invertible H F G =
    ( ( inv-htpy (is-retraction-map-inv-is-invertible G)) ·r
      ( map-inv-is-invertible F)) ∙h
    ( ( map-inv-is-invertible G) ·l
      ( ( inv-htpy H ·r map-inv-is-invertible F) ∙h
        ( is-section-map-inv-is-invertible F)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-htpy :
      {f : A → B} (g : A → B) → f ~ g → is-equiv g → is-equiv f
    pr1 (pr1 (is-equiv-htpy g G ((h , H) , (k , K)))) = h
    pr2 (pr1 (is-equiv-htpy g G ((h , H) , (k , K)))) = (G ·r h) ∙h H
    pr1 (pr2 (is-equiv-htpy g G ((h , H) , (k , K)))) = k
    pr2 (pr2 (is-equiv-htpy g G ((h , H) , (k , K)))) = (k ·l G) ∙h K

  is-equiv-htpy-equiv : {f : A → B} (e : A ≃ B) → f ~ map-equiv e → is-equiv f
  is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

  abstract
    is-equiv-htpy' : (f : A → B) {g : A → B} → f ~ g → is-equiv f → is-equiv g
    is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

  is-equiv-htpy-equiv' : (e : A ≃ B) {g : A → B} → map-equiv e ~ g → is-equiv g
  is-equiv-htpy-equiv' e H =
    is-equiv-htpy' (map-equiv e) H (is-equiv-map-equiv e)

  htpy-map-inv-is-equiv :
    {f g : A → B} (H : f ~ g) (F : is-equiv f) (G : is-equiv g) →
    map-inv-is-equiv F ~ map-inv-is-equiv G
  htpy-map-inv-is-equiv H F G =
    htpy-map-inv-is-invertible H
      ( is-invertible-is-equiv F)
      ( is-invertible-is-equiv G)

is-equiv-htpy-id : {l : Level} {A : UU l} {f : A → A} → f ~ id → is-equiv f
is-equiv-htpy-id H = is-equiv-htpy id H is-equiv-id

is-equiv-htpy-id' : {l : Level} {A : UU l} {f : A → A} → id ~ f → is-equiv f
is-equiv-htpy-id' H = is-equiv-htpy' id H is-equiv-id
```
