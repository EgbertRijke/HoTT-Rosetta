# Exercise 11.4

```agda
module exercise-11-4-embedding-triangles where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-3-homotopic-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
open import exercise-11-3-homotopic-embeddings
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

### Exercise 11.4(a)

Suppose that `g` is an embedding.
Show that `f` is an embedding if and only if `h` is an embedding.

### Exercise 11.4(b)

Suppose that `h` is an equivalence.
Show that `f` is an embedding if and only if `g` is an embedding.

## Solution

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-comp :
    (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp g h is-emb-g is-emb-h x y =
    is-equiv-left-map-triangle
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y))

  abstract
    is-emb-left-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb h → is-emb f
    is-emb-left-map-triangle f g h H is-emb-g is-emb-h =
      is-emb-htpy H (is-emb-comp g h is-emb-g is-emb-h)

  is-emb-map-comp-emb :
    (g : B ↪ C) (f : A ↪ B) → is-emb (map-emb g ∘ map-emb f)
  is-emb-map-comp-emb (g , H) (f , K) = is-emb-comp g f H K

  comp-emb :
    (B ↪ C) → (A ↪ B) → (A ↪ C)
  pr1 (comp-emb (g , H) (f , K)) = g ∘ f
  pr2 (comp-emb (g , H) (f , K)) = is-emb-comp g f H K

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-right-factor :
    (g : B → C) (h : A → B) →
    is-emb g → is-emb (g ∘ h) → is-emb h
  is-emb-right-factor g h is-emb-g is-emb-gh x y =
    is-equiv-top-map-triangle
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-g (h x) (h y))
      ( is-emb-gh x y)

  abstract
    is-emb-top-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb f → is-emb h
    is-emb-top-map-triangle f g h H is-emb-g is-emb-f x y =
      is-equiv-top-map-triangle
        ( ap (g ∘ h))
        ( ap g)
        ( ap h)
        ( ap-comp g h)
        ( is-emb-g (h x) (h y))
        ( is-emb-htpy (inv-htpy H) is-emb-f x y)

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-left-map-triangle f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb f → is-emb g
    is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
      is-emb-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( is-section-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-emb-f)
```

