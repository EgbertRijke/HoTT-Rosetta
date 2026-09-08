# Exercise 9.4

```agda
module exercise-9-4-three-for-two-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
```

## Problem statement

Consider a commuting triangle
<!-- rosetta-diagram: cdb284b42255; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                 [B]

           [X]

Arrows:
- A --h--> B
- A --f--> X
- B --g--> X
```
with `H:f~ g∘ h`.

<div class="subexenum">

Suppose that the map `h` has a section `s:B → A`.
Show that the triangle
<!-- rosetta-diagram: 5c672de7e457; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [B]                 [A]

           [X]

Arrows:
- B --s--> A
- B --g--> X
- A --f--> X
```
commutes, and that `f` has a section if and only if `g` has a section.

Suppose that the map `g` has a retraction `r:X→ B`.
Show that the triangle
<!-- rosetta-diagram: 32d6c414af56; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
 [A]                 [X]

           [B]

Arrows:
- A --f--> X
- A --h--> B
- X --r--> B
```
commutes, and that `f` has a retraction if and only if `h` has a retraction.

(The **3-for-2 property** for equivalences.) Show that if any two of the functions
```text
f, g, h
```
are equivalences, then so is the third.
Conclude that any section and any retraction of an equivalence is again an equivalence.

</div>

## Solution

<!-- rosetta-item: exercise-9-4 -->

<!-- rosetta-agda-block: exercise-9-4-section-comp -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (g : B → X) (h : A → B) (t : section h) (s : section g)
  where

  map-section-comp : X → A
  map-section-comp = map-section h t ∘ map-section g s

  is-section-map-section-comp :
    is-section (g ∘ h) map-section-comp
  is-section-map-section-comp =
    ( g ·l is-section-map-section h t ·r map-section g s) ∙h
    ( is-section-map-section g s)

  section-comp : section (g ∘ h)
  pr1 section-comp = map-section-comp
  pr2 section-comp = is-section-map-section-comp
```

<!-- rosetta-agda-block: exercise-9-4-section-right-prime -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H' : g ∘ h ~ f) (s : section f)
  where

  map-section-right-map-triangle' : X → B
  map-section-right-map-triangle' = h ∘ map-section f s

  is-section-map-section-right-map-triangle' :
    is-section g map-section-right-map-triangle'
  is-section-map-section-right-map-triangle' =
    (H' ·r map-section f s) ∙h is-section-map-section f s

  section-right-map-triangle' : section g
  pr1 section-right-map-triangle' =
    map-section-right-map-triangle'
  pr2 section-right-map-triangle' =
    is-section-map-section-right-map-triangle'
```

<!-- rosetta-agda-block: exercise-9-4-section-right -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) (s : section f)
  where

  map-section-right-map-triangle : X → B
  map-section-right-map-triangle =
    map-section-right-map-triangle' f g h (inv-htpy H) s

  is-section-map-section-right-map-triangle :
    is-section g map-section-right-map-triangle
  is-section-map-section-right-map-triangle =
    is-section-map-section-right-map-triangle' f g h (inv-htpy H) s

  section-right-map-triangle : section g
  section-right-map-triangle =
    section-right-map-triangle' f g h (inv-htpy H) s
```

<!-- rosetta-agda-block: exercise-9-4-section-left -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) (t : section h)
  where

  map-section-left-map-triangle : section g → X → A
  map-section-left-map-triangle s = map-section-comp g h t s

  is-section-map-section-left-map-triangle :
    (s : section g) → is-section f (map-section-left-map-triangle s)
  is-section-map-section-left-map-triangle s =
    ( H ·r map-section-comp g h t s) ∙h
    ( is-section-map-section-comp g h t s)

  section-left-map-triangle : section g → section f
  pr1 (section-left-map-triangle s) = map-section-left-map-triangle s
  pr2 (section-left-map-triangle s) = is-section-map-section-left-map-triangle s
```

<!-- rosetta-agda-block: exercise-9-4-retraction-comp -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (g : B → X) (h : A → B) (r : retraction g) (s : retraction h)
  where

  map-retraction-comp : X → A
  map-retraction-comp = map-retraction h s ∘ map-retraction g r

  is-retraction-map-retraction-comp : is-retraction (g ∘ h) map-retraction-comp
  is-retraction-map-retraction-comp =
    ( map-retraction h s ·l (is-retraction-map-retraction g r ·r h)) ∙h
    ( is-retraction-map-retraction h s)

  retraction-comp : retraction (g ∘ h)
  pr1 retraction-comp = map-retraction-comp
  pr2 retraction-comp = is-retraction-map-retraction-comp
```

<!-- rosetta-agda-block: exercise-9-4-retraction-top -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : g ∘ h ~ f)
  (r : retraction f)
  where

  map-retraction-top-map-triangle' : B → A
  map-retraction-top-map-triangle' = map-retraction f r ∘ g

  is-retraction-map-retraction-top-map-triangle' :
    is-retraction h map-retraction-top-map-triangle'
  is-retraction-map-retraction-top-map-triangle' =
    (map-retraction f r ·l H) ∙h is-retraction-map-retraction f r

  retraction-top-map-triangle' : retraction h
  pr1 retraction-top-map-triangle' =
    map-retraction-top-map-triangle'
  pr2 retraction-top-map-triangle' =
    is-retraction-map-retraction-top-map-triangle'

module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  (r : retraction f)
  where

  retraction-top-map-triangle : retraction h
  retraction-top-map-triangle =
    retraction-top-map-triangle' f g h (inv-htpy H) r
```

<!-- rosetta-agda-block: exercise-9-4-retraction-left -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  (r : retraction g) (s : retraction h)
  where

  map-retraction-left-map-triangle : X → A
  map-retraction-left-map-triangle = map-retraction-comp g h r s

  is-retraction-map-retraction-left-map-triangle :
    is-retraction f map-retraction-left-map-triangle
  is-retraction-map-retraction-left-map-triangle =
    ( map-retraction-comp g h r s ·l H) ∙h
    ( is-retraction-map-retraction-comp g h r s)

  retraction-left-map-triangle : retraction f
  pr1 retraction-left-map-triangle =
    map-retraction-left-map-triangle
  pr2 retraction-left-map-triangle =
    is-retraction-map-retraction-left-map-triangle
```

<!-- rosetta-agda-block: exercise-9-4-equiv-left -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  abstract
    is-equiv-left-map-triangle : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-left-map-triangle H G) =
      section-left-map-triangle f g h T
        ( section-is-equiv H)
        ( section-is-equiv G)
    pr2 (is-equiv-left-map-triangle H G) =
      retraction-left-map-triangle f g h T
        ( retraction-is-equiv G)
        ( retraction-is-equiv H)
```

<!-- rosetta-agda-block: exercise-9-4-equiv-right -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  abstract
    is-equiv-right-map-triangle :
      is-equiv f → is-equiv h → is-equiv g
    is-equiv-right-map-triangle
      ( section-f , retraction-f)
      ( (sh , is-section-sh) , retraction-h) =
        ( pair
          ( section-right-map-triangle f g h H section-f)
          ( retraction-left-map-triangle g f sh
            ( inv-htpy
              ( ( H ·r map-section h (sh , is-section-sh)) ∙h
                ( g ·l is-section-map-section h (sh , is-section-sh))))
            ( retraction-f)
            ( h , is-section-sh)))
```

<!-- rosetta-agda-block: exercise-9-4-equiv-top -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → section h
  section-is-equiv-top-map-triangle G F =
    section-left-map-triangle h
      ( map-retraction-is-equiv G)
      ( f)
      ( inv-htpy
        ( ( map-retraction g (retraction-is-equiv G) ·l H) ∙h
          ( is-retraction-map-retraction g (retraction-is-equiv G) ·r h)))
      ( section-is-equiv F)
      ( g , is-retraction-map-retraction-is-equiv G)

  map-section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → B → A
  map-section-is-equiv-top-map-triangle G F =
    map-section h (section-is-equiv-top-map-triangle G F)

  abstract
    is-equiv-top-map-triangle :
      is-equiv g → is-equiv f → is-equiv h
    is-equiv-top-map-triangle
      ( section-g , (rg , is-retraction-rg))
      ( section-f , retraction-f) =
      ( pair
        ( section-left-map-triangle h rg f
          ( inv-htpy
            ( ( map-retraction g (rg , is-retraction-rg) ·l H) ∙h
              ( is-retraction-map-retraction g (rg , is-retraction-rg) ·r h)))
          ( section-f)
          ( g , is-retraction-rg))
        ( retraction-top-map-triangle f g h H retraction-f))
```

<!-- rosetta-agda-block: exercise-9-4-composition-equivalences -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  where

  opaque
    is-equiv-comp :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    pr1 (is-equiv-comp g h (sh , rh) (sg , rg)) = section-comp g h sh sg
    pr2 (is-equiv-comp g h (sh , rh) (sg , rg)) = retraction-comp g h rg rh

  comp-equiv : B ≃ X → A ≃ B → A ≃ X
  pr1 (comp-equiv g h) = map-equiv g ∘ map-equiv h
  pr2 (comp-equiv g h) = is-equiv-comp (pr1 g) (pr1 h) (pr2 h) (pr2 g)

  infixr 15 _∘e_
  _∘e_ : B ≃ X → A ≃ B → A ≃ X
  _∘e_ = comp-equiv
```
