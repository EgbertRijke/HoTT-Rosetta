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

### Exercise 9.4(a)

Suppose that the map `h` has a section `s:B → A`.
Show that the triangle

```text
       s
  B ------> A
   \       /
  g \     / f
     \   /
      ∨ ∨
       X
```

commutes, and that `f` has a section if and only if `g` has a section.

### Exercise 9.4(b)

Suppose that the map `g` has a retraction `r:X→ B`.
Show that the triangle

```text
       f
  A ------> X
   \       /
  h \     / r
     \   /
      ∨ ∨
       B
```

commutes, and that `f` has a retraction if and only if `h` has a retraction.

### Exercise 9.4(c) The 3-for-2 property for equivalences.

Show that if any two of the functions `f`, `g`, and `h` are equivalences, then so is the third.
Conclude that any section and any retraction of an equivalence is again an equivalence.

## Solutions

### Exercise 9.4(a)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

### Exercise 9.4(b)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  (r : retraction f)
  where

  retraction-top-map-triangle : retraction h
  retraction-top-map-triangle =
    retraction-top-map-triangle' f g h (inv-htpy H) r

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

### Exercise 9.4(c)

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  abstract
    is-equiv-left-map-triangle : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-left-map-triangle K L) =
      section-left-map-triangle f g h H
        ( section-is-equiv K)
        ( section-is-equiv L)
    pr2 (is-equiv-left-map-triangle K L) =
      retraction-left-map-triangle f g h H
        ( retraction-is-equiv L)
        ( retraction-is-equiv K)

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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
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

  is-equiv-left-factor :
    (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor g h is-equiv-gh is-equiv-h =
      is-equiv-right-map-triangle (g ∘ h) g h refl-htpy is-equiv-gh is-equiv-h

  is-equiv-right-factor :
    (g : B → X) (h : A → B) →
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor g h is-equiv-g is-equiv-gh =
    is-equiv-top-map-triangle (g ∘ h) g h refl-htpy is-equiv-g is-equiv-gh
```

## Supplementary definitions

### If `g ∘ h` has a section then `g` has a section

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (s : section (g ∘ h))
  where

  map-section-left-factor : X → B
  map-section-left-factor = h ∘ map-section (g ∘ h) s

  is-section-map-section-left-factor : is-section g map-section-left-factor
  is-section-map-section-left-factor = pr2 s

  section-left-factor : section g
  pr1 section-left-factor = map-section-left-factor
  pr2 section-left-factor = is-section-map-section-left-factor
```

### If `g ∘ f` has a retraction then `f` has a retraction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (r : retraction (g ∘ h))
  where

  map-retraction-right-factor : B → A
  map-retraction-right-factor = map-retraction (g ∘ h) r ∘ g

  is-retraction-map-retraction-right-factor :
    is-retraction h map-retraction-right-factor
  is-retraction-map-retraction-right-factor =
    is-retraction-map-retraction (g ∘ h) r

  retraction-right-factor : retraction h
  pr1 retraction-right-factor = map-retraction-right-factor
  pr2 retraction-right-factor = is-retraction-map-retraction-right-factor
```
