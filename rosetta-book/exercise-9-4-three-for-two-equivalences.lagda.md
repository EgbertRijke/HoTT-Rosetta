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

## Supplement

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

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-map-triangle id g f (inv-htpy H) is-equiv-id is-equiv-f
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → f ∘ g ~ id → is-equiv g
  is-equiv-is-section {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-top-map-triangle id f g (inv-htpy H) is-equiv-f is-equiv-id
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-section :
      (s : section f) → is-equiv (map-section f s) → is-equiv f
    is-equiv-is-equiv-section (g , G) S = is-equiv-is-retraction S G
```

### If a retraction of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-retraction :
      (r : retraction f) → is-equiv (map-retraction f r) → is-equiv f
    is-equiv-is-equiv-retraction (g , G) R = is-equiv-is-section R G
```

## Supplement

### Equivalences in commuting squares

```agda
is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-left-map-triangle
      ( map-equiv j ∘ f)
      ( g)
      ( map-equiv i)
      ( H)
      ( is-equiv-map-equiv i)
      ( K))

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' {f = f} {g} i j H K =
  is-equiv-left-factor
    ( g)
    ( map-equiv i)
    ( is-equiv-left-map-triangle
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)
```

We will assume a commuting square

```text
        h
    A -----> C
    |        |
  f |        | g
    ∨        ∨
    B -----> D
        i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h))
  where

  abstract
    is-equiv-top-is-equiv-left-square :
      is-equiv i → is-equiv f → is-equiv g → is-equiv h
    is-equiv-top-is-equiv-left-square Ei Ef Eg =
      is-equiv-top-map-triangle (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square Ef Eg Ei =
      is-equiv-top-map-triangle (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square Ef Eg Eh =
      is-equiv-left-factor i f
        ( is-equiv-left-map-triangle (i ∘ f) g h H Eh Eg)
        ( Ef)

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square Eh Ei Eg =
      is-equiv-right-factor i f Ei
        ( is-equiv-left-map-triangle (i ∘ f) g h H Eh Eg)

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square Eh Ei Ef =
      is-equiv-right-map-triangle (i ∘ f) g h H (is-equiv-comp i f Ef Ei) Eh
```

### If the top map has a section, then the reversed triangle with the section on top commutes

If `t : B → A` is a [section](foundation-core.sections.md) of the top map `h`,
then the triangle

```text
       t
  B ------> A
   \       /
   g\     /f
     \   /
      ∨ ∨
       X
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (t : section h)
  where

  inv-triangle-section : coherence-triangle-maps' g f (map-section h t)
  inv-triangle-section =
    (H ·r map-section h t) ∙h (g ·l is-section-map-section h t)

  triangle-section : coherence-triangle-maps g f (map-section h t)
  triangle-section = inv-htpy inv-triangle-section
```

### If the right map has a retraction, then the reversed triangle with the retraction on the right commutes

If `r : X → B` is a retraction of the right map `g` in a triangle `f ~ g ∘ h`,
then the triangle

```text
       f
  A ------> X
   \       /
   h\     /r
     \   /
      ∨ ∨
       B
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  (r : retraction g)
  where

  inv-triangle-retraction : coherence-triangle-maps' h (map-retraction g r) f
  inv-triangle-retraction =
    (map-retraction g r ·l H) ∙h (is-retraction-map-retraction g r ·r h)

  triangle-retraction : coherence-triangle-maps h (map-retraction g r) f
  triangle-retraction = inv-htpy inv-triangle-retraction
```
