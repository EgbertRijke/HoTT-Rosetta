# Formal Statements for Exercise 13.14

```agda
module formal-statements-exercise-13-14 where

open import universe-levels
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

### Exercise 13.14(a)

Show that if `h` has a section, then `sec(g)` is a retract of `sec(f)`.

### Exercise 13.14(b)

Show that if `g` has a retraction, then `retr(h)` is a retract of `retr(f)`.

## Formal Statements

### Exercise 13.14(a)

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  where

  section-retract-of-section :
    section h → (section g) retract-of (section f)
  section-retract-of-section = {!!}
```

### Exercise 13.14(b)

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : coherence-triangle-maps f g h)
  where

  retraction-retract-of-retraction :
    retraction g → (retraction h) retract-of (retraction f)
  retraction-retract-of-retraction = {!!}
```
