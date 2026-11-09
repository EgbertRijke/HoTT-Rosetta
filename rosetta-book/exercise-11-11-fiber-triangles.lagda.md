# Exercise 11.11

```agda
module exercise-11-11-fiber-triangles where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import exercise-10-8-fiber-replacement
open import section-11-1-families-of-equivalences
```

## Problem statement

Consider a triangle

```text
         h
    A ------> B
     \       /
    f \     / g
       \   /
        v v
         X
```

with a homotopy `H : f ~ g ∘ h` witnessing that the triangle commutes.

### Exercise 11.11(a)

Construct a family of maps

```text
  fib-triangle(h,H) : Π(x : X) fib(f, x) → fib(g, x),
```

for which the square

```text
                        tot(fib-triangle(h,H))
  Σ(x : X) fib(f, x) ---------------------------> Σ(x : X) fib(g, x)
           |                                               |
           |                                               |
           v                                               v
           A ---------------------h----------------------> B
```

commutes, where the vertical maps are as constructed in Exercise 10.8.

### Exercise 11.11(b)

Show that `h` is an equivalence if and only if `fib-triangle(h,H)` is a family of equivalences.

## Solutions

### Exercise 11.11(a)

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  fiber-triangle :
    (x : X) → fiber f x → fiber g x
  fiber-triangle .(f a) (a , refl) = (h a , inv (H a))

  square-tot-fiber-triangle :
    ( h ∘ map-equiv-total-fiber f) ~
    ( map-equiv-total-fiber g ∘ tot fiber-triangle)
  square-tot-fiber-triangle (.(f a) , a , refl) = refl
```

### Exercise 11.11(b)

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-fiberwise-equiv-is-equiv-triangle :
      is-equiv h → is-fiberwise-equiv (fiber-triangle f g h H)
    is-fiberwise-equiv-is-equiv-triangle E =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fiber f)
          ( map-equiv-total-fiber g)
          ( tot (fiber-triangle f g h H))
          ( h)
          ( square-tot-fiber-triangle f g h H)
          ( is-equiv-map-equiv-total-fiber f)
          ( is-equiv-map-equiv-total-fiber g)
          ( E))

  abstract
    is-equiv-triangle-is-fiberwise-equiv :
      is-fiberwise-equiv (fiber-triangle f g h H) → is-equiv h
    is-equiv-triangle-is-fiberwise-equiv E =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fiber f)
        ( map-equiv-total-fiber g)
        ( tot (fiber-triangle f g h H))
        ( h)
        ( square-tot-fiber-triangle f g h H)
        ( is-equiv-map-equiv-total-fiber f)
        ( is-equiv-map-equiv-total-fiber g)
        ( is-equiv-tot-is-fiberwise-equiv E)
```
