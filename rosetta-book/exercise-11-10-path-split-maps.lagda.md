# Exercise 11.10

```agda
module exercise-11-10-path-split-maps where

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-2-bi-invertible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
```

## Problem statement

(Shulman) We say that a map `f : A → B` is **path-split** if `f` has a section, and for each `x, y : A` the map

```text
  ap_{f}(x,y) : (x = y) → (f(x) = f(y))
```

also has a section.
We write `is-path-split(f)` for the type

```text
  sec(f) × Π(x, y : A) sec(ap_{f}(x,y)).
```

Show that for any map `f : A → B` the following are equivalent:

1. The map `f` is an equivalence.

2. The map `f` is path-split.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-path-split : UU (l1 ⊔ l2)
  is-path-split = section f × ((x y : A) → section (ap f {x = x} {y = y}))

  abstract
    is-path-split-is-equiv : is-equiv f → is-path-split
    pr1 (is-path-split-is-equiv is-equiv-f) = pr1 is-equiv-f
    pr2 (is-path-split-is-equiv is-equiv-f) x y =
      pr1 (is-emb-is-equiv is-equiv-f x y)

  abstract
    is-coherently-invertible-is-path-split :
      is-path-split → is-coherently-invertible f
    pr1 (is-coherently-invertible-is-path-split ((g , G) , s)) =
      g
    pr1 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s))) =
      G
    pr1 (pr2 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s)))) x =
      pr1 (s (g (f x)) x) (G (f x))
    pr2 (pr2 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s)))) x =
      inv (pr2 (s (g (f x)) x) (G (f x)))

  abstract
    is-equiv-is-path-split : is-path-split → is-equiv f
    is-equiv-is-path-split =
      is-equiv-is-coherently-invertible ∘
      is-coherently-invertible-is-path-split
```
