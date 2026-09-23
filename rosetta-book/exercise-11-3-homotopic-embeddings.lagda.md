# Exercise 11.3

```agda
module exercise-11-3-homotopic-embeddings where

open import universe-levels

open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
```

## Problem statement

Show that

```text
  (f ~ g) → (is-emb(f) ↔ is-emb(g))
```

for any `f, g : A → B`.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy : {f g : A → B} (H : f ~ g) → is-emb g → is-emb f
    is-emb-htpy {f} {g} H is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( ap g)
        ( concat' (f x) (H y))
        ( ap f)
        ( concat (H x) (g y))
        ( nat-htpy H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))

  is-emb-htpy-emb : {f : A → B} (e : A ↪ B) → f ~ map-emb e → is-emb f
  is-emb-htpy-emb e H = is-emb-htpy H (is-emb-map-emb e)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy' : {f g : A → B} (H : f ~ g) → is-emb f → is-emb g
    is-emb-htpy' H is-emb-f = is-emb-htpy (inv-htpy H) is-emb-f

  is-emb-htpy-emb' : (e : A ↪ B) {g : A → B} → map-emb e ~ g → is-emb g
  is-emb-htpy-emb' e H = is-emb-htpy' H (is-emb-map-emb e)
```
