# Exercise 15.3

```agda
module exercise-15-3-equivalences-are-surjective-embeddings where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-9-2-bi-invertible-maps
open import section-10-3-contractible-maps
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
```

## Problem statement

Consider a map `f : A → B`.
Show that the following are equivalent:

1. `f` is an equivalence.

2. `f` is both surjective and an embedding.

## Solution

```agda
abstract
  is-equiv-is-emb-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-emb f → is-equiv f
  is-equiv-is-emb-is-surjective {f = f} H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb K y)
          ( apply-universal-property-trunc-Prop
            ( H y)
            ( fiber-emb-Prop (f , K) y)
            ( id)))
```
