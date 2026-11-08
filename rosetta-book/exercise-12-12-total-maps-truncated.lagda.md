# Exercise 12.12

```agda
module exercise-12-12-total-maps-truncated where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-10-3-contractible-maps
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import exercise-12-11-truncated-maps-triangles
```

## Problem statement

Let `f : Π(x : A) B(x) → C(x)` be a family of maps.
Show that the following are equivalent:

1. For each `x : A` the map `f(x)` is `k`-truncated.

2. The induced map

   ```text
   tot(f) : (Σ(x : A) B(x)) → (Σ(x : A) C(x))
   ```

   is `k`-truncated.

## Solution

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot H y =
      is-trunc-equiv k
        ( fiber (f (pr1 y)) (pr2 y))
        ( compute-fiber-tot f y)
        ( H (pr1 y) (pr2 y))

  abstract
    is-trunc-map-is-trunc-map-tot :
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot is-trunc-tot-f x z =
      is-trunc-equiv k
        ( fiber (tot f) (x , z))
        ( inv-compute-fiber-tot f (x , z))
        ( is-trunc-tot-f (x , z))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot =
      is-trunc-map-tot neg-two-𝕋

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = is-trunc-map-tot neg-one-𝕋
```

## Supplement

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-map-map-Σ-map-base :
      (k : 𝕋) {f : A → B} (C : B → UU l3) →
      is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
    is-trunc-map-map-Σ-map-base k {f} C H y =
      is-trunc-equiv' k
        ( fiber f (pr1 y))
        ( compute-fiber-map-Σ-map-base f C y)
        ( H (pr1 y))

  abstract
    is-prop-map-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) →
      is-prop-map f → is-prop-map (map-Σ-map-base f C)
    is-prop-map-map-Σ-map-base C = is-trunc-map-map-Σ-map-base neg-one-𝕋 C

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  abstract
    is-trunc-map-map-Σ :
      (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
      is-trunc-map k (map-Σ D f g)
    is-trunc-map-map-Σ k D {f} {g} H K =
      is-trunc-map-left-map-triangle k
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-trunc-map-map-Σ-map-base k D H)
        ( is-trunc-map-tot k K)

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    abstract
      is-contr-map-map-Σ :
        is-contr-map f → ((x : A) → is-contr-map (g x)) →
        is-contr-map (map-Σ D f g)
      is-contr-map-map-Σ = is-trunc-map-map-Σ neg-two-𝕋 D

    abstract
      is-prop-map-map-Σ :
        is-prop-map f → ((x : A) → is-prop-map (g x)) →
        is-prop-map (map-Σ D f g)
      is-prop-map-map-Σ = is-trunc-map-map-Σ neg-one-𝕋 D
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) → is-emb f → is-emb (map-Σ-map-base f C)
    is-emb-map-Σ-map-base C H =
      is-emb-is-prop-map (is-prop-map-map-Σ-map-base C (is-prop-map-is-emb H))

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = map-Σ-map-base (map-emb f) C
  pr2 (emb-Σ-emb-base f C) =
    is-emb-map-Σ-map-base C (is-emb-map-emb f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-emb-map-Σ :
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
  is-emb-map-Σ D H K =
    is-emb-is-prop-map
      ( is-prop-map-map-Σ D
        ( is-prop-map-is-emb H)
        ( λ x → is-prop-map-is-emb (K x)))

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = map-Σ D (map-emb f) (λ x → map-emb (g x))
  pr2 (emb-Σ D f g) =
    is-emb-map-Σ D (is-emb-map-emb f) (λ x → is-emb-map-emb (g x))
```
