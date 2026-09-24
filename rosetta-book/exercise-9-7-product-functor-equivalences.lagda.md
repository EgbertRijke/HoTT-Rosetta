# Exercise 9.7

```agda
module exercise-9-7-product-functor-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-4-equivalences-are-contractible-maps
```

## Problem statement

### Exercise 9.7(a)

Construct for any two maps `f : A → A'` and `g : B → B'`, a map

```text
  f × g : A × B → A' × B'
```

### Exercise 9.7(b)

Show that `id_A × id_B ~ id_{A × B}`.

### Exercise 9.7(c)

Show that for any two pairs of composable functions

```text
      f         f'
  A -----> A' -----> A"

      g         g'
  B -----> B' -----> B"
```

there is a homotopy `(f' ∘ f) × (g' ∘ g) ~ (f' × g') ∘ (f × g)`.

### Exercise 9.7(d)

Show that if `H : f ~ f'` and `K : g ~ g'`, then there is a homotopy

```text
  H × K : (f × g) ~ (f' × g').
```

### Exercise 9.7(e)

Show that for any two maps `f : A → A'` and `g : B → B'`, the following are equivalent:

1. The map `f × g` is an equivalence.

2. There are functions

   ```text
     α : B → is-equiv(f)
     β : A → is-equiv(g).
   ```

## Solutions

### Exercise 9.7(a)

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  map-product : (A × C) → (B × D)

  pr1 (map-product t) = f (pr1 t)
  pr2 (map-product t) = g (pr2 t)

  map-product-pr1 : pr1 ∘ map-product ~ f ∘ pr1
  map-product-pr1 (a , c) = refl

  map-product-pr2 : pr2 ∘ map-product ~ g ∘ pr2
  map-product-pr2 (a , c) = refl

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  coherence-square-map-product :
    coherence-square-maps
      ( map-product f id)
      ( map-product id g)
      ( map-product id g)
      ( map-product f id)
  coherence-square-map-product t = refl
```

### Exercise 9.7(b)

```agda
map-product-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  map-product (id {A = A}) (id {A = B}) ~ id
map-product-id (a , b) = refl
```

### Exercise 9.7(c)

```agda
preserves-comp-map-product :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-product (h ∘ f) (k ∘ g) ~ map-product h k ∘ map-product f g
preserves-comp-map-product f g h k t = refl
```

### Exercise 9.7(d)

```agda
htpy-map-product :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-product f g ~ map-product f' g'
htpy-map-product H K (a , b) = eq-pair (H a) (K b)
```

### Exercise 9.7(e)

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-inv-map-product :
    (f : A → C) (g : B → D) → is-equiv f → is-equiv g → C × D → A × B
  map-inv-map-product f g H K =
    map-product (map-inv-is-equiv H) (map-inv-is-equiv K)

  is-section-map-inv-map-product :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-product f g ∘ map-inv-map-product f g H K ~ id
  is-section-map-inv-map-product f g H K =
    htpy-map-product
      ( is-section-map-inv-is-equiv H)
      ( is-section-map-inv-is-equiv K)

  is-retraction-map-inv-map-product :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-inv-map-product f g H K ∘ map-product f g ~ id
  is-retraction-map-inv-map-product f g H K =
    htpy-map-product
      ( is-retraction-map-inv-is-equiv H)
      ( is-retraction-map-inv-is-equiv K)

  is-equiv-map-product :
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (map-product f g)
  is-equiv-map-product f g H K =
    is-equiv-is-invertible
      ( map-inv-map-product f g H K)
      ( is-section-map-inv-map-product f g H K)
      ( is-retraction-map-inv-map-product f g H K)

  equiv-product : A ≃ C → B ≃ D → A × B ≃ C × D
  pr1 (equiv-product (f , is-equiv-f) (g , is-equiv-g)) = map-product f g
  pr2 (equiv-product (f , is-equiv-f) (g , is-equiv-g)) =
    is-equiv-map-product f g is-equiv-f is-equiv-g
```

