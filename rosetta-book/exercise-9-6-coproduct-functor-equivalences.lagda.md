# Exercise 9.6

```agda
module exercise-9-6-coproduct-functor-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-8-7-decidable-equality-coproducts
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
open import section-11-5-disjointness-of-coproducts
```

## Problem statement

Recall from Remark 4.4.2 that coproducts have a **functorial action**, i.e., that for every `f : A → A'` and every `g : B → B'` we have a map

```text
  f + g : (A + B) → (A' + B').
```

### Exercise 9.6(a)

Show that `id_A + id_B ~ id_{A+B}`.

### Exercise 9.6(b)

Show that for any two pairs of composable functions

```text
      f         f'
  A -----> A' -----> A"

      g         g'
  B -----> B' -----> B"
```

there is a homotopy `(f' ∘ f) + (g' ∘ g) ~ (f' + g') ∘ (f + g)`.

### Exercise 9.6(c)

Show that if `H : f ~ f'` and `K : g ~ g'`, then there is a homotopy

```text
  H + K : (f + g) ~ (f' + g').
```

### Exercise 9.6(d)

Show that if both `f` and `g` are equivalences, then so is `f + g`. (The converse of this statement also holds, see Exercise 11.7.)

## Solutions

### Exercise 9.6(a)

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  id-map-coproduct : (map-coproduct (id {A = A}) (id {A = B})) ~ id
  id-map-coproduct (inl x) = refl
  id-map-coproduct (inr x) = refl
```

### Exercise 9.6(b)

```agda
module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where

  preserves-comp-map-coproduct :
    map-coproduct (f' ∘ f) (g' ∘ g) ~ map-coproduct f' g' ∘ map-coproduct f g
  preserves-comp-map-coproduct (inl x) = refl
  preserves-comp-map-coproduct (inr y) = refl
```

### Exercise 9.6(c)

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where

  htpy-map-coproduct : map-coproduct f g ~ map-coproduct f' g'
  htpy-map-coproduct (inl x) = ap inl (H x)
  htpy-map-coproduct (inr y) = ap inr (K y)
```

### Exercise 9.6(d)

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  map-equiv-coproduct : A ≃ A' → B ≃ B' → A + B → A' + B'
  map-equiv-coproduct f g = map-coproduct (map-equiv f) (map-equiv g)

  map-inv-equiv-coproduct : A ≃ A' → B ≃ B' → A' + B' → A + B
  map-inv-equiv-coproduct f g =
    map-coproduct (map-inv-equiv f) (map-inv-equiv g)

  is-section-map-inv-equiv-coproduct :
    (f : A ≃ A') (g : B ≃ B') →
    is-section
      ( map-equiv-coproduct f g)
      ( map-inv-equiv-coproduct f g)
  is-section-map-inv-equiv-coproduct f g =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( map-inv-equiv f)
        ( map-equiv f)
        ( map-inv-equiv g)
        ( map-equiv g))) ∙h
    ( htpy-map-coproduct
      ( is-section-map-inv-equiv f)
      ( is-section-map-inv-equiv g)) ∙h
    ( id-map-coproduct A' B')

  is-retraction-map-inv-equiv-coproduct :
    (f : A ≃ A') (g : B ≃ B') →
    is-retraction
      ( map-equiv-coproduct f g)
      ( map-inv-equiv-coproduct f g)
  is-retraction-map-inv-equiv-coproduct f g =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( map-equiv f)
        ( map-inv-equiv f)
        ( map-equiv g)
        ( map-inv-equiv g))) ∙h
    ( htpy-map-coproduct
      ( is-retraction-map-inv-equiv f)
      ( is-retraction-map-inv-equiv g)) ∙h
    ( id-map-coproduct A B)

  is-equiv-map-coproduct :
    {f : A → A'} {g : B → B'} →
    is-equiv f → is-equiv g → is-equiv (map-coproduct f g)
  is-equiv-map-coproduct {f} {g} H K =
    is-equiv-is-invertible
      ( map-coproduct (map-inv-is-equiv H) (map-inv-is-equiv K))
      ( is-section-map-inv-equiv-coproduct (f , H) (g , K))
      ( is-retraction-map-inv-equiv-coproduct (f , H) (g , K))

  equiv-coproduct : A ≃ A' → B ≃ B' → (A + B) ≃ (A' + B')
  equiv-coproduct e e' =
    ( map-equiv-coproduct e e' ,
      is-equiv-map-coproduct (is-equiv-map-equiv e) (is-equiv-map-equiv e'))
```

## Supplement

### The fibers of `map-coproduct`

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B)
  where

  fiber-map-coproduct-inl-fiber :
    (x : A) → fiber f x → fiber (map-coproduct f g) (inl x)
  pr1 (fiber-map-coproduct-inl-fiber x (a' , p)) = inl a'
  pr2 (fiber-map-coproduct-inl-fiber x (a' , p)) = ap inl p

  fiber-fiber-map-coproduct-inl :
    (x : A) → fiber (map-coproduct f g) (inl x) → fiber f x
  pr1 (fiber-fiber-map-coproduct-inl x (inl a' , p)) = a'
  pr2 (fiber-fiber-map-coproduct-inl x (inl a' , p)) =
    map-compute-eq-coproduct-inl-inl (f a') x p
  fiber-fiber-map-coproduct-inl x (inr b' , p) =
    ex-falso (is-empty-eq-coproduct-inr-inl (g b') x p)

  abstract
    is-section-fiber-fiber-map-coproduct-inl :
      (x : A) →
      fiber-map-coproduct-inl-fiber x ∘ fiber-fiber-map-coproduct-inl x ~ id
    is-section-fiber-fiber-map-coproduct-inl .(f a') (inl a' , refl) = refl
    is-section-fiber-fiber-map-coproduct-inl x (inr b' , p) =
      ex-falso (is-empty-eq-coproduct-inr-inl (g b') x p)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inl :
      (x : A) →
      fiber-fiber-map-coproduct-inl x ∘ fiber-map-coproduct-inl-fiber x ~ id
    is-retraction-fiber-fiber-map-coproduct-inl .(f a') (a' , refl) = refl

  abstract
    is-equiv-fiber-map-coproduct-inl-fiber :
      (x : A) → is-equiv (fiber-map-coproduct-inl-fiber x)
    is-equiv-fiber-map-coproduct-inl-fiber x =
      is-equiv-is-invertible
        ( fiber-fiber-map-coproduct-inl x)
        ( is-section-fiber-fiber-map-coproduct-inl x)
        ( is-retraction-fiber-fiber-map-coproduct-inl x)

  compute-fiber-inl-map-coproduct :
    (x : A) → fiber f x ≃ fiber (map-coproduct f g) (inl x)
  compute-fiber-inl-map-coproduct x =
    ( fiber-map-coproduct-inl-fiber x ,
      is-equiv-fiber-map-coproduct-inl-fiber x)

  fiber-map-coproduct-inr-fiber :
    (y : B) → fiber g y → fiber (map-coproduct f g) (inr y)
  pr1 (fiber-map-coproduct-inr-fiber y (b' , p)) = inr b'
  pr2 (fiber-map-coproduct-inr-fiber y (b' , p)) = ap inr p

  fiber-fiber-map-coproduct-inr :
    (y : B) → fiber (map-coproduct f g) (inr y) → fiber g y
  fiber-fiber-map-coproduct-inr y (inl a' , p) =
    ex-falso (is-empty-eq-coproduct-inl-inr (f a') y p)
  pr1 (fiber-fiber-map-coproduct-inr y (inr b' , p)) = b'
  pr2 (fiber-fiber-map-coproduct-inr y (inr b' , p)) =
    map-compute-eq-coproduct-inr-inr (g b') y p

  abstract
    is-section-fiber-fiber-map-coproduct-inr :
      (y : B) →
      (fiber-map-coproduct-inr-fiber y ∘ fiber-fiber-map-coproduct-inr y) ~ id
    is-section-fiber-fiber-map-coproduct-inr .(g b') (inr b' , refl) = refl
    is-section-fiber-fiber-map-coproduct-inr y (inl a' , p) =
      ex-falso (is-empty-eq-coproduct-inl-inr (f a') y p)

  abstract
    is-retraction-fiber-fiber-map-coproduct-inr :
      (y : B) →
      (fiber-fiber-map-coproduct-inr y ∘ fiber-map-coproduct-inr-fiber y) ~ id
    is-retraction-fiber-fiber-map-coproduct-inr .(g b') (b' , refl) = refl

  abstract
    is-equiv-fiber-map-coproduct-inr-fiber :
      (y : B) → is-equiv (fiber-map-coproduct-inr-fiber y)
    is-equiv-fiber-map-coproduct-inr-fiber y =
      is-equiv-is-invertible
        ( fiber-fiber-map-coproduct-inr y)
        ( is-section-fiber-fiber-map-coproduct-inr y)
        ( is-retraction-fiber-fiber-map-coproduct-inr y)

  compute-fiber-inr-map-coproduct :
    (y : B) → fiber g y ≃ fiber (map-coproduct f g) (inr y)
  compute-fiber-inr-map-coproduct y =
    ( fiber-map-coproduct-inr-fiber y ,
      is-equiv-fiber-map-coproduct-inr-fiber y)
```

### The functorial action of coproducts preserves retractions

```agda
module _
  {l1 l2 l1' l2' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f : A → B} {f' : A' → B'} (r : retraction f) (r' : retraction f')
  where

  map-retraction-map-coproduct : B + B' → A + A'
  map-retraction-map-coproduct =
    map-coproduct (map-retraction f r) (map-retraction f' r')

  is-retraction-retraction-map-coproduct :
    is-retraction (map-coproduct f f') map-retraction-map-coproduct
  is-retraction-retraction-map-coproduct =
    ( inv-htpy
      ( preserves-comp-map-coproduct
        ( f)
        ( map-retraction f r)
        ( f')
        ( map-retraction f' r'))) ∙h
    ( htpy-map-coproduct
      ( is-retraction-map-retraction f r)
      ( is-retraction-map-retraction f' r')) ∙h
    ( id-map-coproduct A A')

  retraction-map-coproduct : retraction (map-coproduct f f')
  retraction-map-coproduct =
    ( map-retraction-map-coproduct , is-retraction-retraction-map-coproduct)
```

### Functoriality of coproducts preserves embeddings

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

abstract
  is-emb-map-coproduct :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-emb f → is-emb g → is-emb (map-coproduct f g)
  is-emb-map-coproduct {f = f} {g} F G (inl x) (inl y) =
    is-equiv-left-is-equiv-right-square
      ( ap (map-coproduct f g))
      ( ap f)
      ( map-compute-eq-coproduct-inl-inl x y)
      ( map-compute-eq-coproduct-inl-inl (f x) (f y))
      ( λ where refl → refl)
      ( is-equiv-map-compute-eq-coproduct-inl-inl x y)
      ( is-equiv-map-compute-eq-coproduct-inl-inl (f x) (f y))
      ( F x y)
  is-emb-map-coproduct {f = f} {g} F G (inl x) (inr y) =
    is-equiv-is-empty
      ( ap (map-coproduct f g))
      ( is-empty-eq-coproduct-inl-inr (f x) (g y))
  is-emb-map-coproduct {f = f} {g} F G (inr x) (inl y) =
    is-equiv-is-empty
      ( ap (map-coproduct f g))
      ( is-empty-eq-coproduct-inr-inl (g x) (f y))
  is-emb-map-coproduct {f = f} {g} F G (inr x) (inr y) =
    is-equiv-left-is-equiv-right-square
      ( ap (map-coproduct f g))
      ( ap g)
      ( map-compute-eq-coproduct-inr-inr x y)
      ( map-compute-eq-coproduct-inr-inr (g x) (g y))
      ( λ where refl → refl)
      ( is-equiv-map-compute-eq-coproduct-inr-inr x y)
      ( is-equiv-map-compute-eq-coproduct-inr-inr (g x) (g y))
      ( G x y)
```
