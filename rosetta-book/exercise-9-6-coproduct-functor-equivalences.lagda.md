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
open import section-10-4-equivalences-are-contractible-maps
```

## Problem statement

Recall from Remark 4.4.2 that coproducts have a **functorial action**, i.e., that for every `f : A → A'` and every `g : B → B'` we have a map

```text
  f + g : (A + B) → (A' + B').
```

### Exercise 9.6(a)

Show that `id_A + id_B ~ id_{A + B}`.

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
