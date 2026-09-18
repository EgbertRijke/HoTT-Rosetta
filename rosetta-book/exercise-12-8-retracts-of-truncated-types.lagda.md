# Exercise 12.8

```agda
module exercise-12-8-retracts-of-truncated-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
```

## Problem statement

### Exercise 12.8(a)

Consider a section-retraction pair

```text
      i        r
  A -----> B -----> A
```

with `H : r ∘ i ~ id`.
Show that `x = y` is a retract of `i(x) = i(y)`.

### Exercise 12.8(b)

Use Exercise 10.2 to show that if `A` is a retract of a `k`-type `B`, then `A` is also a `k`-type.

## Solutions

### Exercise 12.8(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  (r : B → A) (H : r ∘ i ~ id)
  where

  is-injective-has-retraction :
    {x y : A} → i x ＝ i y → x ＝ y
  is-injective-has-retraction {x} {y} p = inv (H x) ∙ (ap r p ∙ H y)

  is-retraction-is-injective-has-retraction :
    {x y : A} → is-injective-has-retraction ∘ ap i {x} {y} ~ id
  is-retraction-is-injective-has-retraction {x} refl = left-inv (H x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B) (R : retraction i)
  where

  is-injective-retraction :
    {x y : A} → i x ＝ i y → x ＝ y
  is-injective-retraction =
    is-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  is-retraction-is-injective-retraction :
    {x y : A} → is-injective-retraction ∘ ap i {x} {y} ~ id
  is-retraction-is-injective-retraction =
    is-retraction-is-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  retraction-ap : {x y : A} → retraction (ap i {x} {y})
  pr1 retraction-ap = is-injective-retraction
  pr2 retraction-ap = is-retraction-is-injective-retraction

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) (x y : A)
  where

  retract-eq :
    (x ＝ y) retract-of (pr1 R x ＝ pr1 R y)
  pr1 retract-eq = ap (pr1 R)
  pr2 retract-eq = retraction-ap (pr1 R) (pr2 R)
```

### Exercise 12.8(b)

The solution of this exercise already appears in our implentation of the proof of Proposition 12.4.5 in [section-12-4-general-truncation-levels].

## Supplements

### Equivalences are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
  is-injective-is-equiv {f} H =
    is-injective-retraction f (retraction-is-equiv H)

  is-injective-equiv : (e : A ≃ B) → is-injective (map-equiv e)
  is-injective-equiv e = is-injective-is-equiv (is-equiv-map-equiv e)
```
