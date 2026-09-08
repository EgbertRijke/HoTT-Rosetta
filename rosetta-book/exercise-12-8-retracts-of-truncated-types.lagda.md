# Exercise 12.8

```agda
module exercise-12-8-retracts-of-truncated-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
```

## Problem statement

<div class="subexenum">

Consider a section-retraction pair
<!-- rosetta-diagram: af030234c6b2; review: pending -->

*Linear diagram (automatic draft).*

```text
 [A] ----> [B] ----> [A]

Arrows:
- A --i--> B
- B --r--> A
```
with `H:r∘ i~ id`.
Show that `x = y` is a retract of `i(x) = i(y)`.

Use Exercise 10.2 to show that if `A` is a retract of a `k`-type `B`, then `A` is also a `k`-type.

</div>

## Solution

<!-- rosetta-item: exercise-12-8 -->

### Part (a): identity types of a retract

<!-- rosetta-agda-block: exercise-12-8-retraction-on-identities -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (i : A → B)
  (r : B → A) (H : r ∘ i ~ id)
  where

  is-injective-has-retraction :
    {x y : A} → i x ＝ i y → x ＝ y
  is-injective-has-retraction {x} {y} p = inv (H x) ∙ (ap r p ∙ H y)

  is-retraction-is-injective-has-retraction :
    {x y : A} → is-injective-has-retraction ∘ ap i {x} {y} ~ id
  is-retraction-is-injective-has-retraction {x} refl = left-inv (H x)

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (i : A → B) (R : retraction i)
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
```

<!-- rosetta-agda-block: exercise-12-8-identity-retract -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (R : A retract-of B) (x y : A)
  where

  retract-eq :
    (x ＝ y) retract-of (pr1 R x ＝ pr1 R y)
  pr1 retract-eq = ap (pr1 R)
  pr2 retract-eq = retraction-ap (pr1 R) (pr2 R)
```
