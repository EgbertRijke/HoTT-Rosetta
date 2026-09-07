# Exercise 10.7

```agda
module exercise-10-7-fibers-of-projections where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-4-transport
open import section-9-2-bi-invertible-maps
open import section-10-3-contractible-maps
```

## Problem statement

Let `B` be a family of types over `A`, and consider the projection map
```text
pr 1 : (Σ(x:A) B(x))→ A.
```

<div class="subexenum">

Show that for any `a:A`, the map
```text
λ ((x,y),p). tr_B(p,y) : fib(pr 1, a) → B(a),
```
is an equivalence.

Show that the following are equivalent:

1.  The projection map `pr 1` is an equivalence.

2.  The type `B(x)` is contractible for each `x:A`.

Consider a dependent function `b:Π(x:A) B(x)`.
Show that the following are equivalent:

1.  The map
```text
λ x. (x,b(x)) : A → Σ(x:A) B(x)
```
    is an equivalence.

2.  The type `B(x)` is contractible for each `x:A`.

</div>

## Solution

<!-- rosetta-item: exercise-10-7 -->

<!-- rosetta-agda-block: exercise-10-7-projection-fiber-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) (a : A)
  where

  map-fiber-pr1 : fiber (pr1 {B = B}) a → B a
  map-fiber-pr1 ((x , y) , p) = tr B p y

  map-inv-fiber-pr1 : B a → fiber (pr1 {B = B}) a
  map-inv-fiber-pr1 b = (a , b) , refl

  is-section-map-inv-fiber-pr1 :
    is-section map-fiber-pr1 map-inv-fiber-pr1
  is-section-map-inv-fiber-pr1 b = refl

  is-retraction-map-inv-fiber-pr1 :
    is-retraction map-fiber-pr1 map-inv-fiber-pr1
  is-retraction-map-inv-fiber-pr1 ((.a , y) , refl) = refl

  abstract
    is-equiv-map-fiber-pr1 : is-equiv map-fiber-pr1
    is-equiv-map-fiber-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1
        is-retraction-map-inv-fiber-pr1

  equiv-fiber-pr1 : fiber (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-pr1 = map-fiber-pr1
  pr2 equiv-fiber-pr1 = is-equiv-map-fiber-pr1

  abstract
    is-equiv-map-inv-fiber-pr1 : is-equiv map-inv-fiber-pr1
    is-equiv-map-inv-fiber-pr1 =
      is-equiv-is-invertible
        map-fiber-pr1
        is-retraction-map-inv-fiber-pr1
        is-section-map-inv-fiber-pr1

  inv-equiv-fiber-pr1 : B a ≃ fiber (pr1 {B = B}) a
  pr1 inv-equiv-fiber-pr1 = map-inv-fiber-pr1
  pr2 inv-equiv-fiber-pr1 = is-equiv-map-inv-fiber-pr1
```
