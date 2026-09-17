# Exercise 8.7

```agda
module exercise-8-7-decidable-equality-coproducts where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-8-1-decidability-and-decidable-equality
```

## Problem statement

Consider two types `A` and `B`, and consider the observational equality `Eq-coproduct` on the coproduct `A+B` defined by
```text
Eq-coproduct(inl(x),inl(x')) ≔ x= x' Eq-coproduct(inl(x),inr(y')) ≔ empty
Eq-coproduct(inr(y),inl(x')) ≔ empty Eq-coproduct(inr(y),inr(y')) ≔ y = y'.
```

<div class="subexenum">

Show that `(x=y)↔Eq-coproduct(x,y)` for every `x,y:A+B`.

Show that the following are equivalent:

1.  Both `A` and `B` have decidable equality.

2.  The coproduct `A+B` has decidable equality.

Conclude that `ℤ` has decidable equality.

</div>

## Solution

<!-- rosetta-item: exercise-8-7 -->

<!-- rosetta-agda-block: exercise-8-7-injective-map -->

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = {x y : A} → f x ＝ f y → x ＝ y
```

<!-- rosetta-agda-block: exercise-8-7-negated-equality -->

```agda
nonequal : {l : Level} {A : UU l} → A → A → UU l
nonequal x y = ¬ (x ＝ y)

infix 6 _≠_
_≠_ = nonequal
```

<!-- rosetta-agda-block: exercise-8-7-coproduct-injections -->

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = A + B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = A + B} inr
  is-injective-inr refl = refl

  neq-inl-inr : {x : A} {y : B} → inl x ≠ inr y
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → inr x ≠ inl y
  neq-inr-inl ()
```

<!-- rosetta-agda-block: exercise-8-7-observational-equality -->

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coproduct : A + B → A + B → UU (l1 ⊔ l2)
    where
    Eq-eq-coproduct-inl : {x y : A} → x ＝ y → Eq-coproduct (inl x) (inl y)
    Eq-eq-coproduct-inr : {x y : B} → x ＝ y → Eq-coproduct (inr x) (inr y)
```

<!-- rosetta-agda-block: exercise-8-7-observational-identity -->

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  refl-Eq-coproduct : (x : A + B) → Eq-coproduct x x
  refl-Eq-coproduct (inl x) = Eq-eq-coproduct-inl refl
  refl-Eq-coproduct (inr x) = Eq-eq-coproduct-inr refl

  Eq-eq-coproduct : (x y : A + B) → x ＝ y → Eq-coproduct x y
  Eq-eq-coproduct x .x refl = refl-Eq-coproduct x

  eq-Eq-coproduct : (x y : A + B) → Eq-coproduct x y → x ＝ y
  eq-Eq-coproduct .(inl x) .(inl x) (Eq-eq-coproduct-inl {x} {.x} refl) = refl
  eq-Eq-coproduct .(inr x) .(inr x) (Eq-eq-coproduct-inr {x} {.x} refl) = refl
```

<!-- rosetta-agda-block: exercise-8-7-decidable-coproduct -->

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-decidable-equality-coproduct :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A + B)
  has-decidable-equality-coproduct d e (inl x) (inl y) =
    is-decidable-iff (ap inl) is-injective-inl (d x y)
  has-decidable-equality-coproduct d e (inl x) (inr y) =
    inr neq-inl-inr
  has-decidable-equality-coproduct d e (inr x) (inl y) =
    inr neq-inr-inl
  has-decidable-equality-coproduct d e (inr x) (inr y) =
    is-decidable-iff (ap inr) is-injective-inr (e x y)

  has-decidable-equality-left-summand :
    has-decidable-equality (A + B) → has-decidable-equality A
  has-decidable-equality-left-summand d x y =
    is-decidable-iff is-injective-inl (ap inl) (d (inl x) (inl y))

  has-decidable-equality-right-summand :
    has-decidable-equality (A + B) → has-decidable-equality B
  has-decidable-equality-right-summand d x y =
    is-decidable-iff is-injective-inr (ap inr) (d (inr x) (inr y))
```
