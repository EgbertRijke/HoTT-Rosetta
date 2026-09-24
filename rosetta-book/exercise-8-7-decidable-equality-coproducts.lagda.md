# Exercise 8.7

```agda
module exercise-8-7-decidable-equality-coproducts where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-7-group-laws-integers
open import section-6-3-observational-equality-of-the-natural-numbers
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-7-3-the-standard-finite-types
open import section-8-1-decidability-and-decidable-equality
open import section-12-1-propositions
```

## Problem statement

Consider two types `A` and `B`, and consider the observational equality `Eq-coproduct` on the coproduct `A + B` defined by

```text
  Eq-coproduct(inl(x),inl(x')) ≔ x = x'
  Eq-coproduct(inl(x),inr(y')) ≔ ∅
  Eq-coproduct(inr(y),inl(x')) ≔ ∅
  Eq-coproduct(inr(y),inr(y')) ≔ y = y'.
```

Note: Agda-unimath's definition of `Eq-coproduct` is as a data-type.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coproduct : A + B → A + B → UU (l1 ⊔ l2)
    where
    Eq-eq-coproduct-inl : {x y : A} → x ＝ y → Eq-coproduct (inl x) (inl y)
    Eq-eq-coproduct-inr : {x y : B} → x ＝ y → Eq-coproduct (inr x) (inr y)
```

### Exercise 8.7(a)

Show that `(x = y) ↔ Eq-coproduct(x,y)` for every `x, y : A + B`.

### Exercise 8.7(b)

Show that the following are equivalent:

1. Both `A` and `B` have decidable equality.

2. The coproduct `A + B` has decidable equality.

Conclude that `ℤ` has decidable equality.

## Solutions

### Exercise 8.7(a)

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

### Exercise 8.7(b)

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

Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl y) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

refl-Eq-ℤ : (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-eq-ℤ : {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = refl-Eq-ℤ x

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → x ＝ y
eq-Eq-ℤ (inl x) (inl y) e = ap inl (eq-Eq-ℕ x y e)
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = refl
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = ap (inr ∘ inr) (eq-Eq-ℕ x y e)

has-decidable-equality-unit : has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coproduct
    has-decidable-equality-ℕ
    ( has-decidable-equality-coproduct
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = has-decidable-equality-ℤ x one-ℤ

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = has-decidable-equality-ℤ x neg-one-ℤ

ℤ-Discrete-Type : Discrete-Type lzero
pr1 ℤ-Discrete-Type = ℤ
pr2 ℤ-Discrete-Type = has-decidable-equality-ℤ
```

## Supplement

### The predicates of being on the left and on the right

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-left-Prop : X + Y → Prop lzero
  is-left-Prop (inl x) = unit-Prop
  is-left-Prop (inr x) = empty-Prop

  is-left : X + Y → UU lzero
  is-left x = type-Prop (is-left-Prop x)

  is-prop-is-left : (x : X + Y) → is-prop (is-left x)
  is-prop-is-left x = is-prop-type-Prop (is-left-Prop x)

  is-right-Prop : X + Y → Prop lzero
  is-right-Prop (inl x) = empty-Prop
  is-right-Prop (inr x) = unit-Prop

  is-right : X + Y → UU lzero
  is-right x = type-Prop (is-right-Prop x)

  is-prop-is-right : (x : X + Y) → is-prop (is-right x)
  is-prop-is-right x = is-prop-type-Prop (is-right-Prop x)

  is-left-or-is-right : (x : X + Y) → is-left x + is-right x
  is-left-or-is-right (inl x) = inl star
  is-left-or-is-right (inr x) = inr star

  left-is-left : (x : X + Y) → is-left x → X
  left-is-left (inl x) _ = x

  right-is-right : (x : X + Y) → is-right x → Y
  right-is-right (inr y) _ = y
```
