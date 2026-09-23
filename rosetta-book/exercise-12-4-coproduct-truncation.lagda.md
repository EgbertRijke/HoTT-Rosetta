# Exercise 12.4

```agda
module exercise-12-4-coproduct-truncation where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-3-order-natural-numbers
open import section-7-3-the-standard-finite-types
open import exercise-7-3-divisibility-factorials
open import exercise-7-5-observational-equality-finite-types
open import section-8-1-decidability-and-decidable-equality
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import exercise-10-1-identity-types-contractible
open import section-11-5-disjointness-of-coproducts
open import section-12-1-propositions
open import section-12-3-sets
open import section-12-4-general-truncation-levels
```

## Problem statement

### Exercise 12.4(a)

Show that for any two contractible types `A` and `B`, the coproduct `A + B` is not contractible.

### Exercise 12.4(b)

Show that for any two propositions `P` and `Q`, we have a logical equivalence

```text
  is-contr(P + Q) ↔ P ⊕ Q,
```

where the **exclusive disjunction** `P ⊕ Q` is defined by

```text
  P ⊕ Q ≔ (P × ¬ Q) + (Q × ¬ P).
```

### Exercise 12.4(c)

Show that for any two propositions `P` and `Q`, the coproduct `P + Q` is a proposition if and only if `P → ¬ Q`.

### Exercise 12.4(d)

Show that for any two `(k + 2)`-types `A` and `B`, the coproduct `A + B` is again a `(k + 2)`-type.
Conclude that `ℤ` is a set.

## Solution

### Exercise 12.4(a)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  noncontractibility-coproduct-is-contr' :
    is-contr A → is-contr B → noncontractibility' (A + B) 1
  noncontractibility-coproduct-is-contr' HA HB =
    inl (center HA) , inr (center HB) , neq-inl-inr

  abstract
    is-not-contractible-coproduct-is-contr :
      is-contr A → is-contr B → is-not-contractible (A + B)
    is-not-contractible-coproduct-is-contr HA HB =
      is-not-contractible-noncontractibility
        ( 1 , noncontractibility-coproduct-is-contr' HA HB)
```

### Exercise 12.4(b)

BENCHMARK PROBLEM

### Exercise 12.4(c)

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coproduct :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (P + Q)
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inl p) (inl p') =
      ap inl (is-prop-P p p')
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inr q) (inr q') =
      ap inr (is-prop-Q q q')

  abstract
    is-prop-coproduct : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (P + Q)
    is-prop-coproduct f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coproduct f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

coproduct-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P → ¬ (type-Prop Q)) → Prop (l1 ⊔ l2)
pr1 (coproduct-Prop P Q H) =
  type-Prop P + type-Prop Q
pr2 (coproduct-Prop P Q H) =
  is-prop-coproduct H (is-prop-type-Prop P) (is-prop-type-Prop Q)
```

### Exercise 12.4(d)

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-coproduct :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (A + B)
    is-trunc-coproduct is-trunc-A is-trunc-B (inl x) (inl y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coproduct-inl-inl x y)
        ( is-trunc-A x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inl x) (inr y) =
      is-trunc-is-empty k (is-empty-eq-coproduct-inl-inr x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inr x) (inl y) =
      is-trunc-is-empty k (is-empty-eq-coproduct-inr-inl x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inr x) (inr y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coproduct-inr-inr x y)
        ( is-trunc-B x y)

abstract
  is-set-coproduct :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A + B)
  is-set-coproduct = is-trunc-coproduct neg-two-𝕋

coproduct-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
pr1 (coproduct-Set (A , is-set-A) (B , is-set-B)) = A + B
pr2 (coproduct-Set (A , is-set-A) (B , is-set-B)) =
  is-set-coproduct is-set-A is-set-B
```

## Supplement

### Propositional case distinctions about inequalities of natural numbers

```agda
is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

is-prop-leq-succ-cases :
  (m n : ℕ) → is-prop ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
is-prop-leq-succ-cases m n =
  is-prop-coproduct
    ( λ q α →
      contradiction-leq-ℕ n n (refl-leq-ℕ n)
        ( concatenate-eq-leq-ℕ n (inv α) q))
    ( is-prop-leq-ℕ m n)
    ( is-set-ℕ m (succ-ℕ n))

equiv-leq-succ-cases :
  (m n : ℕ) → (m ≤-ℕ succ-ℕ n) ≃ ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
equiv-leq-succ-cases m n =
  equiv-iff-is-prop
    ( is-prop-leq-ℕ m (succ-ℕ n))
    ( is-prop-leq-succ-cases m n)
    ( decide-leq-succ-ℕ m n)
    ( rec-coproduct
      ( preserves-leq-succ-ℕ m n)
      ( leq-eq-ℕ m (succ-ℕ n)))

eq-cases-leq-succ :
  (m n : ℕ) (p : m ≤-ℕ succ-ℕ n) (x : (m ≤-ℕ n) + (m ＝ succ-ℕ n)) →
  decide-leq-succ-ℕ m n p ＝ x
eq-cases-leq-succ m n p x =
  eq-is-prop' (is-prop-leq-succ-cases m n) (decide-leq-succ-ℕ m n p) x
```

### The unit type is a set

```agda
abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : Set lzero
unit-Set = unit , is-set-unit
```

### The standard finite types are sets

The following code is not copied verbatim from agda-unimath. In agda-unimath, the standard finite types are defined as sets, whereas in this book the topic of sets is introduced much later than the standard finite types.

```agda
is-set-Fin : (n : ℕ) → is-set (Fin n)
is-set-Fin zero-ℕ = is-set-empty
is-set-Fin (succ-ℕ n) = is-set-coproduct (is-set-Fin n) is-set-unit

Fin-Set : (n : ℕ) → Set lzero
pr1 (Fin-Set n) = Fin n
pr2 (Fin-Set n) = is-set-Fin n

is-prop-Eq-Fin : (k : ℕ) → (x : Fin k) → (y : Fin k) → is-prop (Eq-Fin k x y)
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-prop-Eq-Fin k x y
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-prop-empty
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-prop-empty
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-prop-unit

extensionality-Fin :
  (k : ℕ)
  (x y : Fin k) →
  (x ＝ y) ≃ (Eq-Fin k x y)
pr1 (extensionality-Fin k x y) = Eq-Fin-eq k
pr2 (extensionality-Fin k x y) =
  is-equiv-has-converse-is-prop
    ( is-set-Fin k x y)
    ( is-prop-Eq-Fin k x y)
    ( eq-Eq-Fin k)

Fin-Discrete-Type : ℕ → Discrete-Type lzero
pr1 (Fin-Discrete-Type k) = Fin k
pr2 (Fin-Discrete-Type k) = has-decidable-equality-Fin k
```
