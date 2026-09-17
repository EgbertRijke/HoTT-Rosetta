# Exercise 12.4

```agda
module exercise-12-4-coproduct-truncation where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-3-order-natural-numbers
open import exercise-7-3-divisibility-factorials
open import section-9-2-bi-invertible-maps
open import section-12-1-propositions
open import section-12-3-sets
open import exercise-12-3-injective-maps-into-sets
```

## Problem statement

Show that for any two contractible types `A` and `B`, the coproduct `A+B` is not contractible.

Show that for any two propositions `P` and `Q`, we have a logical equivalence
```text
is-contr(P+Q)↔ P\oplus Q,
```
where the **exclusive disjunction** `P\oplus Q` is defined by
```text
P\oplus Q:= (P×¬ Q)+(Q×¬ P).
```

Show that for any two propositions `P` and `Q`, the coproduct `P+Q` is a proposition if and only if `P→ ¬ Q`.

Show that for any two `(k+2)`-types `A` and `B`, the coproduct `A+B` is again a `(k+2)`-type.
Conclude that `ℤ` is a set.

## Solution

### Part (c): mutually exclusive propositions have propositional coproduct

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
```

## Supplement

```agda
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
