# Exercise 12.4

```agda
module exercise-12-4-coproduct-truncation where

open import universe-levels
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-4-3-negation
open import section-12-1-propositions
```

## Problem statement

<div class="subexenum">

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

</div>

## Solution

<!-- rosetta-item: exercise-12-4 -->

### Part (c): mutually exclusive propositions have propositional coproduct

<!-- rosetta-agda-block: exercise-12-4-exclusive-propositions -->

```agda
module _
  {l1 l2 : Level} {P : Type l1} {Q : Type l2}
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
