# Exercise 10.2

```agda
module exercise-10-2-contractible-retracts where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
```

## Problem statement

Suppose that `A` is a retract of `B`.
Show that
```text
is-contr(B)→is-contr(A).
```

## Solution

<!-- rosetta-item: exercise-10-2 -->

<!-- rosetta-agda-block: exercise-10-2-contractibility-retracts -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : Type l2)
  where

  abstract
    is-contr-retract-of : A retract-of B → is-contr B → is-contr A
    pr1 (is-contr-retract-of (pair i (pair r is-retraction-r)) H) = r (center H)
    pr2 (is-contr-retract-of (pair i (pair r is-retraction-r)) H) x =
      ap r (contraction H (i x)) ∙ (is-retraction-r x)
```
