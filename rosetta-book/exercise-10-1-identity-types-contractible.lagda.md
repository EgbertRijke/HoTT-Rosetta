# Exercise 10.1

```agda
module exercise-10-1-identity-types-contractible where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-10-1-contractible-types
```

## Problem statement

Show that if `A` is contractible, then for any `x,y:A` the identity type `x=y` is also contractible.

## Solution

<!-- rosetta-item: exercise-10-1 -->

<!-- rosetta-agda-block: exercise-10-1-contractible-identities -->

```agda
is-prop-is-contr :
  {l : Level} {A : Type l} → is-contr A → (x y : A) → is-contr (x ＝ y)
pr1 (is-prop-is-contr H x y) = eq-is-contr H
pr2 (is-prop-is-contr H x .x) refl = left-inv (pr2 H x)
```
