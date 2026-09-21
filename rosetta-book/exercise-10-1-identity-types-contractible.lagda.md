# Exercise 10.1

```agda
module exercise-10-1-identity-types-contractible where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-10-1-contractible-types
```

## Problem statement

Show that if `A` is contractible, then for any `x, y : A` the identity type `x = y` is also contractible.

## Solution

```agda
is-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → is-contr (x ＝ y)
pr1 (is-prop-is-contr H x y) = eq-is-contr H
pr2 (is-prop-is-contr H x .x) refl = left-inv (pr2 H x)
```

## Supplement

### Noncontractible types are not contractible

```agda
is-not-contractible-noncontractibility :
  {l : Level} {X : UU l} → noncontractibility X → is-not-contractible X
is-not-contractible-noncontractibility (zero-ℕ , H) =
  is-not-contractible-is-empty H
is-not-contractible-noncontractibility (succ-ℕ n , x , y , H) C =
  is-not-contractible-noncontractibility (n , H) (is-prop-is-contr C x y)
```
