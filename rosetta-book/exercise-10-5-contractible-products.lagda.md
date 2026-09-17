# Exercise 10.5

```agda
module exercise-10-5-contractible-products where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-9-1-homotopies
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-1-contractible-types
open import exercise-10-2-contractible-retracts
```

## Problem statement

Show that for any two types `A` and `B`, the following are equivalent:

1. Both `A` and `B` are contractible.

2. The type `A × B` is contractible.

## Solution

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-left-factor-product : is-contr (A × B) → is-contr A
    is-contr-left-factor-product H =
      is-contr-retract-of
        ( A × B)
        ( ( λ x → (x , (pr2 (center H)))) , ( pr1 , refl-htpy))
        ( H)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-contr-right-factor-product : is-contr (A × B) → is-contr B
    is-contr-right-factor-product H =
      is-contr-retract-of
        ( A × B)
        ( (pair (pr1 (center H))) , (pr2 , refl-htpy))
        ( H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-product : is-contr A → is-contr B → is-contr (A × B)
    pr1 (pr1 (is-contr-product (a , C) (b , D))) = a
    pr2 (pr1 (is-contr-product (a , C) (b , D))) = b
    pr2 (is-contr-product (a , C) (b , D)) (x , y) = eq-pair (C x) (D y)
```
