# Exercise 10.3

```agda
module exercise-10-3-contractible-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import exercise-10-2-contractible-retracts
```

## Problem statement

<div class="subexenum">

Show that for any type `A`, the map `const_⋆ : A→ unit` is an equivalence if and only if `A` is contractible.

Apply Exercise 9.4 to show that for any map `f:A→ B`, if any two of the three assertions

1.  `A` is contractible

2.  `B` is contractible

3.  `f` is an equivalence

hold, then so does the third.

</div>

## Solution

<!-- rosetta-item: exercise-10-3 -->

<!-- rosetta-agda-block: exercise-10-3-contractibility-equivalences -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : Type l2)
  where

  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv f H =
      is-contr-retract-of B (f , retraction-is-equiv H)

  abstract
    is-contr-equiv :
      A ≃ B → is-contr B → is-contr A
    is-contr-equiv (e , H) =
      is-contr-is-equiv e H

module _
  {l1 l2 : Level} (A : Type l1) {B : Type l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f H =
      is-contr-is-equiv A
        ( map-section-is-equiv H)
        ( is-equiv-map-section-is-equiv H)

  abstract
    is-contr-equiv' :
      (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (e , H) = is-contr-is-equiv' e H

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr f H K =
      is-equiv-is-invertible
        ( λ y → center H)
        ( λ y → eq-is-contr K)
        ( contraction H)

  equiv-is-contr :
    is-contr A → is-contr B → A ≃ B
  pr1 (equiv-is-contr H K) a =
    center K
  pr2 (equiv-is-contr H K) =
    is-equiv-is-contr _ H K
```
