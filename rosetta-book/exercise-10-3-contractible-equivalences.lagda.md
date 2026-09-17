# Exercise 10.3

```agda
module exercise-10-3-contractible-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-2-contractible-retracts
```

## Problem statement

### Exercise 10.3(a)

Show that for any type `A`, the map `const_⋆ : A → unit` is an equivalence if and only if `A` is contractible.

### Exercise 10.3(b)

Apply Exercise 9.4 to show that for any map `f : A → B`, if any two of the three assertions

1. `A` is contractible

2. `B` is contractible

3. `f` is an equivalence

hold, then so does the third.

## Solutions

### Exercise 10.3(a)

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-terminal-map-is-contr : is-contr A → is-equiv (terminal-map A)
  is-equiv-terminal-map-is-contr H =
    is-equiv-is-invertible (λ _ → center H) (λ _ → refl) (contraction H)

  equiv-unit-is-contr : is-contr A → A ≃ unit
  equiv-unit-is-contr H = terminal-map A , is-equiv-terminal-map-is-contr H

  is-contr-retraction-terminal-map : retraction (terminal-map A) → is-contr A
  is-contr-retraction-terminal-map (h , H) = h star , H

  is-contr-is-equiv-terminal-map : is-equiv (terminal-map A) → is-contr A
  is-contr-is-equiv-terminal-map H =
    is-contr-retraction-terminal-map (retraction-is-equiv H)

  is-contr-equiv-unit : A ≃ unit → is-contr A
  is-contr-equiv-unit e = (map-inv-equiv e star , is-retraction-map-inv-equiv e)

  is-contr-equiv-unit' : unit ≃ A → is-contr A
  is-contr-equiv-unit' e = (map-equiv e star , is-section-map-inv-equiv e)
```

### Exercise 10.3(b)

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
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
  {l1 l2 : Level} (A : UU l1) {B : UU l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f H =
      is-contr-is-equiv A
        ( map-inv-is-equiv H)
        ( is-equiv-map-inv-is-equiv H)

  abstract
    is-contr-equiv' :
      (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (e , H) = is-contr-is-equiv' e H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
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
