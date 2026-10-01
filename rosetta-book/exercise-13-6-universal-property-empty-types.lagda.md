# Exercise 13.6

```agda
module exercise-13-6-universal-property-empty-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import exercise-10-3-contractible-equivalences
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is empty.

2. The type `Π(x : A) P(x)` is contractible for any family `P` of types over `A`.
This property is the **dependent universal property of an empty type**.

3. The type `A → X` is contractible for any type `X`.
This property is the **universal property of an empty type**.

## Solution

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty l =
    (P : A → UU l) → is-contr ((x : A) → P x)

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty l = (X : UU l) → is-contr (A → X)

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty dup-empty X =
    dup-empty (λ _ → X)

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty up-empty = center (up-empty empty)

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  pr1 (dependent-universal-property-empty-is-empty {l} H P) x = ex-falso (H x)
  pr2 (dependent-universal-property-empty-is-empty {l} H P) f =
    eq-htpy (λ x → ex-falso (H x))

  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty {l} H =
    universal-property-dependent-universal-property-empty
      ( dependent-universal-property-empty-is-empty H)

abstract
  dependent-universal-property-empty' :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  pr1 (dependent-universal-property-empty' P) = ind-empty {P = P}
  pr2 (dependent-universal-property-empty' P) f = eq-htpy ind-empty

abstract
  universal-property-empty' :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty' X =
    dependent-universal-property-empty' (λ _ → X)

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) →
    ({l' : Level} (X : UU l') → is-contr (Y → X)) →
    is-equiv (ind-empty {P = λ _ → Y})
  uniqueness-empty Y H =
    is-equiv-is-equiv-precomp ind-empty
      ( λ X →
        is-equiv-is-contr
          ( λ g → g ∘ ind-empty)
          ( H X)
          ( universal-property-empty' X))

abstract
  universal-property-empty-is-equiv-ind-empty :
    {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ _ → X}) →
    ((l' : Level) (Y : UU l') → is-contr (X → Y))
  universal-property-empty-is-equiv-ind-empty X is-equiv-ind-empty l' Y =
    is-contr-is-equiv
      ( empty → Y)
      ( λ f → f ∘ ind-empty)
      ( is-equiv-precomp-is-equiv ind-empty is-equiv-ind-empty Y)
      ( universal-property-empty' Y)
```
