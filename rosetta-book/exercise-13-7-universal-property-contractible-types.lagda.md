# Exercise 13.7

```agda
module exercise-13-7-universal-property-contractible-types where

open import universe-levels

open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import exercise-2-3-constant-maps
open import section-4-6-dependent-pair-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-13-1-equivalent-forms-of-function-extensionality
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is contractible.

2. The type `A` comes equipped with a point `a : A`, and the map

   ```text
     (Π(x : A) P(x)) → P(a)
   ```

   given by `f ↦ f(a)` is an equivalence for any type family `P` over `A`. This property is the **dependent universal property of a contractible type**.

3. The type `A` comes equipped with a point `a : A`, and the map

   ```text
     (A → X) → X
   ```

   given by `f ↦ f(a)` is an equivalence for any type `X`. This property is the **universal property of a contractible type**.

4. The type `A` comes equipped with a point `a : A`, and the map

   ```text
     (A → A) → A
   ```

   given by `f ↦ f(a)` is an equivalence.

5. The map

   ```text
     X → (A → X)
   ```

   given by `x ↦ λ y. x` is an equivalence for any type `X`.

6. The map

   ```text
     A → (A → A)
   ```

   given by `x ↦ λ y. x` is an equivalence.

## Solution

PARTIAL BENCHMARK PROBLEM

### The diagonal of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-equiv (diagonal-exponential A A)
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H = H A

  abstract
    is-contr-is-equiv-self-diagonal-exponential :
      is-equiv (diagonal-exponential A A) → is-contr A
    is-contr-is-equiv-self-diagonal-exponential H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential H =
      is-contr-is-equiv-self-diagonal-exponential
        ( is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H)

  abstract
    is-equiv-diagonal-exponential-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)
    is-equiv-diagonal-exponential-is-contr H X =
      is-equiv-is-invertible
        ( ev (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( refl-htpy)

  equiv-diagonal-exponential-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-exponential-is-contr X H) =
    diagonal-exponential X A
  pr2 (equiv-diagonal-exponential-is-contr X H) =
    is-equiv-diagonal-exponential-is-contr H X

  abstract
    is-equiv-diagonal-exponential-is-contr' :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)
    is-equiv-diagonal-exponential-is-contr' H X =
      is-equiv-is-invertible
        ( λ _ → center H)
        ( λ x → eq-htpy (contraction H ∘ x))
        ( contraction H)

  equiv-diagonal-exponential-is-contr' :
    {l : Level} (X : UU l) → is-contr A → A ≃ (X → A)
  equiv-diagonal-exponential-is-contr' X H =
    ( diagonal-exponential A X , is-equiv-diagonal-exponential-is-contr' H X)

  abstract
    is-contr-is-equiv-diagonal-exponential' :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential' H =
      is-contr-is-equiv-self-diagonal-exponential (H A)
```
