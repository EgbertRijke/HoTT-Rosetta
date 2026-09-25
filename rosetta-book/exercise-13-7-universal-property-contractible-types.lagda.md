# Exercise 13.7

```agda
module exercise-13-7-universal-property-contractible-types where

open import universe-levels

open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import exercise-2-3-constant-maps
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-2-singleton-induction
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
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

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  dependent-universal-property-contr : UUω
  dependent-universal-property-contr =
    {l : Level} (P : A → UU l) → is-equiv (ev {B = P} a)

  universal-property-contr : UUω
  universal-property-contr = {l : Level} (X : UU l) → is-equiv (ev {B = λ _ → X} a)
```

### 13.7(ii) implies 13.7(iii)

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  universal-property-dependent-universal-property-contr :
    dependent-universal-property-contr a → universal-property-contr a
  universal-property-dependent-universal-property-contr dup-contr {l} X =
    dup-contr (λ _ → X)
```

13.7(iv) is a direct corollary of 13.7(iii) and is not formalized.

### 13.7(iv) implies 13.7(i) and 13.7(iii) implies 13.7(i)

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-contr-is-equiv-ev-point :
      is-equiv (ev {B = λ _ → A} a) → is-contr A
    pr1 (is-contr-is-equiv-ev-point H) = a
    pr2 (is-contr-is-equiv-ev-point H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( (λ _ → a) , refl)
            ( id , refl)))

  abstract
    is-contr-universal-property-contr :
      universal-property-contr a → is-contr A
    is-contr-universal-property-contr up-contr =
      is-contr-is-equiv-ev-point (up-contr A)
```

### 13.7(ii) implies 13.7(i)

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-contr-dependent-universal-property-contr :
      dependent-universal-property-contr a → is-contr A
    is-contr-dependent-universal-property-contr dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)
```

### 13.7(i) implies 13.7(ii)

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    dependent-universal-property-contr-is-contr :
      is-contr A → dependent-universal-property-contr a
    dependent-universal-property-contr-is-contr H P =
      is-equiv-is-invertible
        ( ind-singleton a H P)
        ( compute-ind-singleton a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton a H
              ( λ x → ind-singleton a H P (f a) x ＝ f x)
              ( compute-ind-singleton a H P (f a))))

  equiv-dependent-universal-property-contr :
    is-contr A → {l : Level} (B : A → UU l) → ((x : A) → B x) ≃ B a
  pr1 (equiv-dependent-universal-property-contr H P) = ev a
  pr2 (equiv-dependent-universal-property-contr H P) =
    dependent-universal-property-contr-is-contr H P

  apply-dependent-universal-property-contr :
    is-contr A → {l : Level} (B : A → UU l) → (B a → ((x : A) → B x))
  apply-dependent-universal-property-contr H P =
    map-inv-equiv (equiv-dependent-universal-property-contr H P)
```

### 13.7(i) implies 13.7(iii)

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    universal-property-contr-is-contr :
      is-contr A → universal-property-contr a
    universal-property-contr-is-contr H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr H X) = ev a
  pr2 (equiv-universal-property-contr H X) =
    universal-property-contr-is-contr H X

  apply-universal-property-contr :
    is-contr A → {l : Level} (X : UU l) → X → (A → X)
  apply-universal-property-contr H X =
    map-inv-equiv (equiv-universal-property-contr H X)
```

### 13.7(v) implies 13.7(vi)

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-equiv (diagonal-exponential A A)
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H = H A
```

### 13.7(vi) implies 13.7(i)

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-contr-is-equiv-self-diagonal-exponential :
      is-equiv (diagonal-exponential A A) → is-contr A
    is-contr-is-equiv-self-diagonal-exponential H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))
```

### 13.7(v) implies 13.7(i)

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-contr-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential H =
      is-contr-is-equiv-self-diagonal-exponential
        ( is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H)
```

### 13.7(i) implies 13.7(v)

```agda
module _
  {l1 : Level} {A : UU l1}
  where

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
```

## Supplement

### A type `A` is contractible if and only if `A → (X → A)` is an equivalence

```agda
module _
  {l1 : Level} {A : UU l1}
  where

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

### The universal property of the unit type

```agda
ev-star :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) → P star
ev-star P f = f star

ev-star' :
  {l : Level} (Y : UU l) → (unit → Y) → Y
ev-star' Y = ev-star (λ _ → Y)

abstract
  dependent-universal-property-unit :
    {l : Level} (P : unit → UU l) → is-equiv (ev-star P)
  dependent-universal-property-unit =
    dependent-universal-property-contr-is-contr star is-contr-unit

equiv-dependent-universal-property-unit :
  {l : Level} (P : unit → UU l) → ((x : unit) → P x) ≃ P star
pr1 (equiv-dependent-universal-property-unit P) = ev-star P
pr2 (equiv-dependent-universal-property-unit P) =
  dependent-universal-property-unit P

module _
  {l : Level} (Y : UU l)
  where

  is-section-const-unit : is-section (ev-star' Y) (const unit)
  is-section-const-unit = refl-htpy

  is-retraction-const-unit : is-retraction (ev-star' Y) (const unit)
  is-retraction-const-unit = refl-htpy

  universal-property-unit : is-equiv (ev-star' Y)
  universal-property-unit =
    is-equiv-is-invertible
      ( const unit)
      ( is-section-const-unit)
      ( is-retraction-const-unit)

  equiv-universal-property-unit : (unit → Y) ≃ Y
  equiv-universal-property-unit = (ev-star' Y , universal-property-unit)

  is-equiv-const-unit : is-equiv (const unit)
  is-equiv-const-unit =
    is-equiv-is-invertible
      ( ev-star' Y)
      ( is-retraction-const-unit)
      ( is-section-const-unit)

  inv-equiv-universal-property-unit : Y ≃ (unit → Y)
  inv-equiv-universal-property-unit = (const unit , is-equiv-const-unit)

abstract
  is-equiv-point-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X → is-equiv (point x)
  is-equiv-point-is-contr x is-contr-X =
    is-equiv-is-contr (point x) is-contr-unit is-contr-X

abstract
  is-equiv-point-universal-property-unit :
    {l1 : Level} (X : UU l1) (x : X) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x)) →
    is-equiv (point x)
  is-equiv-point-universal-property-unit X x H =
    is-equiv-is-equiv-precomp
      ( point x)
      ( λ Y →
        is-equiv-right-factor
          ( ev-star' Y)
          ( precomp (point x) Y)
          ( universal-property-unit Y)
          ( H Y))

abstract
  universal-property-unit-is-equiv-point :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (point x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-equiv-point x is-equiv-point Y =
    is-equiv-comp
      ( ev-star' Y)
      ( precomp (point x) Y)
      ( is-equiv-precomp-is-equiv (point x) is-equiv-point Y)
      ( universal-property-unit Y)

abstract
  universal-property-unit-is-contr :
    {l1 : Level} {X : UU l1} (x : X) →
    is-contr X →
    ({l2 : Level} (Y : UU l2) → is-equiv (λ (f : X → Y) → f x))
  universal-property-unit-is-contr x is-contr-X =
    universal-property-unit-is-equiv-point x
      ( is-equiv-point-is-contr x is-contr-X)

abstract
  is-equiv-diagonal-exponential-is-equiv-point :
    {l1 : Level} {X : UU l1} (x : X) →
    is-equiv (point x) →
    ({l2 : Level} (Y : UU l2) → is-equiv (diagonal-exponential Y X))
  is-equiv-diagonal-exponential-is-equiv-point x is-equiv-point Y =
    is-equiv-is-section
      ( universal-property-unit-is-equiv-point x is-equiv-point Y)
      ( refl-htpy)
```

