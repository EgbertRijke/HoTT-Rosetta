# Exercise 9.1

```agda
module exercise-9-1-groupoid-operations-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-5-4-transport
```

## Problem statement

Show that the functions
```text
inv :(x = y)→(y = x)
concat(p) : (y = z)→(x = z)
concat'(q) : (x = y) → (x = z)
tr_B(p) :B(x)→ B(y)
```
are equivalences, where `concat'(q,p)≔ p ∙ q`.
Give their inverses explicitly.

## Solution

<!-- rosetta-item: exercise-9-1 -->

<!-- rosetta-agda-block: exercise-9-1-inverse-concatenation -->

```agda
module _
  {l : Level} {A : Type l}
  where

  inv-concat : {x y : A} (p : x ＝ y) (z : A) → x ＝ z → y ＝ z
  inv-concat p = concat (inv p)
```

<!-- rosetta-agda-block: exercise-9-1-concatenation-inverse-laws -->

```agda
module _
  {l : Level} {A : Type l}
  where

  is-retraction-inv-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → inv p ∙ (p ∙ q) ＝ q
  is-retraction-inv-concat refl q = refl

  is-section-inv-concat :
    {x y z : A} (p : x ＝ y) (r : x ＝ z) → p ∙ (inv p ∙ r) ＝ r
  is-section-inv-concat refl r = refl
```

<!-- rosetta-agda-block: exercise-9-1-inversion-and-concatenation-equivalences -->

```agda
module _
  {l : Level} {A : Type l}
  where

  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : x ＝ y) → inv p)
    is-equiv-inv x y = is-equiv-is-invertible inv inv-inv inv-inv

  equiv-inv : (x y : A) → (x ＝ y) ≃ (y ＝ x)
  pr1 (equiv-inv x y) = inv
  pr2 (equiv-inv x y) = is-equiv-inv x y

  abstract
    is-equiv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z =
      is-equiv-is-invertible
        ( inv-concat p z)
        ( is-section-inv-concat p)
        ( is-retraction-inv-concat p)

  abstract
    is-equiv-inv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (inv-concat p z)
    is-equiv-inv-concat p z =
      is-equiv-is-invertible
        ( concat p z)
        ( is-retraction-inv-concat p)
        ( is-section-inv-concat p)

  equiv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (y ＝ z) ≃ (x ＝ z)
  pr1 (equiv-concat p z) = concat p z
  pr2 (equiv-concat p z) = is-equiv-concat p z

  equiv-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (x ＝ z) ≃ (y ＝ z)
  pr1 (equiv-inv-concat p z) = inv-concat p z
  pr2 (equiv-inv-concat p z) = is-equiv-inv-concat p z
```

<!-- rosetta-agda-block: exercise-9-1-transport-equivalences -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {x y : A}
  where

  is-retraction-inv-tr : (p : x ＝ y) → is-retraction (tr B p) (tr B (inv p))
  is-retraction-inv-tr refl b = refl

  is-section-inv-tr : (p : x ＝ y) → is-section (tr B p) (tr B (inv p))
  is-section-inv-tr refl b = refl

  is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
  is-equiv-tr p =
    is-equiv-is-invertible
      ( tr B (inv p))
      ( is-section-inv-tr p)
      ( is-retraction-inv-tr p)

  is-equiv-inv-tr : (p : x ＝ y) → is-equiv (tr B (inv p))
  is-equiv-inv-tr p =
    is-equiv-is-invertible
      ( tr B p)
      ( is-retraction-inv-tr p)
      ( is-section-inv-tr p)

  equiv-tr : x ＝ y → B x ≃ B y
  equiv-tr p = (tr B p , is-equiv-tr p)

  equiv-inv-tr : x ＝ y → B y ≃ B x
  equiv-inv-tr p = (tr B (inv p) , is-equiv-inv-tr p)
```
