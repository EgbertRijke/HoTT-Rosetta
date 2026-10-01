# Exercise 9.1

```agda
module exercise-9-1-groupoid-operations-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-5-4-transport
```

## Problem statement

Show that the functions

```text
         inv : (x = y) → (y = x)
   concat(p) : (y = z) → (x = z)
  concat'(q) : (x = y) → (x = z)
     tr_B(p) : B(x) → B(y)
```

are equivalences, where `concat'(q,p) ≔ p ∙ q`.
Give their inverses explicitly.

## Solution

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-concat : {x y : A} (p : x ＝ y) (z : A) → x ＝ z → y ＝ z
  inv-concat p = concat (inv p)

  is-retraction-inv-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → inv p ∙ (p ∙ q) ＝ q
  is-retraction-inv-concat refl q = refl

  is-section-inv-concat :
    {x y z : A} (p : x ＝ y) (r : x ＝ z) → p ∙ (inv p ∙ r) ＝ r
  is-section-inv-concat refl r = refl

  is-retraction-inv-concat' :
    {x y z : A} (q : y ＝ z) (p : x ＝ y) → (p ∙ q) ∙ inv q ＝ p
  is-retraction-inv-concat' refl refl = refl

  is-section-inv-concat' :
    {x y z : A} (q : y ＝ z) (r : x ＝ z) → (r ∙ inv q) ∙ q ＝ r
  is-section-inv-concat' refl refl = refl

  cancellation-inv-inv-concat :
    {x y z : A} (p : x ＝ y) (q : x ＝ z) →
    p ∙ inv (inv q ∙ p) ＝ q
  cancellation-inv-inv-concat refl refl = refl

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

  inv-concat' : (x : A) {y z : A} → y ＝ z → x ＝ z → x ＝ y
  inv-concat' x q = concat' x (inv q)

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (concat' x q)
    is-equiv-concat' x q =
      is-equiv-is-invertible
        ( inv-concat' x q)
        ( is-section-inv-concat' q)
        ( is-retraction-inv-concat' q)

  abstract
    is-equiv-inv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (inv-concat' x q)
    is-equiv-inv-concat' x q =
      is-equiv-is-invertible
        ( concat' x q)
        ( is-retraction-inv-concat' q)
        ( is-section-inv-concat' q)

  equiv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ y) ≃ (x ＝ z)
  pr1 (equiv-concat' x q) = concat' x q
  pr2 (equiv-concat' x q) = is-equiv-concat' x q

  equiv-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ z) ≃ (x ＝ y)
  pr1 (equiv-inv-concat' x q) = inv-concat' x q
  pr2 (equiv-inv-concat' x q) = is-equiv-inv-concat' x q

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
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

## Supplement

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  conjugate-right-unit :
    {x y : A} {p q : x ＝ y} (s : p ＝ q) →
    inv right-unit ∙ ap (_∙ refl) s ∙ right-unit ＝ s
  conjugate-right-unit refl =
    ap (_∙ right-unit) right-unit ∙ left-inv right-unit
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-section-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-section (ap (concat p z)) (is-injective-concat p {q} {r})
  is-section-is-injective-concat refl refl = refl

  is-retraction-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-retraction (ap (concat p z)) (is-injective-concat p {q} {r})
  is-retraction-is-injective-concat refl refl = refl

  is-equiv-is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} →
    is-equiv (is-injective-concat p {q} {r})
  is-equiv-is-injective-concat {z = z} p =
    is-equiv-is-invertible
      ( ap (concat p z))
      ( is-retraction-is-injective-concat p)
      ( is-section-is-injective-concat p)

  cases-is-section-is-injective-concat' :
    {x y : A} {p q : x ＝ y} (s : p ＝ q) →
    ( ap
      ( concat' x refl)
      ( is-injective-concat' refl (right-unit ∙ (s ∙ inv right-unit)))) ＝
    ( right-unit ∙ (s ∙ inv right-unit))
  cases-is-section-is-injective-concat' {p = refl} refl = refl

  abstract
    is-section-is-injective-concat' :
      {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
      is-section (ap (concat' x r)) (is-injective-concat' r {p} {q})
    is-section-is-injective-concat' refl {p} {q} s =
      ( ap (λ u → ap (concat' _ refl) (is-injective-concat' refl u)) (inv α)) ∙
      ( ( cases-is-section-is-injective-concat'
          ( inv right-unit ∙ (s ∙ right-unit))) ∙
        ( α))
      where
      α :
        ( ( right-unit) ∙
          ( ( inv right-unit ∙ (s ∙ right-unit)) ∙
            ( inv right-unit))) ＝
        ( s)
      α =
        ( ap
          ( concat right-unit (q ∙ refl))
          ( ( assoc (inv right-unit) (s ∙ right-unit) (inv right-unit)) ∙
            ( ap
              ( concat (inv right-unit) (q ∙ refl))
              ( ( assoc s right-unit (inv right-unit)) ∙
                ( ap (concat s (q ∙ refl)) (right-inv right-unit)) ∙
                ( right-unit))))) ∙
        ( inv (assoc right-unit (inv right-unit) s)) ∙
        ( ( ap (concat' (p ∙ refl) s) (right-inv right-unit)))

  is-retraction-is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
    is-retraction (ap (concat' x r)) (is-injective-concat' r {p} {q})
  is-retraction-is-injective-concat' refl = conjugate-right-unit

  is-equiv-is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} →
    is-equiv (is-injective-concat' r {p} {q})
  is-equiv-is-injective-concat' {x} r =
    is-equiv-is-invertible
      ( ap (concat' x r))
      ( is-retraction-is-injective-concat' r)
      ( is-section-is-injective-concat' r)
```

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p p' : x ＝ y} (q : y ＝ z)
  where

  is-equiv-right-unwhisker-concat :
    is-equiv (λ (α : p ∙ q ＝ p' ∙ q) → right-unwhisker-concat q α)
  is-equiv-right-unwhisker-concat = is-equiv-is-injective-concat' q

  equiv-right-unwhisker-concat : (p ∙ q ＝ p' ∙ q) ≃ (p ＝ p')
  equiv-right-unwhisker-concat =
    ( right-unwhisker-concat q , is-equiv-right-unwhisker-concat)
```
