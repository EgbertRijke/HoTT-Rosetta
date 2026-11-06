# Exercise 13.9

```agda
module exercise-13-9-uniqueness-of-identity-types where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-13-3-universal-properties
open import exercise-13-7-universal-property-contractible-types
```

## Problem statement

Consider a type `A` equipped with an element `a : A` and consider a type family `B` over `A` equipped with an element `b : B(a)`.
Show that the following are equivalent:

1. The map

   ```text
     ev_b : (Π(x : A) B(x) → C(x)) → C(a)
   ```
    
   given by `ev_b(h) ≔ h(a,b)` is an equivalence for any type family `C` over `A`.

2. The map

   ```text
     h : Π(x : A) (a = x) → B(x)
   ```
    
   given by `h(a,refl) ≔ b` is an equivalence.

## Solution

```agda
dependent-universal-property-identity-system :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {a : A} (b : B a) → UUω
dependent-universal-property-identity-system {A = A} B b =
  {l3 : Level} (P : (x : A) (y : B x) → UU l3) →
  is-equiv (ev-refl-identity-system b {P})

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A} (b : B a)
  where

  dependent-universal-property-identity-system-is-torsorial :
    is-torsorial B →
    dependent-universal-property-identity-system B b
  dependent-universal-property-identity-system-is-torsorial
    H P =
    is-equiv-left-factor
      ( ev-refl-identity-system b)
      ( ev-pair)
      ( dependent-universal-property-contr-is-contr
        ( a , b)
        ( H)
        ( λ u → P (pr1 u) (pr2 u)))
      ( is-equiv-ev-pair)

  equiv-dependent-universal-property-identity-system-is-torsorial :
    is-torsorial B →
    {l : Level} {C : (x : A) → B x → UU l} →
    ((x : A) (y : B x) → C x y) ≃ C a b
  pr1 (equiv-dependent-universal-property-identity-system-is-torsorial H) =
    ev-refl-identity-system b
  pr2 (equiv-dependent-universal-property-identity-system-is-torsorial H) =
    dependent-universal-property-identity-system-is-torsorial H _

  is-torsorial-dependent-universal-property-identity-system :
    dependent-universal-property-identity-system B b →
    is-torsorial B
  pr1 (is-torsorial-dependent-universal-property-identity-system H) = (a , b)
  pr2 (is-torsorial-dependent-universal-property-identity-system H) u =
    map-inv-is-equiv
      ( H (λ x y → (a , b) ＝ (x , y)))
      ( refl)
      ( pr1 u)
      ( pr2 u)
```
