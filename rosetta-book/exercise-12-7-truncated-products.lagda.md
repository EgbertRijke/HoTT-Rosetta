# Exercise 12.7

```agda
module exercise-12-7-truncated-products where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-10-5-contractible-products
open import section-12-1-propositions
open import section-12-4-general-truncation-levels
open import exercise-12-6-truncated-sigma-types
```

## Problem statement

Consider two types `A` and `B`.
Show that the following are equivalent:

1. There are functions

   ```text
     f : B → is-trunc_{k+1}(A)
     g : A → is-trunc_{k+1}(B).
   ```

2. The type `A× B` is `(k+1)`-truncated.

Conclude with Exercise 10.5 that, if both `A` and `B` come equipped with an element, then both `A` and `B` are `k`-truncated if and only if the product `A × B` is `k`-truncated.

## Solution

```agda
abstract
  is-trunc-product :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-product k is-trunc-A is-trunc-B =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-B)

product-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) →
  Truncated-Type l1 k → Truncated-Type l2 k → Truncated-Type (l1 ⊔ l2) k
pr1 (product-Truncated-Type k A B) =
  type-Truncated-Type A × type-Truncated-Type B
pr2 (product-Truncated-Type k A B) =
  is-trunc-product k
    ( is-trunc-type-Truncated-Type A)
    ( is-trunc-type-Truncated-Type B)

is-trunc-product' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-product' k f g (a , b) (a' , b') =
  is-trunc-equiv k
    ( Eq-product (a , b) (a' , b'))
    ( equiv-pair-eq (a , b) (a' , b'))
    ( is-trunc-product k (f b a a') (g a b b'))

is-trunc-left-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-product neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-product A B H
is-trunc-left-factor-product (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-product k {A = (a ＝ a')} {B = (b ＝ b)}
    ( is-trunc-equiv' k
      ( (a , b) ＝ (a' , b))
      ( equiv-pair-eq (a , b) (a' , b))
      ( H (a , b) (a' , b)))
    ( refl)

is-trunc-right-factor-product :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-product neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-product A B H
is-trunc-right-factor-product (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-product k {A = (a ＝ a)} {B = (b ＝ b')}
    ( is-trunc-equiv' k
      ( (a , b) ＝ (a , b'))
      ( equiv-pair-eq (a , b) (a , b'))
      ( H (a , b) (a , b')))
    ( refl)
```

## Supplemental definitions

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-product H K = is-prop-Σ H (λ x → K)

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-product-Prop : UU (l1 ⊔ l2)
  type-product-Prop = type-Prop P × type-Prop Q

  is-prop-product-Prop : is-prop type-product-Prop
  is-prop-product-Prop =
    is-prop-product (is-prop-type-Prop P) (is-prop-type-Prop Q)

  product-Prop : Prop (l1 ⊔ l2)
  product-Prop = (type-product-Prop , is-prop-product-Prop)
```
