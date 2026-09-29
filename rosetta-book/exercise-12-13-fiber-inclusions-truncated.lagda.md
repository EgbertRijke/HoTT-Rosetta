# Exercise 12.13

```agda
module exercise-12-13-fiber-inclusions-truncated where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-7-fibers-of-projections
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-17-1-equivalent-forms-of-the-univalence-axiom
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is `(k + 1)`-truncated.

2. For any type family `B` over `A` and any `a : A`, the **fiber inclusion**

   ```text
     i_a: B(a)→Σ(x:A) B(x)
   ```

   given by `y ↦ (a,y)` is a `k`-truncated map.

In particular, if `A` is a set then any fiber inclusion `i_a : B(a) → Σ(x:A) B(x)` is an embedding.

## Solution

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  fiber-inclusion : (x : A) → B x → Σ A B
  pr1 (fiber-inclusion x y) = x
  pr2 (fiber-inclusion x y) = y

  fiber-fiber-inclusion :
    (a : A) (t : Σ A B) → fiber (fiber-inclusion a) t ≃ (a ＝ pr1 t)
  fiber-fiber-inclusion a t =
    ( ( right-unit-law-Σ-is-contr
        ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
      ( equiv-left-swap-Σ)) ∘e
    ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  is-trunc-is-trunc-map-fiber-inclusion :
    ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
    is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-map-fiber-inclusion H x y =
    is-trunc-equiv' k
      ( fiber (fiber-inclusion B x) (pair y raise-star))
      ( fiber-fiber-inclusion B x (pair y raise-star))
      ( H B x (pair y raise-star))
    where
    B : A → UU l2
    B a = raise-unit l2

  is-trunc-map-fiber-inclusion-is-trunc :
    (B : A → UU l2) (a : A) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
  is-trunc-map-fiber-inclusion-is-trunc B a H t =
    is-trunc-equiv k
      ( a ＝ pr1 t)
      ( fiber-fiber-inclusion B a t)
      ( H a (pr1 t))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-contr-map-fiber-inclusion :
    (x : A) → is-prop A → is-contr-map (fiber-inclusion B x)
  is-contr-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-two-𝕋 B

  is-prop-map-fiber-inclusion :
    (x : A) → is-set A → is-prop-map (fiber-inclusion B x)
  is-prop-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B

  is-0-map-fiber-inclusion :
    (x : A) → is-1-type A → is-0-map (fiber-inclusion B x)
  is-0-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc zero-𝕋 B

  is-emb-fiber-inclusion : is-set A → (x : A) → is-emb (fiber-inclusion B x)
  is-emb-fiber-inclusion H x =
    is-emb-is-prop-map (is-prop-map-fiber-inclusion x H)

  emb-fiber-inclusion : is-set A → (x : A) → B x ↪ Σ A B
  pr1 (emb-fiber-inclusion H x) = fiber-inclusion B x
  pr2 (emb-fiber-inclusion H x) = is-emb-fiber-inclusion H x

fiber-inclusion-emb :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → UU l2) →
  (x : type-Set A) → B x ↪ Σ (type-Set A) B
pr1 (fiber-inclusion-emb A B x) = fiber-inclusion B x
pr2 (fiber-inclusion-emb A B x) = is-emb-fiber-inclusion B (is-set-type-Set A) x
```
