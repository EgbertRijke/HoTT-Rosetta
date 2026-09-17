# Exercise 8.6

```agda
module exercise-8-6-decidable-equality-products where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-8-1-decidability-and-decidable-equality
open import section-5-4-transport
```

## Problem statement

Consider two types `A` and `B`.
Show that the following are equivalent:

1. There are functions
```text
B → has-decidable-eq(A)
A → has-decidable-eq(B).
```

2. The product `A× B` has decidable equality.

Conclude that if both `A` and `B` have decidable equality, then so does `A× B`.

## Solution

<!-- rosetta-agda-block: exercise-8-6-sigma-equality -->

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t =
    Σ (pr1 s ＝ pr1 t) (λ α → dependent-identification B α (pr2 s) (pr2 t))
```

<!-- rosetta-agda-block: exercise-8-6-sigma-identity -->

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  refl-Eq-Σ s = refl , refl

  eq-base-eq-pair : {s t : Σ A B} → s ＝ t → pr1 s ＝ pr1 t
  eq-base-eq-pair = ap pr1

  dependent-identification-eq-pair :
    {s t : Σ A B} (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair p) (pr2 s) (pr2 t)
  dependent-identification-eq-pair {s} p = tr-ap pr1 (λ x _ → pr2 x) p (pr1 s)

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ p = eq-base-eq-pair p , dependent-identification-eq-pair p

  eq-pair-eq-base :
    {x y : A} {s : B x} (p : x ＝ y) → (x , s) ＝ (y , tr B p s)
  eq-pair-eq-base refl = refl

  eq-pair-eq-base' :
    {x y : A} {t : B y} (p : x ＝ y) → (x , tr B (inv p) t) ＝ (y , t)
  eq-pair-eq-base' refl = refl

  eq-pair-eq-fiber :
    {x : A} {s t : B x} → s ＝ t → (x , s) ＝ (x , t)
  eq-pair-eq-fiber {x} = ap {B = Σ A B} (pair x)

  eq-pair-Σ :
    {s t : Σ A B}
    (α : pr1 s ＝ pr1 t) →
    dependent-identification B α (pr2 s) (pr2 t) → s ＝ t
  eq-pair-Σ refl = eq-pair-eq-fiber

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = eq-pair-Σ (pr1 p) (pr2 p)
```

<!-- rosetta-agda-block: exercise-8-6-product-forward -->

```agda
has-decidable-equality-product' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-product' f g (x , y) (x' , y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-product d e =
  has-decidable-equality-product' (λ _ → d) (λ _ → e)
```

<!-- rosetta-agda-block: exercise-8-6-product-backward -->

```agda
has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (x , b) (y , b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → z , b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (a , x) (a , y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (eq-pair-eq-fiber q))
```
