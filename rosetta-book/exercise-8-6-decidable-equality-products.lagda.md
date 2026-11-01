# Exercise 8.6

```agda
module exercise-8-6-decidable-equality-products where

open import universe-levels
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-8-1-decidability-and-decidable-equality
```

## Problem statement

Consider two types `A` and `B`.
Show that the following are equivalent:

1. There are functions
```text
B → has-decidable-eq(A)
A → has-decidable-eq(B).
```

2. The product `A × B` has decidable equality.

Conclude that if both `A` and `B` have decidable equality, then so does `A × B`.

## Solution

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
... | inr np = inr (λ q → np (ap (λ z → a , z) q))
```
