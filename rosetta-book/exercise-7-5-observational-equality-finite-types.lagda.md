# Exercise 7.5

```agda
module exercise-7-5-observational-equality-finite-types where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
```

## Problem statement

The observational equality on `Fin{k}` is a binary relation
```text
Eq-Fin_{k}:Fin{k}→(Fin{k}→𝒰_0)
```
defined recursively by
```text
Eq-Fin_{k+1}(i(x),i(y)) ≔ Eq-Fin_k(x,y) Eq-Fin_{k+1}(i(x),⋆) ≔ empty
Eq-Fin_{k+1}(⋆,i(y)) ≔ empty Eq-Fin_{k+1}(⋆,⋆) ≔ unit.
```

<div class="subexenum">

Show that
```text
(x=y)↔ Eq-Fin_k(x,y)
```
for any two elements `x,y:Fin{k}`.

Show that the function `i:Fin{k}→Fin{k+1}` is injective, for each `k:ℕ`.

Show that
```text
succ-Fin_{k+1}(i(x))≠ 0
```
for any `x:Fin{k}`.

Show that function `succ-Fin_k:Fin{k}→Fin{k}` is injective, for each `k:ℕ`.

</div>

## Solution

<!-- rosetta-item: exercise-7-5 -->

<!-- rosetta-agda-block: exercise-7-5-observational-equality -->

```agda
Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit
refl-Eq-Fin : (k : ℕ) (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin (succ-ℕ k) (inl x) = refl-Eq-Fin k x
refl-Eq-Fin (succ-ℕ k) (inr x) = star

Eq-Fin-eq : (k : ℕ) {x y : Fin k} → x ＝ y → Eq-Fin k x y
Eq-Fin-eq k refl = refl-Eq-Fin k _

eq-Eq-Fin :
  (k : ℕ) {x y : Fin k} → Eq-Fin k x y → x ＝ y
eq-Eq-Fin (succ-ℕ k) {inl x} {inl y} e = ap inl (eq-Eq-Fin k e)
eq-Eq-Fin (succ-ℕ k) {inr star} {inr star} star = refl
```

<!-- rosetta-agda-block: exercise-7-5-zero-predicates -->

```agda
is-zero-Fin : (k : ℕ) → Fin k → UU lzero
is-zero-Fin (succ-ℕ k) x = x ＝ zero-Fin k

is-zero-Fin' : (k : ℕ) → Fin k → UU lzero
is-zero-Fin' (succ-ℕ k) x = zero-Fin k ＝ x

is-nonzero-Fin : (k : ℕ) → Fin k → UU lzero
is-nonzero-Fin (succ-ℕ k) x = ¬ (is-zero-Fin (succ-ℕ k) x)
```

<!-- rosetta-agda-block: exercise-7-5-injective-inclusion -->

```agda
is-injective-inl-Fin : (k : ℕ) → is-injective (inl-Fin k)
is-injective-inl-Fin k refl = refl
```

<!-- rosetta-agda-block: exercise-7-5-successor-nonzero -->

```agda
neq-zero-skip-zero-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (skip-zero-Fin k x)
neq-zero-skip-zero-Fin {succ-ℕ k} {inl x} p =
  neq-zero-skip-zero-Fin {k = k} {x = x} (is-injective-inl-Fin (succ-ℕ k) p)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin (succ-ℕ k) p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} ()
```

<!-- rosetta-agda-block: exercise-7-5-injective-successor -->

```agda
is-injective-skip-zero-Fin : (k : ℕ) → is-injective (skip-zero-Fin k)
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k (is-injective-inl-Fin (succ-ℕ k) p))
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inr star} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inl y} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inr star} p = refl

is-injective-succ-Fin : (k : ℕ) → is-injective (succ-Fin k)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k {x} {y} p)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inr star} p = refl
```
