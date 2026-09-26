# Exercise 7.7

```agda
module exercise-7-7-classical-finite-types where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-1-injectivity-addition-multiplication
open import section-6-4-peanos-seventh-and-eighth-axioms
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
```

## Problem statement

Recall that
```text
classical-Fin_k:=Σ(x:ℕ) x<k.
```

Show that
```text
(x=y)↔ (pr 1(x)=pr 1(y))
```
for each `x,y:classical-Fin_k`.

By Lemma 7.3.5 it follows that the map `nat-Fin :Fin{k}→ℕ` induces a map `nat-Fin:Fin{k}→classical-Fin_k`.
Construct a map
```text
α_k:classical-Fin_k → Fin{k}
```
for each `k:ℕ`, and show that
```text
α_k(nat-Fin(x)) = x and nat-Fin(α_k(y)) = y
```
for each `x:Fin{k}` and each `y:classical-Fin_k`.

## Solution

```agda
standard-classical-Fin : (k : ℕ) → classical-Fin k → Fin k
standard-classical-Fin (succ-ℕ k) (pair x H) = mod-succ-ℕ k x

classical-standard-Fin :
  (k : ℕ) → Fin k → classical-Fin k
pr1 (classical-standard-Fin k x) = nat-Fin k x
pr2 (classical-standard-Fin k x) = strict-upper-bound-nat-Fin k x
```

```agda
is-section-classical-standard-Fin :
  {k : ℕ} (x : Fin k) →
  standard-classical-Fin k (classical-standard-Fin k x) ＝ x
is-section-classical-standard-Fin {succ-ℕ k} x = is-section-nat-Fin k x

is-retraction-classical-standard-Fin :
  {k : ℕ} (x : classical-Fin k) →
  classical-standard-Fin k (standard-classical-Fin k x) ＝ x
is-retraction-classical-standard-Fin {succ-ℕ k} (pair x p) =
  eq-Eq-classical-Fin (succ-ℕ k)
    ( classical-standard-Fin
      ( succ-ℕ k)
      ( standard-classical-Fin (succ-ℕ k) (pair x p)))
    ( pair x p)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( x)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( p)
      ( cong-nat-mod-succ-ℕ k x))
```
