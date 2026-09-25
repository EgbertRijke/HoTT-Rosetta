# Exercise 7.9

```agda
module exercise-7-9-euclidean-division where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import section-6-4-peanos-seventh-and-eighth-axioms
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
```

## Problem statement

(Euclidean division) Consider two natural numbers `a` and `b`.

Construct two natural numbers `q` and `r` such that `(b≠ 0) → (r<b)`, along with an identification
```text
a=qb+r.
```

Show that for any four natural numbers `q,q'` and `r,r'` such that the implications `(b≠ 0) → (r<b)` and `(b≠ 0)→ (r'<b)` hold, and for which there are identifications
```text
a=qb+r and a=q'b+r',
```
we have `q=q'` and `r=r'`.

## Solution

```agda
leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (succ-ℕ k) (skip-zero-Fin k x))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inl x)))
    ( nat-skip-zero-Fin k x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inr star)))
    ( is-zero-nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin (succ-ℕ k) (inr star))))
```

```agda
leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ k zero-ℕ =
  concatenate-eq-leq-ℕ zero-ℕ (is-zero-nat-zero-Fin {k}) (refl-leq-ℕ zero-ℕ)
leq-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-leq-ℕ
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( leq-nat-mod-succ-ℕ k x)
    ( leq-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
```

```agda
opaque
  euclidean-division-ℕ :
    (k x : ℕ) → Σ ℕ (λ r → (cong-ℕ k x r) × (is-nonzero-ℕ k → le-ℕ r k))
  pr1 (euclidean-division-ℕ zero-ℕ x) = x
  pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
  pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
  pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)
  pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
    symmetric-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( x)
      ( cong-nat-mod-succ-ℕ k x)
  pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
    strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)

remainder-euclidean-division-ℕ : ℕ → ℕ → ℕ
remainder-euclidean-division-ℕ k x =
  pr1 (euclidean-division-ℕ k x)

cong-euclidean-division-ℕ :
  (k x : ℕ) → cong-ℕ k x (remainder-euclidean-division-ℕ k x)
cong-euclidean-division-ℕ k x =
  pr1 (pr2 (euclidean-division-ℕ k x))

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → le-ℕ (remainder-euclidean-division-ℕ k x) k
strict-upper-bound-remainder-euclidean-division-ℕ k x =
  pr2 (pr2 (euclidean-division-ℕ k x))

quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ k x =
  pr1 (cong-euclidean-division-ℕ k x)

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) →
  ( (quotient-euclidean-division-ℕ k x) *ℕ k) ＝
  ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

abstract opaque
  unfolding euclidean-division-ℕ

  eq-euclidean-division-ℕ :
    (k x : ℕ) →
    ( add-ℕ
      ( (quotient-euclidean-division-ℕ k x) *ℕ k)
      ( remainder-euclidean-division-ℕ k x)) ＝
    ( x)
  eq-euclidean-division-ℕ zero-ℕ x =
    ( inv
      ( ap
        ( _+ℕ x)
        ( right-zero-law-mul-ℕ (quotient-euclidean-division-ℕ zero-ℕ x)))) ∙
    ( left-unit-law-add-ℕ x)
  eq-euclidean-division-ℕ (succ-ℕ k) x =
    ( ap
      ( _+ℕ (remainder-euclidean-division-ℕ (succ-ℕ k) x))
      ( ( pr2 (cong-euclidean-division-ℕ (succ-ℕ k) x)) ∙
        ( symmetric-dist-ℕ x
          ( remainder-euclidean-division-ℕ (succ-ℕ k) x)))) ∙
    ( is-difference-dist-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x) x
      ( leq-nat-mod-succ-ℕ k x))
```
