# Exercise 6.4 Strict order on the natural numbers

```agda
module exercise-6-4-strict-order-natural-numbers where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
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
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
```

## Problem statement

The strict ordering relation `<` on `ℕ` is defined recursively by

```text
  (0 < 0)       := ∅      (0 < n + 1)       := 𝟙
  (m + 1 < 0)   := ∅      (m + 1 < n + 1)   := (m < n).
```

Show that the strict ordering relation is antireflexive, antisymmetric, and
transitive.

## Solution

```agda
le-ℕ : ℕ → ℕ → UU lzero
le-ℕ m zero-ℕ = empty
le-ℕ zero-ℕ (succ-ℕ m) = unit
le-ℕ (succ-ℕ n) (succ-ℕ m) = le-ℕ n m

infix 30 _<-ℕ_
_<-ℕ_ = le-ℕ
```

```agda
concatenate-eq-le-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → le-ℕ y z → z ＝ w → le-ℕ x w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → x ＝ y → le-ℕ y z → le-ℕ x z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → le-ℕ x y → y ＝ z → le-ℕ x z
concatenate-le-eq-ℕ p refl = p
```

```agda
is-nonzero-le-ℕ : (m n : ℕ) → le-ℕ m n → is-nonzero-ℕ n
is-nonzero-le-ℕ m .zero-ℕ () refl

abstract
  le-is-nonzero-ℕ : (n : ℕ) → is-nonzero-ℕ n → le-ℕ zero-ℕ n
  le-is-nonzero-ℕ zero-ℕ H = H refl
  le-is-nonzero-ℕ (succ-ℕ n) H = star

  contradiction-le-zero-ℕ :
    (m : ℕ) → (le-ℕ m zero-ℕ) → empty
  contradiction-le-zero-ℕ zero-ℕ ()
  contradiction-le-zero-ℕ (succ-ℕ m) ()

  contradiction-le-one-ℕ :
    (n : ℕ) → le-ℕ (succ-ℕ n) 1 → empty
  contradiction-le-one-ℕ zero-ℕ ()
  contradiction-le-one-ℕ (succ-ℕ n) ()
```

```agda
abstract
  irreflexive-le-ℕ : (n : ℕ) → ¬ (n <-ℕ n)
  irreflexive-le-ℕ zero-ℕ ()
  irreflexive-le-ℕ (succ-ℕ n) = irreflexive-le-ℕ n

  neq-le-ℕ : {x y : ℕ} → le-ℕ x y → ¬ (x ＝ y)
  neq-le-ℕ {x} H refl = irreflexive-le-ℕ x H

  antisymmetric-le-ℕ : (m n : ℕ) → le-ℕ m n → le-ℕ n m → m ＝ n
  antisymmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
    ap succ-ℕ (antisymmetric-le-ℕ m n p q)

  transitive-le-ℕ : (n m l : ℕ) → (le-ℕ n m) → (le-ℕ m l) → (le-ℕ n l)
  transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
  transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
    transitive-le-ℕ n m l p q
```

## Problem statement

Show that `n < n + 1` and

```text
  (m < n) → (m < n + 1)
```

for any `m, n : ℕ`.

## Solution

```agda
abstract
  succ-le-ℕ : (n : ℕ) → le-ℕ n (succ-ℕ n)
  succ-le-ℕ zero-ℕ = star
  succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n

  preserves-le-succ-ℕ :
    (m n : ℕ) → le-ℕ m n → le-ℕ m (succ-ℕ n)
  preserves-le-succ-ℕ m n H =
    transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)
```

## Problem statement

Show that

```text
  (m < n) ↔ (m + 1 ≤ n)
  (m < n) ↔ (n ≰ m)
```

for any `m, n : ℕ`.

## Solution

```agda
abstract
  concatenate-leq-le-ℕ :
    {x y z : ℕ} → x ≤-ℕ y → le-ℕ y z → le-ℕ x z
  concatenate-leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} H K = star
  concatenate-leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
  concatenate-leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
    concatenate-leq-le-ℕ {x} {y} {z} H K

  concatenate-le-leq-ℕ :
    {x y z : ℕ} → le-ℕ x y → y ≤-ℕ z → le-ℕ x z
  concatenate-le-leq-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
  concatenate-le-leq-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
    concatenate-le-leq-ℕ {x} {y} {z} H K
```

```agda
abstract
  contradiction-le-ℕ : (m n : ℕ) → le-ℕ m n → ¬ (n ≤-ℕ m)
  contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
  contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H

  contradiction-le-ℕ' : (m n : ℕ) → n ≤-ℕ m → ¬ (le-ℕ m n)
  contradiction-le-ℕ' m n K H = contradiction-le-ℕ m n H K

  leq-not-le-ℕ : (m n : ℕ) → ¬ (le-ℕ m n) → n ≤-ℕ m
  leq-not-le-ℕ zero-ℕ zero-ℕ H = star
  leq-not-le-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
  leq-not-le-ℕ (succ-ℕ m) zero-ℕ H = star
  leq-not-le-ℕ (succ-ℕ m) (succ-ℕ n) H = leq-not-le-ℕ m n H

  le-not-leq-ℕ : (m n : ℕ) → ¬ (n ≤-ℕ m) → le-ℕ m n
  le-not-leq-ℕ zero-ℕ zero-ℕ H = ex-falso (H star)
  le-not-leq-ℕ zero-ℕ (succ-ℕ n) H = star
  le-not-leq-ℕ (succ-ℕ m) zero-ℕ H = ex-falso (H star)
  le-not-leq-ℕ (succ-ℕ m) (succ-ℕ n) H = le-not-leq-ℕ m n H
```

```agda
abstract
  leq-le-ℕ :
    (x y : ℕ) → le-ℕ x y → x ≤-ℕ y
  leq-le-ℕ zero-ℕ (succ-ℕ y) H = star
  leq-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-ℕ x y H

  leq-le-succ-ℕ :
    (x y : ℕ) → le-ℕ x (succ-ℕ y) → x ≤-ℕ y
  leq-le-succ-ℕ zero-ℕ y H = star
  leq-le-succ-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-succ-ℕ x y H

  leq-succ-le-ℕ :
    (x y : ℕ) → le-ℕ x y → leq-ℕ (succ-ℕ x) y
  leq-succ-le-ℕ zero-ℕ (succ-ℕ y) H = star
  leq-succ-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-succ-le-ℕ x y H

  le-leq-succ-ℕ :
    (x y : ℕ) → leq-ℕ (succ-ℕ x) y → le-ℕ x y
  le-leq-succ-ℕ zero-ℕ (succ-ℕ y) H = star
  le-leq-succ-ℕ (succ-ℕ x) (succ-ℕ y) H = le-leq-succ-ℕ x y H

  le-succ-leq-ℕ :
    (x y : ℕ) → leq-ℕ x y → le-ℕ x (succ-ℕ y)
  le-succ-leq-ℕ zero-ℕ y H = star
  le-succ-leq-ℕ (succ-ℕ x) (succ-ℕ y) H = le-succ-leq-ℕ x y H
```
