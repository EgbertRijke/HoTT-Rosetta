# Exercise 6.5 Distance on the natural numbers

```agda
module exercise-6-5-distance-natural-numbers where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
open import section-2-2-ordinary-function-types
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
open import section-5-4-transport
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import path-algebra
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
```

## Problem statement

The **distance function**

```text
  dist-ℕ : ℕ → (ℕ → ℕ)
```

is defined recursively by

```text
  dist-ℕ(0, 0)       := 0       dist-ℕ(0, n + 1)       := n + 1
  dist-ℕ(m + 1, 0)   := m + 1   dist-ℕ(m + 1, n + 1)   := dist-ℕ(m, n).
```

In other words, the distance between two natural numbers is the *symmetric
difference* between them.
Show that `dist-ℕ` satisfies the axioms of a metric:

1. `(m = n) ↔ (dist-ℕ(m, n) = 0)`.
2. `dist-ℕ(m, n) = dist-ℕ(n, m)`.
3. `dist-ℕ(m, n) ≤ dist-ℕ(m, k) + dist-ℕ(k, n)`.

## Solution

```agda
ap-add-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → m +ℕ n ＝ m' +ℕ n'
ap-add-ℕ p q = ap-binary add-ℕ p q

dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ n = n
dist-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
dist-ℕ (succ-ℕ m) (succ-ℕ n) = dist-ℕ m n

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = dist-ℕ n m

ap-dist-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → dist-ℕ m n ＝ dist-ℕ m' n'
ap-dist-ℕ p q = ap-binary dist-ℕ p q
```

```agda
abstract
  eq-dist-ℕ : (m n : ℕ) → is-zero-ℕ (dist-ℕ m n) → m ＝ n
  eq-dist-ℕ zero-ℕ zero-ℕ p = refl
  eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (eq-dist-ℕ m n p)

  dist-eq-ℕ' : (n : ℕ) → is-zero-ℕ (dist-ℕ n n)
  dist-eq-ℕ' zero-ℕ = refl
  dist-eq-ℕ' (succ-ℕ n) = dist-eq-ℕ' n

  dist-eq-ℕ : (m n : ℕ) → m ＝ n → is-zero-ℕ (dist-ℕ m n)
  dist-eq-ℕ m .m refl = dist-eq-ℕ' m

  dist-neq-ℕ : (m n : ℕ) → ¬ (m ＝ n) → is-nonzero-ℕ (dist-ℕ m n)
  dist-neq-ℕ m n = map-neg (eq-dist-ℕ m n)

  dist-neq-ℕ' : (m n : ℕ) → ¬ (m ＝ n) → is-successor-ℕ (dist-ℕ m n)
  dist-neq-ℕ' m n np = is-successor-is-nonzero-ℕ (dist-neq-ℕ m n np)
```

```agda
abstract
  is-one-dist-succ-ℕ : (x : ℕ) → is-one-ℕ (dist-ℕ x (succ-ℕ x))
  is-one-dist-succ-ℕ zero-ℕ = refl
  is-one-dist-succ-ℕ (succ-ℕ x) = is-one-dist-succ-ℕ x

  is-one-dist-succ-ℕ' : (x : ℕ) → is-one-ℕ (dist-ℕ (succ-ℕ x) x)
  is-one-dist-succ-ℕ' zero-ℕ = refl
  is-one-dist-succ-ℕ' (succ-ℕ x) = is-one-dist-succ-ℕ' x
```

```agda
abstract
  commutative-dist-ℕ :
    (m n : ℕ) → dist-ℕ m n ＝ dist-ℕ n m
  commutative-dist-ℕ zero-ℕ zero-ℕ = refl
  commutative-dist-ℕ zero-ℕ (succ-ℕ n) = refl
  commutative-dist-ℕ (succ-ℕ m) zero-ℕ = refl
  commutative-dist-ℕ (succ-ℕ m) (succ-ℕ n) = commutative-dist-ℕ m n
```

```agda
abstract
  left-unit-law-dist-ℕ :
    (n : ℕ) → dist-ℕ zero-ℕ n ＝ n
  left-unit-law-dist-ℕ zero-ℕ = refl
  left-unit-law-dist-ℕ (succ-ℕ n) = refl

  right-unit-law-dist-ℕ :
    (n : ℕ) → dist-ℕ n zero-ℕ ＝ n
  right-unit-law-dist-ℕ zero-ℕ = refl
  right-unit-law-dist-ℕ (succ-ℕ n) = refl
```

```agda
abstract
  triangle-inequality-dist-ℕ :
    (m n k : ℕ) → (dist-ℕ m n) ≤-ℕ ((dist-ℕ m k) +ℕ (dist-ℕ k n))
  triangle-inequality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = star
  triangle-inequality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = star
  triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ =
    tr
      ( leq-ℕ (succ-ℕ n))
      ( inv (left-unit-law-add-ℕ (succ-ℕ n)))
      ( refl-leq-ℕ (succ-ℕ n))
  triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
    concatenate-eq-leq-eq-ℕ
      ( inv (ap succ-ℕ (left-unit-law-dist-ℕ n)))
      ( triangle-inequality-dist-ℕ zero-ℕ n k)
      ( ( ap (succ-ℕ ∘ (_+ℕ (dist-ℕ k n))) (left-unit-law-dist-ℕ k)) ∙
        ( inv (left-successor-law-add-ℕ k (dist-ℕ k n))))
  triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl-leq-ℕ (succ-ℕ m)
  triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
    concatenate-eq-leq-eq-ℕ
      ( inv (ap succ-ℕ (right-unit-law-dist-ℕ m)))
      ( triangle-inequality-dist-ℕ m zero-ℕ k)
      ( ap (succ-ℕ ∘ ((dist-ℕ m k) +ℕ_)) (right-unit-law-dist-ℕ k))
  triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ =
    concatenate-leq-eq-ℕ
      ( dist-ℕ m n)
      ( transitive-leq-ℕ
        ( dist-ℕ m n)
        ( succ-ℕ ((dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n)))
        ( succ-ℕ (succ-ℕ ((dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n))))
        ( succ-leq-ℕ (succ-ℕ ((dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n))))
        ( transitive-leq-ℕ
          ( dist-ℕ m n)
          ( (dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n))
          ( succ-ℕ ((dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n)))
          ( succ-leq-ℕ ((dist-ℕ m zero-ℕ) +ℕ (dist-ℕ zero-ℕ n)))
          ( triangle-inequality-dist-ℕ m n zero-ℕ)))
      ( ( ap
          ( succ-ℕ ∘ succ-ℕ)
          ( ap-add-ℕ (right-unit-law-dist-ℕ m) (left-unit-law-dist-ℕ n))) ∙
        ( inv (left-successor-law-add-ℕ m (succ-ℕ n))))
  triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
    triangle-inequality-dist-ℕ m n k
```

## Problem statement

Show that `dist-ℕ(m, n) = dist-ℕ(m, k) + dist-ℕ(k, n)` if and only if either
both `m ≤ k` and `k ≤ n` hold or both `n ≤ k` and `k ≤ m` hold.

## Solution

```agda
abstract
  is-additive-right-inverse-dist-ℕ :
    (x y : ℕ) → x ≤-ℕ y → x +ℕ (dist-ℕ x y) ＝ y
  is-additive-right-inverse-dist-ℕ zero-ℕ zero-ℕ H = refl
  is-additive-right-inverse-dist-ℕ zero-ℕ (succ-ℕ y) star =
    left-unit-law-add-ℕ (succ-ℕ y)
  is-additive-right-inverse-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
    ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
    ( ap succ-ℕ (is-additive-right-inverse-dist-ℕ x y H))
```

```agda
abstract
  rewrite-left-add-dist-ℕ :
    (x y z : ℕ) → x +ℕ y ＝ z → x ＝ dist-ℕ y z
  rewrite-left-add-dist-ℕ zero-ℕ zero-ℕ .zero-ℕ refl = refl
  rewrite-left-add-dist-ℕ zero-ℕ (succ-ℕ y) .(succ-ℕ (zero-ℕ +ℕ y)) refl =
    ( inv (dist-eq-ℕ' y)) ∙
    ( inv (ap (dist-ℕ (succ-ℕ y)) (left-unit-law-add-ℕ (succ-ℕ y))))
  rewrite-left-add-dist-ℕ (succ-ℕ x) zero-ℕ .(succ-ℕ x) refl = refl
  rewrite-left-add-dist-ℕ (succ-ℕ x) (succ-ℕ y) ._ refl =
    rewrite-left-add-dist-ℕ (succ-ℕ x) y ((succ-ℕ x) +ℕ y) refl

  rewrite-left-dist-add-ℕ :
    (x y z : ℕ) → y ≤-ℕ z → x ＝ dist-ℕ y z → x +ℕ y ＝ z
  rewrite-left-dist-add-ℕ .(dist-ℕ y z) y z H refl =
    ( commutative-add-ℕ (dist-ℕ y z) y) ∙
    ( is-additive-right-inverse-dist-ℕ y z H)

  rewrite-right-add-dist-ℕ :
    (x y z : ℕ) → x +ℕ y ＝ z → y ＝ dist-ℕ x z
  rewrite-right-add-dist-ℕ x y z p =
    rewrite-left-add-dist-ℕ y x z (commutative-add-ℕ y x ∙ p)

  rewrite-right-dist-add-ℕ :
    (x y z : ℕ) → x ≤-ℕ z → y ＝ dist-ℕ x z → x +ℕ y ＝ z
  rewrite-right-dist-add-ℕ x .(dist-ℕ x z) z H refl =
    is-additive-right-inverse-dist-ℕ x z H

  is-difference-dist-ℕ :
    (x y : ℕ) → x ≤-ℕ y → x +ℕ (dist-ℕ x y) ＝ y
  is-difference-dist-ℕ zero-ℕ zero-ℕ H = refl
  is-difference-dist-ℕ zero-ℕ (succ-ℕ y) H = left-unit-law-add-ℕ (succ-ℕ y)
  is-difference-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
    ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
    ( ap succ-ℕ (is-difference-dist-ℕ x y H))

  is-difference-dist-ℕ' :
    (x y : ℕ) → x ≤-ℕ y → (dist-ℕ x y) +ℕ x ＝ y
  is-difference-dist-ℕ' x y H =
    ( commutative-add-ℕ (dist-ℕ x y) x) ∙
    ( is-difference-dist-ℕ x y H)
```

```agda
abstract
  dist-add-ℕ : (x y : ℕ) → dist-ℕ x (x +ℕ y) ＝ y
  dist-add-ℕ x y = inv (rewrite-right-add-dist-ℕ x y (x +ℕ y) refl)

  dist-add-ℕ' : (x y : ℕ) → dist-ℕ (x +ℕ y) x ＝ y
  dist-add-ℕ' x y = commutative-dist-ℕ (x +ℕ y) x ∙ dist-add-ℕ x y
```

```agda
abstract
  triangle-equality-dist-ℕ :
    (x y z : ℕ) → (x ≤-ℕ y) → (y ≤-ℕ z) →
    (dist-ℕ x y) +ℕ (dist-ℕ y z) ＝ dist-ℕ x z
  triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
  triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
    ap succ-ℕ (left-unit-law-add-ℕ z)
  triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
    left-successor-law-add-ℕ y (dist-ℕ y z) ∙
    ap succ-ℕ (is-additive-right-inverse-dist-ℕ y z H2)
  triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
    triangle-equality-dist-ℕ x y z H1 H2

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z =
  ( (dist-ℕ x y) +ℕ (dist-ℕ y z) ＝ dist-ℕ x z) +
  ( ( (dist-ℕ y z) +ℕ (dist-ℕ x z) ＝ dist-ℕ x y) +
    ( (dist-ℕ x z) +ℕ (dist-ℕ x y) ＝ dist-ℕ y z))

abstract
  is-total-dist-ℕ :
    (x y z : ℕ) → cases-dist-ℕ x y z
  is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
  is-total-dist-ℕ x y z | inl (inl (pair H1 H2)) =
    inl (triangle-equality-dist-ℕ x y z H1 H2)
  is-total-dist-ℕ x y z | inl (inr (pair H1 H2)) =
    inr
      ( inl
        ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
          ( ( ap ((dist-ℕ x z) +ℕ_) (commutative-dist-ℕ y z)) ∙
            ( triangle-equality-dist-ℕ x z y H1 H2))))
  is-total-dist-ℕ x y z | inr (inl (inl (pair H1 H2))) =
    inr
      ( inl
        ( ( ap ((dist-ℕ y z) +ℕ_) (commutative-dist-ℕ x z)) ∙
          ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
            ( commutative-dist-ℕ y x))))
  is-total-dist-ℕ x y z | inr (inl (inr (pair H1 H2))) =
    inr
      ( inr
        ( ( ap ((dist-ℕ x z) +ℕ_) (commutative-dist-ℕ x y)) ∙
          ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
            ( triangle-equality-dist-ℕ y x z H1 H2))))
  is-total-dist-ℕ x y z | inr (inr (inl (pair H1 H2))) =
    inr
      ( inr
        ( ( ap (_+ℕ (dist-ℕ x y)) (commutative-dist-ℕ x z)) ∙
          ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
            ( commutative-dist-ℕ z y))))
  is-total-dist-ℕ x y z | inr (inr (inr (pair H1 H2))) =
    inl
      ( ( ap-add-ℕ (commutative-dist-ℕ x y) (commutative-dist-ℕ y z)) ∙
        ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
          ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
            ( commutative-dist-ℕ z x))))
```

## Problem statement

Show that `dist-ℕ` is translation invariant and linear:

```text
  dist-ℕ(a + m, a + n)   = dist-ℕ(m, n)
  dist-ℕ(k · m, k · n)   = k · dist-ℕ(m, n).
```

## Solution

```agda
abstract
  translation-invariant-dist-ℕ :
    (k m n : ℕ) → dist-ℕ (k +ℕ m) (k +ℕ n) ＝ dist-ℕ m n
  translation-invariant-dist-ℕ zero-ℕ m n =
    ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
  translation-invariant-dist-ℕ (succ-ℕ k) m n =
    ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
    ( translation-invariant-dist-ℕ k m n)

  translation-invariant-dist-ℕ' :
    (k m n : ℕ) → dist-ℕ (m +ℕ k) (n +ℕ k) ＝ dist-ℕ m n
  translation-invariant-dist-ℕ' k m n =
    ( ap-dist-ℕ (commutative-add-ℕ m k) (commutative-add-ℕ n k)) ∙
    ( translation-invariant-dist-ℕ k m n)
```

```agda
abstract
  left-distributive-mul-dist-ℕ :
    (m n k : ℕ) → k *ℕ (dist-ℕ m n) ＝ dist-ℕ (k *ℕ m) (k *ℕ n)
  left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
  left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) =
    left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ k
  left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
  left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
    ap
      ( dist-ℕ' ((succ-ℕ k) *ℕ (succ-ℕ n)))
      ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
  left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
  left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
    ap
      ( dist-ℕ ((succ-ℕ k) *ℕ (succ-ℕ m)))
      ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
  left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
  left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
    inv
      ( ( ap-dist-ℕ
          ( right-successor-law-mul-ℕ (succ-ℕ k) m)
          ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
        ( ( translation-invariant-dist-ℕ
            ( succ-ℕ k)
            ( (succ-ℕ k) *ℕ m)
            ( (succ-ℕ k) *ℕ n)) ∙
          ( inv (left-distributive-mul-dist-ℕ m n (succ-ℕ k)))))

  left-distributive-mul-dist-ℕ' :
    (m n k : ℕ) → dist-ℕ (k *ℕ m) (k *ℕ n) ＝ k *ℕ (dist-ℕ m n)
  left-distributive-mul-dist-ℕ' m n k =
    inv (left-distributive-mul-dist-ℕ m n k)

  right-distributive-mul-dist-ℕ :
    (x y k : ℕ) → (dist-ℕ x y) *ℕ k ＝ dist-ℕ (x *ℕ k) (y *ℕ k)
  right-distributive-mul-dist-ℕ x y k =
    ( commutative-mul-ℕ (dist-ℕ x y) k) ∙
    ( ( left-distributive-mul-dist-ℕ x y k) ∙
      ( ap-dist-ℕ (commutative-mul-ℕ k x) (commutative-mul-ℕ k y)))
```

## Problem statement

Show that `x + dist-ℕ(x, y) = y` for any `x ≤ y`.

## Solution
