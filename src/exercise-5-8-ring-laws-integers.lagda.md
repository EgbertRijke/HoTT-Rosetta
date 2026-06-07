# Exercise 5.8 Ring laws for integers

```agda
module exercise-5-8-ring-laws-integers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import path-algebra
open import exercise-5-6-successor-predecessor-integers
open import exercise-5-7-group-laws-integers
```

## Problem statement

In this exercise we will show that `ℤ` satisfies the axioms of a **ring**,
using multiplication on the integers.

1. Show that multiplication on `ℤ` satisfies the following laws for `0` and
   `1`:

```text
  0 · x = 0
  1 · x = x
  x · 0 = 0
  x · 1 = x.
```

2. Show that multiplication on `ℤ` satisfies the predecessor and successor
   laws:

```text
  pred-ℤ(x) · y = x · y - y
  succ-ℤ(x) · y = x · y + y
  x · pred-ℤ(y) = x · y - x
  x · succ-ℤ(y) = x · y + x.
```

3. Show that multiplication on `ℤ` distributes over addition, both from the
   left and from the right:

```text
  x · (y + z) = x · y + x · z
  (x + y) · z = x · z + y · z.
```

4. Show that multiplication on `ℤ` is associative and commutative:

```text
  (x · y) · z = x · (y · z)
  x · y = y · x.
```

## Solution

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = (neg-ℤ l) +ℤ (mul-ℤ (inl x) l)
mul-ℤ (inr (inl _)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = l +ℤ (mul-ℤ (inr (inr x)) l)

infixl 40 _*ℤ_
_*ℤ_ = mul-ℤ

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = mul-ℤ y x

ap-mul-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x *ℤ y ＝ x' *ℤ y'
ap-mul-ℤ p q = ap-binary mul-ℤ p q

abstract
  left-zero-law-mul-ℤ : (k : ℤ) → zero-ℤ *ℤ k ＝ zero-ℤ
  left-zero-law-mul-ℤ k = refl

  right-zero-law-mul-ℤ : (k : ℤ) → k *ℤ zero-ℤ ＝ zero-ℤ
  right-zero-law-mul-ℤ (inl zero-ℕ) = refl
  right-zero-law-mul-ℤ (inl (succ-ℕ n)) =
    right-zero-law-mul-ℤ (inl n)
  right-zero-law-mul-ℤ (inr (inl _)) = refl
  right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = refl
  right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) =
    right-zero-law-mul-ℤ (inr (inr n))

abstract
  left-unit-law-mul-ℤ : (k : ℤ) → one-ℤ *ℤ k ＝ k
  left-unit-law-mul-ℤ k = refl

  right-unit-law-mul-ℤ : (k : ℤ) → k *ℤ one-ℤ ＝ k
  right-unit-law-mul-ℤ (inl zero-ℕ) = refl
  right-unit-law-mul-ℤ (inl (succ-ℕ n)) =
    ap ((neg-one-ℤ) +ℤ_) (right-unit-law-mul-ℤ (inl n))
  right-unit-law-mul-ℤ (inr (inl _)) = refl
  right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
    ap (one-ℤ +ℤ_) (right-unit-law-mul-ℤ (inr (inr n)))

abstract
  left-neg-unit-law-mul-ℤ : (k : ℤ) → neg-one-ℤ *ℤ k ＝ neg-ℤ k
  left-neg-unit-law-mul-ℤ k = refl

  right-neg-unit-law-mul-ℤ : (k : ℤ) → k *ℤ neg-one-ℤ ＝ neg-ℤ k
  right-neg-unit-law-mul-ℤ (inl zero-ℕ) = refl
  right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) =
    ap (one-ℤ +ℤ_) (right-neg-unit-law-mul-ℤ (inl n))
  right-neg-unit-law-mul-ℤ (inr (inl _)) = refl
  right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
  right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
    ap (neg-one-ℤ +ℤ_) (right-neg-unit-law-mul-ℤ (inr (inr n)))

abstract
  left-successor-law-mul-ℤ :
    (k l : ℤ) → (succ-ℤ k) *ℤ l ＝ l +ℤ (k *ℤ l)
  left-successor-law-mul-ℤ (inl zero-ℕ) l =
    inv (right-inverse-law-add-ℤ l)
  left-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
    ( ( inv (left-unit-law-add-ℤ ((inl n) *ℤ l))) ∙
      ( ap
        ( _+ℤ ((inl n) *ℤ l))
        ( inv (right-inverse-law-add-ℤ l)))) ∙
    ( associative-add-ℤ l (neg-ℤ l) ((inl n) *ℤ l))
  left-successor-law-mul-ℤ (inr (inl _)) l =
    inv (right-unit-law-add-ℤ l)
  left-successor-law-mul-ℤ (inr (inr n)) l = refl

  left-successor-law-mul-ℤ' :
    (k l : ℤ) → (succ-ℤ k) *ℤ l ＝ (k *ℤ l) +ℤ l
  left-successor-law-mul-ℤ' k l =
    left-successor-law-mul-ℤ k l ∙
    commutative-add-ℤ l (k *ℤ l)

  left-predecessor-law-mul-ℤ :
    (k l : ℤ) → (pred-ℤ k) *ℤ l ＝ (neg-ℤ l) +ℤ (k *ℤ l)
  left-predecessor-law-mul-ℤ (inl n) l = refl
  left-predecessor-law-mul-ℤ (inr (inl _)) l =
    ( left-neg-unit-law-mul-ℤ l) ∙
    ( inv (right-unit-law-add-ℤ (neg-ℤ l)))
  left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l =
    inv (left-inverse-law-add-ℤ l)
  left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
    ( ap
      ( _+ℤ ((in-pos-ℤ x) *ℤ l))
      ( inv (left-inverse-law-add-ℤ l))) ∙
    ( associative-add-ℤ (neg-ℤ l) l ((in-pos-ℤ x) *ℤ l))

  left-predecessor-law-mul-ℤ' :
    (k l : ℤ) → (pred-ℤ k) *ℤ l ＝ (k *ℤ l) +ℤ (neg-ℤ l)
  left-predecessor-law-mul-ℤ' k l =
    left-predecessor-law-mul-ℤ k l ∙
    commutative-add-ℤ (neg-ℤ l) (k *ℤ l)

  right-successor-law-mul-ℤ :
    (k l : ℤ) → k *ℤ (succ-ℤ l) ＝ k +ℤ (k *ℤ l)
  right-successor-law-mul-ℤ (inl zero-ℕ) l = inv (pred-neg-ℤ l)
  right-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
    ( left-predecessor-law-mul-ℤ (inl n) (succ-ℤ l)) ∙
    ( ( ap ((neg-ℤ (succ-ℤ l)) +ℤ_) (right-successor-law-mul-ℤ (inl n) l)) ∙
      ( ( inv (associative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl n) ((inl n) *ℤ l))) ∙
        ( ( ap
            ( _+ℤ ((inl n) *ℤ l))
            { x = (neg-ℤ (succ-ℤ l)) +ℤ (inl n)}
            { y = (inl (succ-ℕ n)) +ℤ (neg-ℤ l)}
            ( ( right-successor-law-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n))) ∙
              ( ( ap succ-ℤ
                  ( commutative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n)))) ∙
                ( ( inv
                    ( right-successor-law-add-ℤ
                      ( inl (succ-ℕ n))
                      ( neg-ℤ (succ-ℤ l)))) ∙
                  ( ap
                    ( (inl (succ-ℕ n)) +ℤ_)
                    ( ( ap succ-ℤ (inv (pred-neg-ℤ l))) ∙
                      ( is-section-pred-ℤ (neg-ℤ l)))))))) ∙
          ( associative-add-ℤ (inl (succ-ℕ n)) (neg-ℤ l) ((inl n) *ℤ l)))))
  right-successor-law-mul-ℤ (inr (inl _)) l = refl
  right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
  right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
    ( left-successor-law-mul-ℤ (in-pos-ℤ n) (succ-ℤ l)) ∙
    ( ( ap ((succ-ℤ l) +ℤ_) (right-successor-law-mul-ℤ (inr (inr n)) l)) ∙
      ( ( inv (associative-add-ℤ (succ-ℤ l) (in-pos-ℤ n) ((in-pos-ℤ n) *ℤ l))) ∙
        ( ( ap
            ( _+ℤ ((in-pos-ℤ n) *ℤ l))
            { x = (succ-ℤ l) +ℤ (in-pos-ℤ n)}
            { y = (in-pos-ℤ (succ-ℕ n)) +ℤ l}
            ( ( left-successor-law-add-ℤ l (in-pos-ℤ n)) ∙
              ( ( ap succ-ℤ (commutative-add-ℤ l (in-pos-ℤ n))) ∙
                ( inv (left-successor-law-add-ℤ (in-pos-ℤ n) l))))) ∙
          ( associative-add-ℤ (inr (inr (succ-ℕ n))) l ((inr (inr n)) *ℤ l)))))

  right-successor-law-mul-ℤ' :
    (k l : ℤ) → k *ℤ (succ-ℤ l) ＝ (k *ℤ l) +ℤ k
  right-successor-law-mul-ℤ' k l =
    right-successor-law-mul-ℤ k l ∙
    commutative-add-ℤ k (k *ℤ l)

  right-predecessor-law-mul-ℤ :
    (k l : ℤ) → k *ℤ (pred-ℤ l) ＝ (neg-ℤ k) +ℤ (k *ℤ l)
  right-predecessor-law-mul-ℤ (inl zero-ℕ) l =
    ( left-neg-unit-law-mul-ℤ (pred-ℤ l)) ∙
    ( neg-pred-ℤ l)
  right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l =
    ( left-predecessor-law-mul-ℤ (inl n) (pred-ℤ l)) ∙
    ( ( ap ((neg-ℤ (pred-ℤ l)) +ℤ_) (right-predecessor-law-mul-ℤ (inl n) l)) ∙
      ( ( inv
          ( associative-add-ℤ (neg-ℤ (pred-ℤ l)) (in-pos-ℤ n) ((inl n) *ℤ l))) ∙
        ( ( ap
            ( _+ℤ ((inl n) *ℤ l))
            { x = (neg-ℤ (pred-ℤ l)) +ℤ (inr (inr n))}
            { y = (neg-ℤ (inl (succ-ℕ n))) +ℤ (neg-ℤ l)}
            ( ( ap (_+ℤ (in-pos-ℤ n)) (neg-pred-ℤ l)) ∙
              ( ( left-successor-law-add-ℤ (neg-ℤ l) (in-pos-ℤ n)) ∙
                ( ( ap succ-ℤ (commutative-add-ℤ (neg-ℤ l) (in-pos-ℤ n))) ∙
                  ( inv (left-successor-law-add-ℤ (in-pos-ℤ n) (neg-ℤ l))))))) ∙
          ( associative-add-ℤ (in-pos-ℤ (succ-ℕ n)) (neg-ℤ l) ((inl n) *ℤ l)))))
  right-predecessor-law-mul-ℤ (inr (inl _)) l = refl
  right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
  right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
    ( left-successor-law-mul-ℤ (in-pos-ℤ n) (pred-ℤ l)) ∙
    ( ( ap ((pred-ℤ l) +ℤ_) (right-predecessor-law-mul-ℤ (inr (inr n)) l)) ∙
      ( ( inv (associative-add-ℤ (pred-ℤ l) (inl n) ((inr (inr n)) *ℤ l))) ∙
        ( ( ap
            ( _+ℤ ((in-pos-ℤ n) *ℤ l))
            { x = (pred-ℤ l) +ℤ (inl n)}
            { y = (neg-ℤ (in-pos-ℤ (succ-ℕ n))) +ℤ l}
            ( ( left-predecessor-law-add-ℤ l (inl n)) ∙
              ( ( ap pred-ℤ (commutative-add-ℤ l (inl n))) ∙
                ( inv (left-predecessor-law-add-ℤ (inl n) l))))) ∙
          ( associative-add-ℤ (inl (succ-ℕ n)) l ((inr (inr n)) *ℤ l)))))

  right-predecessor-law-mul-ℤ' :
    (k l : ℤ) → k *ℤ (pred-ℤ l) ＝ (k *ℤ l) +ℤ (neg-ℤ k)
  right-predecessor-law-mul-ℤ' k l =
    right-predecessor-law-mul-ℤ k l ∙
    commutative-add-ℤ (neg-ℤ k) (k *ℤ l)

abstract
  right-distributive-mul-add-ℤ :
    (k l m : ℤ) → (k +ℤ l) *ℤ m ＝ (k *ℤ m) +ℤ (l *ℤ m)
  right-distributive-mul-add-ℤ (inl zero-ℕ) l m =
    ( left-predecessor-law-mul-ℤ l m) ∙
    ( ap
      ( _+ℤ (l *ℤ m))
      ( inv
        ( ( left-predecessor-law-mul-ℤ zero-ℤ m) ∙
          ( right-unit-law-add-ℤ (neg-ℤ m)))))
  right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m =
    ( left-predecessor-law-mul-ℤ ((inl x) +ℤ l) m) ∙
    ( ( ap ((neg-ℤ m) +ℤ_) (right-distributive-mul-add-ℤ (inl x) l m)) ∙
      ( inv (associative-add-ℤ (neg-ℤ m) ((inl x) *ℤ m) (l *ℤ m))))
  right-distributive-mul-add-ℤ (inr (inl _)) l m = refl
  right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m =
    left-successor-law-mul-ℤ l m
  right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m =
    ( left-successor-law-mul-ℤ ((in-pos-ℤ n) +ℤ l) m) ∙
    ( ( ap (m +ℤ_) (right-distributive-mul-add-ℤ (inr (inr n)) l m)) ∙
      ( inv (associative-add-ℤ m ((in-pos-ℤ n) *ℤ m) (l *ℤ m))))

abstract
  left-negative-law-mul-ℤ :
    (k l : ℤ) → (neg-ℤ k) *ℤ l ＝ neg-ℤ (k *ℤ l)
  left-negative-law-mul-ℤ (inl zero-ℕ) l =
    ( left-unit-law-mul-ℤ l) ∙
    ( inv (neg-neg-ℤ l))
  left-negative-law-mul-ℤ (inl (succ-ℕ n)) l =
    ( ap (_*ℤ l) (neg-pred-ℤ (inl n))) ∙
    ( ( left-successor-law-mul-ℤ (neg-ℤ (inl n)) l) ∙
      ( ( ap (l +ℤ_) (left-negative-law-mul-ℤ (inl n) l)) ∙
        ( right-negative-law-add-ℤ l ((inl n) *ℤ l))))
  left-negative-law-mul-ℤ (inr (inl _)) l = refl
  left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
  left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
    ( left-predecessor-law-mul-ℤ (inl n) l) ∙
    ( ( ap ((neg-ℤ l) +ℤ_) (left-negative-law-mul-ℤ (inr (inr n)) l)) ∙
      ( inv (distributive-neg-add-ℤ l ((in-pos-ℤ n) *ℤ l))))

abstract
  associative-mul-ℤ :
    (k l m : ℤ) → (k *ℤ l) *ℤ m ＝ k *ℤ (l *ℤ m)
  associative-mul-ℤ (inl zero-ℕ) l m =
    left-negative-law-mul-ℤ l m
  associative-mul-ℤ (inl (succ-ℕ n)) l m =
    ( right-distributive-mul-add-ℤ (neg-ℤ l) ((inl n) *ℤ l) m) ∙
    ( ( ap (((neg-ℤ l) *ℤ m) +ℤ_) (associative-mul-ℤ (inl n) l m)) ∙
      ( ap
        ( _+ℤ ((inl n) *ℤ (l *ℤ m)))
        ( left-negative-law-mul-ℤ l m)))
  associative-mul-ℤ (inr (inl _)) l m = refl
  associative-mul-ℤ (inr (inr zero-ℕ)) l m = refl
  associative-mul-ℤ (inr (inr (succ-ℕ n))) l m =
    ( right-distributive-mul-add-ℤ l ((in-pos-ℤ n) *ℤ l) m) ∙
    ( ap ((l *ℤ m) +ℤ_) (associative-mul-ℤ (inr (inr n)) l m))

abstract
  commutative-mul-ℤ :
    (k l : ℤ) → k *ℤ l ＝ l *ℤ k
  commutative-mul-ℤ (inl zero-ℕ) l = inv (right-neg-unit-law-mul-ℤ l)
  commutative-mul-ℤ (inl (succ-ℕ n)) l =
    ( ap ((neg-ℤ l) +ℤ_) (commutative-mul-ℤ (inl n) l)) ∙
    ( inv (right-predecessor-law-mul-ℤ l (inl n)))
  commutative-mul-ℤ (inr (inl _)) l = inv (right-zero-law-mul-ℤ l)
  commutative-mul-ℤ (inr (inr zero-ℕ)) l = inv (right-unit-law-mul-ℤ l)
  commutative-mul-ℤ (inr (inr (succ-ℕ n))) l =
    ( ap (l +ℤ_) (commutative-mul-ℤ (inr (inr n)) l)) ∙
    ( inv (right-successor-law-mul-ℤ l (in-pos-ℤ n)))

abstract
  left-distributive-mul-add-ℤ :
    (m k l : ℤ) → m *ℤ (k +ℤ l) ＝ (m *ℤ k) +ℤ (m *ℤ l)
  left-distributive-mul-add-ℤ m k l =
    ( commutative-mul-ℤ m (k +ℤ l)) ∙
    ( right-distributive-mul-add-ℤ k l m) ∙
    ( ap-add-ℤ (commutative-mul-ℤ k m) (commutative-mul-ℤ l m))
```
