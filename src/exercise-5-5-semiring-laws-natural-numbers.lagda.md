# Exercise 5.5 Semiring laws for natural numbers

```agda
module exercise-5-5-semiring-laws-natural-numbers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
```

## Problem statement

In this exercise we show that the operations of addition and multiplication on
the natural numbers satisfy the laws of a commutative **semiring**.

1. Show that multiplication satisfies the following laws:

```text
  m · 0 = 0
  m · 1 = m
  m · succ-ℕ(n) = m + m · n
  0 · m = 0
  1 · m = m
  succ-ℕ(m) · n = m · n + n.
```

2. Show that multiplication on `ℕ` is commutative:

```text
  m · n = n · m.
```

3. Show that multiplication on `ℕ` distributes over addition from the left and
   from the right, i.e., show that we have identifications

```text
  m · (n + k) = m · n + m · k
  (m + n) · k = m · k + n · k.
```

4. Show that multiplication on `ℕ` is associative:

```text
  (m · n) · k = m · (n · k).
```


## Solution

```agda
abstract
  left-zero-law-mul-ℕ :
    (x : ℕ) → zero-ℕ *ℕ x ＝ zero-ℕ
  left-zero-law-mul-ℕ x = refl

  right-zero-law-mul-ℕ :
    (x : ℕ) → x *ℕ zero-ℕ ＝ zero-ℕ
  right-zero-law-mul-ℕ zero-ℕ = refl
  right-zero-law-mul-ℕ (succ-ℕ x) =
    ( right-unit-law-add-ℕ (x *ℕ zero-ℕ)) ∙ (right-zero-law-mul-ℕ x)

abstract
  right-unit-law-mul-ℕ :
    (x : ℕ) → x *ℕ 1 ＝ x
  right-unit-law-mul-ℕ zero-ℕ = refl
  right-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (right-unit-law-mul-ℕ x)

  left-unit-law-mul-ℕ :
    (x : ℕ) → 1 *ℕ x ＝ x
  left-unit-law-mul-ℕ zero-ℕ = refl
  left-unit-law-mul-ℕ (succ-ℕ x) = ap succ-ℕ (left-unit-law-mul-ℕ x)

abstract
  left-successor-law-mul-ℕ :
    (x y : ℕ) → (succ-ℕ x) *ℕ y ＝ (x *ℕ y) +ℕ y
  left-successor-law-mul-ℕ x y = refl

  right-successor-law-mul-ℕ :
    (x y : ℕ) → x *ℕ (succ-ℕ y) ＝ x +ℕ (x *ℕ y)
  right-successor-law-mul-ℕ zero-ℕ y = refl
  right-successor-law-mul-ℕ (succ-ℕ x) y =
    ( ( ap (λ t → succ-ℕ (t +ℕ y)) (right-successor-law-mul-ℕ x y)) ∙
      ( ap succ-ℕ (associative-add-ℕ x (x *ℕ y) y))) ∙
    ( inv (left-successor-law-add-ℕ x ((x *ℕ y) +ℕ y)))

abstract
  commutative-mul-ℕ :
    (x y : ℕ) → x *ℕ y ＝ y *ℕ x
  commutative-mul-ℕ zero-ℕ y = inv (right-zero-law-mul-ℕ y)
  commutative-mul-ℕ (succ-ℕ x) y =
    ( commutative-add-ℕ (x *ℕ y) y) ∙
    ( ( ap (y +ℕ_) (commutative-mul-ℕ x y)) ∙
      ( inv (right-successor-law-mul-ℕ y x)))

abstract
  left-distributive-mul-add-ℕ :
    (x y z : ℕ) → x *ℕ (y +ℕ z) ＝ (x *ℕ y) +ℕ (x *ℕ z)
  left-distributive-mul-add-ℕ zero-ℕ y z = refl
  left-distributive-mul-add-ℕ (succ-ℕ x) y z =
    ( left-successor-law-mul-ℕ x (y +ℕ z)) ∙
    ( ( ap (_+ℕ (y +ℕ z)) (left-distributive-mul-add-ℕ x y z)) ∙
      ( ( associative-add-ℕ (x *ℕ y) (x *ℕ z) (y +ℕ z)) ∙
        ( ( ap
            ( ( x *ℕ y) +ℕ_)
            ( ( inv (associative-add-ℕ (x *ℕ z) y z)) ∙
              ( ( ap (_+ℕ z) (commutative-add-ℕ (x *ℕ z) y)) ∙
                ( associative-add-ℕ y (x *ℕ z) z)))) ∙
          ( inv (associative-add-ℕ (x *ℕ y) y ((x *ℕ z) +ℕ z))))))

  right-distributive-mul-add-ℕ :
    (x y z : ℕ) → (x +ℕ y) *ℕ z ＝ (x *ℕ z) +ℕ (y *ℕ z)
  right-distributive-mul-add-ℕ x y z =
    ( commutative-mul-ℕ (x +ℕ y) z) ∙
    ( ( left-distributive-mul-add-ℕ z x y) ∙
      ( ( ap (_+ℕ (z *ℕ y)) (commutative-mul-ℕ z x)) ∙
        ( ap ((x *ℕ z) +ℕ_) (commutative-mul-ℕ z y))))

abstract
  associative-mul-ℕ :
    (x y z : ℕ) → (x *ℕ y) *ℕ z ＝ x *ℕ (y *ℕ z)
  associative-mul-ℕ zero-ℕ y z = refl
  associative-mul-ℕ (succ-ℕ x) y z =
    ( right-distributive-mul-add-ℕ (x *ℕ y) y z) ∙
    ( ap (_+ℕ (y *ℕ z)) (associative-mul-ℕ x y z))
```
