# Exercise 5.7 Group laws for integers

```agda
module exercise-5-7-group-laws-integers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import path-algebra
open import exercise-5-6-successor-predecessor-integers
```

## Problem statement

In this exercise we will show that the laws for abelian groups hold for addition
on the integers, using the group operations on `ℤ`.

1. Show that addition satisfies the left and right unit laws, i.e., show that

```text
  0 + x = x
  x + 0 = x.
```

2. Show that the following successor and predecessor laws hold for addition on
   `ℤ`.

```text
  pred-ℤ(x) + y = pred-ℤ(x + y)
  succ-ℤ(x) + y = succ-ℤ(x + y)
  x + pred-ℤ(y) = pred-ℤ(x + y)
  x + succ-ℤ(y) = succ-ℤ(x + y).
```

3. Use part 2 to show that addition on the integers is associative and
   commutative:

```text
  (x + y) + z = x + (y + z)
  x + y = y + x.
```

4. Show that addition satisfies the left and right inverse laws:

```text
  (-x) + x = 0
  x + (-x) = 0.
```


## Solution

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x

abstract
  neg-neg-ℤ : (k : ℤ) → neg-ℤ (neg-ℤ k) ＝ k
  neg-neg-ℤ (inl n) = refl
  neg-neg-ℤ (inr (inl star)) = refl
  neg-neg-ℤ (inr (inr n)) = refl

abstract
  neg-pred-ℤ : (k : ℤ) → neg-ℤ (pred-ℤ k) ＝ succ-ℤ (neg-ℤ k)
  neg-pred-ℤ (inl x) = refl
  neg-pred-ℤ (inr (inl star)) = refl
  neg-pred-ℤ (inr (inr zero-ℕ)) = refl
  neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl

abstract
  neg-succ-ℤ : (x : ℤ) → neg-ℤ (succ-ℤ x) ＝ pred-ℤ (neg-ℤ x)
  neg-succ-ℤ (inl zero-ℕ) = refl
  neg-succ-ℤ (inl (succ-ℕ x)) = refl
  neg-succ-ℤ (inr (inl star)) = refl
  neg-succ-ℤ (inr (inr x)) = refl

abstract
  pred-neg-ℤ :
    (k : ℤ) → pred-ℤ (neg-ℤ k) ＝ neg-ℤ (succ-ℤ k)
  pred-neg-ℤ (inl zero-ℕ) = refl
  pred-neg-ℤ (inl (succ-ℕ x)) = refl
  pred-neg-ℤ (inr (inl star)) = refl
  pred-neg-ℤ (inr (inr x)) = refl

add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x

infixl 35 _+ℤ_
_+ℤ_ = add-ℤ

ap-add-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x +ℤ y ＝ x' +ℤ y'
ap-add-ℤ p q = ap-binary add-ℤ p q

abstract
  left-unit-law-add-ℤ : (k : ℤ) → zero-ℤ +ℤ k ＝ k
  left-unit-law-add-ℤ k = refl

  right-unit-law-add-ℤ : (k : ℤ) → k +ℤ zero-ℤ ＝ k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))

abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → pred-ℤ x +ℤ y ＝ pred-ℤ (x +ℤ y)
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    inv (is-retraction-pred-ℤ y)
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    inv (is-retraction-pred-ℤ ((inr (inr x)) +ℤ y))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → x +ℤ pred-ℤ y ＝ pred-ℤ (x +ℤ y)
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    equational-reasoning
      succ-ℤ (pred-ℤ n)
      ＝ n
        by is-section-pred-ℤ n
      ＝ pred-ℤ (succ-ℤ n)
        by inv (is-retraction-pred-ℤ n)
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ n)
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ n))
        by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)
      ＝ inr (inr x) +ℤ n
        by is-section-pred-ℤ ((inr (inr x)) +ℤ n)
      ＝ pred-ℤ (succ-ℤ (inr (inr x) +ℤ n))
        by inv (is-retraction-pred-ℤ ((inr (inr x)) +ℤ n))

abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → succ-ℤ x +ℤ y ＝ succ-ℤ (x +ℤ y)
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    inv (is-section-pred-ℤ y)
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      inl x +ℤ y
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))
        by inv (is-section-pred-ℤ ((inl x) +ℤ y))
      ＝ succ-ℤ (pred-ℤ (inl x) +ℤ y)
        by ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → x +ℤ succ-ℤ y ＝ succ-ℤ (x +ℤ y)
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      pred-ℤ (succ-ℤ y)
      ＝ y
        by is-retraction-pred-ℤ y
      ＝ succ-ℤ (pred-ℤ y)
        by inv (is-section-pred-ℤ y)
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      pred-ℤ (inl x +ℤ succ-ℤ y)
      ＝ pred-ℤ (succ-ℤ (inl x +ℤ y))
        by ap pred-ℤ (right-successor-law-add-ℤ (inl x) y)
      ＝ inl x +ℤ y
        by is-retraction-pred-ℤ ((inl x) +ℤ y)
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))
        by inv (is-section-pred-ℤ ((inl x) +ℤ y))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)

abstract
  associative-add-ℤ :
    (x y z : ℤ) → ((x +ℤ y) +ℤ z) ＝ (x +ℤ (y +ℤ z))
  associative-add-ℤ (inl zero-ℕ) y z =
    equational-reasoning
      (neg-one-ℤ +ℤ y) +ℤ z
      ＝ (pred-ℤ (zero-ℤ +ℤ y)) +ℤ z
        by ap (_+ℤ z) (left-predecessor-law-add-ℤ zero-ℤ y)
      ＝ pred-ℤ (y +ℤ z)
        by left-predecessor-law-add-ℤ y z
      ＝ neg-one-ℤ +ℤ (y +ℤ z)
        by inv (left-predecessor-law-add-ℤ zero-ℤ (y +ℤ z))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    equational-reasoning
      (pred-ℤ (inl x) +ℤ y) +ℤ z
      ＝ pred-ℤ (inl x +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-predecessor-law-add-ℤ (inl x) y)
      ＝ pred-ℤ ((inl x +ℤ y) +ℤ z)
        by left-predecessor-law-add-ℤ ((inl x) +ℤ y) z
      ＝ pred-ℤ (inl x +ℤ (y +ℤ z))
        by ap pred-ℤ (associative-add-ℤ (inl x) y z)
      ＝ pred-ℤ (inl x) +ℤ (y +ℤ z)
        by inv (left-predecessor-law-add-ℤ (inl x) (y +ℤ z))
  associative-add-ℤ (inr (inl star)) y z =
    refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    equational-reasoning
      (one-ℤ +ℤ y) +ℤ z
      ＝ succ-ℤ (zero-ℤ +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-successor-law-add-ℤ zero-ℤ y)
      ＝ succ-ℤ (y +ℤ z)
        by left-successor-law-add-ℤ y z
      ＝ one-ℤ +ℤ (y +ℤ z)
        by inv (left-successor-law-add-ℤ zero-ℤ (y +ℤ z))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    equational-reasoning
      (succ-ℤ (inr (inr x)) +ℤ y) +ℤ z
      ＝ succ-ℤ (inr (inr x) +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-successor-law-add-ℤ (inr (inr x)) y)
      ＝ succ-ℤ ((inr (inr x) +ℤ y) +ℤ z)
        by left-successor-law-add-ℤ ((inr (inr x)) +ℤ y) z
      ＝ succ-ℤ (inr (inr x) +ℤ (y +ℤ z))
        by ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z)
      ＝ succ-ℤ (inr (inr x)) +ℤ (y +ℤ z)
        by inv (left-successor-law-add-ℤ (inr (inr x)) (y +ℤ z))

abstract
  commutative-add-ℤ : (x y : ℤ) → x +ℤ y ＝ y +ℤ x
  commutative-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      neg-one-ℤ +ℤ y
      ＝ pred-ℤ (zero-ℤ +ℤ y)
        by left-predecessor-law-add-ℤ zero-ℤ y
      ＝ pred-ℤ (y +ℤ zero-ℤ)
        by inv (ap pred-ℤ (right-unit-law-add-ℤ y))
      ＝ y +ℤ neg-one-ℤ
        by inv (right-predecessor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      (inl (succ-ℕ x)) +ℤ y
      ＝ pred-ℤ (y +ℤ (inl x))
        by ap pred-ℤ (commutative-add-ℤ (inl x) y)
      ＝ y +ℤ (inl (succ-ℕ x))
        by inv (right-predecessor-law-add-ℤ y (inl x))
  commutative-add-ℤ (inr (inl star)) y =
    inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    equational-reasoning
      succ-ℤ y
      ＝ succ-ℤ (y +ℤ zero-ℤ)
        by inv (ap succ-ℤ (right-unit-law-add-ℤ y))
      ＝ y +ℤ one-ℤ
        by inv (right-successor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    equational-reasoning
      succ-ℤ ((inr (inr x)) +ℤ y)
      ＝ succ-ℤ (y +ℤ (inr (inr x)))
        by ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y)
      ＝ y +ℤ (succ-ℤ (inr (inr x)))
        by inv (right-successor-law-add-ℤ y (inr (inr x)))

abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → neg-ℤ x +ℤ x ＝ zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ (inl x))
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ inl x))
        by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x))
      ＝ inr (inr x) +ℤ inl x
        by is-section-pred-ℤ ((inr (inr x)) +ℤ (inl x))
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ (inl x)
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    equational-reasoning
      neg-ℤ (inr (inr x)) +ℤ inr (inr x)
      ＝ inr (inr x) +ℤ inl x
        by commutative-add-ℤ (inl x) (inr (inr x))
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ (inl x)

  right-inverse-law-add-ℤ :
    (x : ℤ) → x +ℤ neg-ℤ x ＝ zero-ℤ
  right-inverse-law-add-ℤ x =
    equational-reasoning
      x +ℤ neg-ℤ x
      ＝ neg-ℤ x +ℤ x
        by commutative-add-ℤ x (neg-ℤ x)
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ x

abstract
  right-negative-law-add-ℤ :
    (k l : ℤ) → k +ℤ neg-ℤ l ＝ neg-ℤ (neg-ℤ k +ℤ l)
  right-negative-law-add-ℤ (inl zero-ℕ) l =
    equational-reasoning
      neg-one-ℤ +ℤ neg-ℤ l
      ＝ pred-ℤ (zero-ℤ +ℤ neg-ℤ l)
        by left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)
      ＝ neg-ℤ (succ-ℤ l)
        by pred-neg-ℤ l
  right-negative-law-add-ℤ (inl (succ-ℕ x)) l =
    equational-reasoning
      pred-ℤ (inl x) +ℤ neg-ℤ l
      ＝ pred-ℤ (inl x +ℤ neg-ℤ l)
        by left-predecessor-law-add-ℤ (inl x) (neg-ℤ l)
      ＝ pred-ℤ (neg-ℤ (neg-ℤ (inl x) +ℤ l))
        by ap pred-ℤ (right-negative-law-add-ℤ (inl x) l)
      ＝ neg-ℤ (succ-ℤ (inr (inr x) +ℤ l))
        by pred-neg-ℤ (inr (inr x) +ℤ l)
  right-negative-law-add-ℤ (inr (inl star)) l =
    refl
  right-negative-law-add-ℤ (inr (inr zero-ℕ)) l =
    inv (neg-pred-ℤ l)
  right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l =
    equational-reasoning
      succ-ℤ (in-pos-ℤ n) +ℤ neg-ℤ l
      ＝ succ-ℤ (in-pos-ℤ n +ℤ neg-ℤ l)
        by left-successor-law-add-ℤ (in-pos-ℤ n) (neg-ℤ l)
      ＝ succ-ℤ (neg-ℤ (neg-ℤ (inr (inr n)) +ℤ l))
        by ap succ-ℤ (right-negative-law-add-ℤ (inr (inr n)) l)
      ＝ neg-ℤ (pred-ℤ ((inl n) +ℤ l))
        by inv (neg-pred-ℤ ((inl n) +ℤ l))

abstract
  distributive-neg-add-ℤ :
    (k l : ℤ) → neg-ℤ (k +ℤ l) ＝ neg-ℤ k +ℤ neg-ℤ l
  distributive-neg-add-ℤ (inl zero-ℕ) l =
    equational-reasoning
      neg-ℤ (inl zero-ℕ +ℤ l)
      ＝ neg-ℤ (pred-ℤ (zero-ℤ +ℤ l))
        by ap neg-ℤ (left-predecessor-law-add-ℤ zero-ℤ l)
      ＝ neg-ℤ (inl zero-ℕ) +ℤ neg-ℤ l
        by neg-pred-ℤ l
  distributive-neg-add-ℤ (inl (succ-ℕ n)) l =
    equational-reasoning
      neg-ℤ (pred-ℤ (inl n +ℤ l))
      ＝ succ-ℤ (neg-ℤ (inl n +ℤ l))
        by neg-pred-ℤ (inl n +ℤ l)
      ＝ succ-ℤ (neg-ℤ (inl n) +ℤ neg-ℤ l)
        by ap succ-ℤ (distributive-neg-add-ℤ (inl n) l)
      ＝ neg-ℤ (pred-ℤ (inl n)) +ℤ neg-ℤ l
        by ap (_+ℤ (neg-ℤ l)) (inv (neg-pred-ℤ (inl n)))
  distributive-neg-add-ℤ (inr (inl star)) l =
    refl
  distributive-neg-add-ℤ (inr (inr zero-ℕ)) l =
    inv (pred-neg-ℤ l)
  distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l =
    equational-reasoning
      neg-ℤ (succ-ℤ (in-pos-ℤ n +ℤ l))
      ＝ pred-ℤ (neg-ℤ (in-pos-ℤ n +ℤ l))
        by inv (pred-neg-ℤ (in-pos-ℤ n +ℤ l))
      ＝ pred-ℤ (neg-ℤ (inr (inr n)) +ℤ neg-ℤ l)
        by ap pred-ℤ (distributive-neg-add-ℤ (inr (inr n)) l)
```
