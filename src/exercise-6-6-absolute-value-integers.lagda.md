# Exercise 6.6 Absolute value on the integers

```agda
module exercise-6-6-absolute-value-integers where

open import universe-levels renaming (Type to UU ; Typeω to UUω)
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import path-algebra
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-5-6-successor-predecessor-integers
open import exercise-5-7-group-laws-integers
open import exercise-5-8-ring-laws-integers
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-3-order-natural-numbers
```

## Problem statement

Construct the **absolute value function**

```text
  |_| : ℤ → ℕ
```

and show that it satisfies the following three properties:

1. `(x = 0) ↔ (|x| = 0)`.
2. `|x + y| ≤ |x| + |y|`.
3. `|xy| = |x||y|`.

## Solution

```agda
is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ x = (x ＝ zero-ℤ)

int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos-ℤ n

abstract
  succ-int-ℕ : (x : ℕ) → succ-ℤ (int-ℕ x) ＝ int-ℕ (succ-ℕ x)
  succ-int-ℕ zero-ℕ = refl
  succ-int-ℕ (succ-ℕ x) = refl
```

```agda
abstract
  is-right-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ x +ℤ one-ℤ
  is-right-add-one-succ-ℤ x =
    equational-reasoning
      succ-ℤ x
      ＝ succ-ℤ (x +ℤ zero-ℤ)
        by inv (ap succ-ℤ (right-unit-law-add-ℤ x))
      ＝ x +ℤ one-ℤ
        by inv (right-successor-law-add-ℤ x zero-ℤ)

  is-left-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ one-ℤ +ℤ x
  is-left-add-one-succ-ℤ x = inv (left-successor-law-add-ℤ zero-ℤ x)

  left-add-one-ℤ : (x : ℤ) → one-ℤ +ℤ x ＝ succ-ℤ x
  left-add-one-ℤ x = refl

  right-add-one-ℤ : (x : ℤ) → x +ℤ one-ℤ ＝ succ-ℤ x
  right-add-one-ℤ x = inv (is-right-add-one-succ-ℤ x)
```

```agda
abstract
  is-left-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ neg-one-ℤ +ℤ x
  is-left-add-neg-one-pred-ℤ x =
    inv (left-predecessor-law-add-ℤ zero-ℤ x)

  is-right-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ x +ℤ neg-one-ℤ
  is-right-add-neg-one-pred-ℤ x =
    equational-reasoning
      pred-ℤ x
      ＝ pred-ℤ (x +ℤ zero-ℤ)
        by inv (ap pred-ℤ (right-unit-law-add-ℤ x))
      ＝ x +ℤ neg-one-ℤ
        by inv (right-predecessor-law-add-ℤ x zero-ℤ)

  left-add-neg-one-ℤ : (x : ℤ) → neg-one-ℤ +ℤ x ＝ pred-ℤ x
  left-add-neg-one-ℤ x = refl

  right-add-neg-one-ℤ : (x : ℤ) → x +ℤ neg-one-ℤ ＝ pred-ℤ x
  right-add-neg-one-ℤ x = inv (is-right-add-neg-one-pred-ℤ x)
```

```agda
abs-ℤ : ℤ → ℕ
abs-ℤ (inl x) = succ-ℕ x
abs-ℤ (inr (inl star)) = zero-ℕ
abs-ℤ (inr (inr x)) = succ-ℕ x

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = int-ℕ ∘ abs-ℤ

abs-int-ℕ : (n : ℕ) → abs-ℤ (int-ℕ n) ＝ n
abs-int-ℕ zero-ℕ = refl
abs-int-ℕ (succ-ℕ n) = refl

abs-neg-ℤ : (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
abs-neg-ℤ (inl x) = refl
abs-neg-ℤ (inr (inl star)) = refl
abs-neg-ℤ (inr (inr x)) = refl
```

```agda
eq-abs-ℤ : (x : ℤ) → is-zero-ℕ (abs-ℤ x) → is-zero-ℤ x
eq-abs-ℤ (inr (inl star)) p = refl

abs-eq-ℤ : (x : ℤ) → is-zero-ℤ x → is-zero-ℕ (abs-ℤ x)
abs-eq-ℤ .zero-ℤ refl = refl
```

```agda
predecessor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (pred-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
predecessor-law-abs-ℤ (inl x) =
  refl-leq-ℕ (succ-ℕ x)
predecessor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
predecessor-law-abs-ℤ (inr (inr zero-ℕ)) =
  star
predecessor-law-abs-ℤ (inr (inr (succ-ℕ x))) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)

successor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (succ-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
successor-law-abs-ℤ (inl zero-ℕ) =
  star
successor-law-abs-ℤ (inl (succ-ℕ x)) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)
successor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
successor-law-abs-ℤ (inr (inr x)) =
  refl-leq-ℕ (succ-ℕ x)
```

```agda
subadditive-abs-ℤ :
  (x y : ℤ) → (abs-ℤ (x +ℤ y)) ≤-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
subadditive-abs-ℤ x (inl zero-ℕ) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-add-neg-one-ℤ x))
    ( predecessor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inl (succ-ℕ y)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-predecessor-law-add-ℤ x (inl y)))
    ( transitive-leq-ℕ
      ( abs-ℤ (pred-ℤ (x +ℤ (inl y))))
      ( succ-ℕ (abs-ℤ (x +ℤ (inl y))))
      ( (abs-ℤ x) +ℕ (succ-ℕ (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inl y))
      ( predecessor-law-abs-ℤ (x +ℤ (inl y))))
    ( refl)
subadditive-abs-ℤ x (inr (inl star)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-unit-law-add-ℤ x))
    ( refl-leq-ℕ (abs-ℤ x))
    ( refl)
subadditive-abs-ℤ x (inr (inr zero-ℕ)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-add-one-ℤ x))
    ( successor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inr (inr (succ-ℕ y))) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-successor-law-add-ℤ x (inr (inr y))))
    ( transitive-leq-ℕ
      ( abs-ℤ (succ-ℤ (x +ℤ (inr (inr y)))))
      ( succ-ℕ (abs-ℤ (x +ℤ (inr (inr y)))))
      ( succ-ℕ ((abs-ℤ x) +ℕ (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inr (inr y)))
      ( successor-law-abs-ℤ (x +ℤ (inr (inr y)))))
    ( refl)
```

```agda
abstract
  add-int-ℕ : (x y : ℕ) → (int-ℕ x) +ℤ (int-ℕ y) ＝ int-ℕ (x +ℕ y)
  add-int-ℕ x zero-ℕ = right-unit-law-add-ℤ (int-ℕ x)
  add-int-ℕ x (succ-ℕ y) =
    equational-reasoning
      int-ℕ x +ℤ int-ℕ (succ-ℕ y)
      ＝ int-ℕ x +ℤ succ-ℤ (int-ℕ y)
        by ap ((int-ℕ x) +ℤ_) (inv (succ-int-ℕ y))
      ＝ succ-ℤ (int-ℕ x +ℤ int-ℕ y)
        by right-successor-law-add-ℤ (int-ℕ x) (int-ℕ y)
      ＝ succ-ℤ (int-ℕ (x +ℕ y))
        by ap succ-ℤ (add-int-ℕ x y)
      ＝ int-ℕ (succ-ℕ (x +ℕ y))
        by succ-int-ℕ (x +ℕ y)
```

```agda
explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))
explicit-mul-ℤ (inl x) (inr (inl _)) = zero-ℤ
explicit-mul-ℤ (inl x) (inr (inr y)) = neg-ℤ (int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
explicit-mul-ℤ (inr (inl _)) (inl y) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inl y) = neg-ℤ (int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
explicit-mul-ℤ (inr (inl _)) (inr (inl _)) = zero-ℤ
explicit-mul-ℤ (inr (inl _)) (inr (inr y)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inl _)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = explicit-mul-ℤ y x
```

```agda
abstract
  mul-int-ℕ : (x y : ℕ) → (int-ℕ x) *ℤ (int-ℕ y) ＝ int-ℕ (x *ℕ y)
  mul-int-ℕ zero-ℕ y = refl
  mul-int-ℕ (succ-ℕ x) y =
    ( ap (_*ℤ (int-ℕ y)) (inv (succ-int-ℕ x))) ∙
    ( ( left-successor-law-mul-ℤ (int-ℕ x) (int-ℕ y)) ∙
      ( ( ( ap ((int-ℕ y) +ℤ_) (mul-int-ℕ x y)) ∙
          ( add-int-ℕ y (x *ℕ y))) ∙
        ( ap int-ℕ (commutative-add-ℕ y (x *ℕ y)))))

  compute-mul-ℤ : (x y : ℤ) → x *ℤ y ＝ explicit-mul-ℤ x y
  compute-mul-ℤ (inl zero-ℕ) (inl y) =
    inv (ap int-ℕ (left-unit-law-mul-ℕ (succ-ℕ y)))
  compute-mul-ℤ (inl (succ-ℕ x)) (inl y) =
    ( ( ap ((int-ℕ (succ-ℕ y)) +ℤ_) (compute-mul-ℤ (inl x) (inl y))) ∙
      ( commutative-add-ℤ
        ( int-ℕ (succ-ℕ y))
        ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))))) ∙
    ( add-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)) (succ-ℕ y))
  compute-mul-ℤ (inl zero-ℕ) (inr (inl _)) = refl
  compute-mul-ℤ (inl zero-ℕ) (inr (inr x)) =
    ap inl (inv (left-unit-law-add-ℕ x))
  compute-mul-ℤ (inl (succ-ℕ x)) (inr (inl _)) = right-zero-law-mul-ℤ (inl x)
  compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr y)) =
    ( ( ( ap ((inl y) +ℤ_) (compute-mul-ℤ (inl x) (inr (inr y)))) ∙
        ( inv
          ( distributive-neg-add-ℤ
            ( inr (inr y))
            ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))))) ∙
      ( ap
        ( neg-ℤ)
        ( commutative-add-ℤ
          ( int-ℕ (succ-ℕ y))
          ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))))) ∙
    ( ap neg-ℤ (add-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)) (succ-ℕ y)))
  compute-mul-ℤ (inr (inl _)) (inl y) = refl
  compute-mul-ℤ (inr (inr zero-ℕ)) (inl y) =
    ap inl (inv (left-unit-law-add-ℕ y))
  compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl y) =
    ( ap ((inl y) +ℤ_) (compute-mul-ℤ (inr (inr x)) (inl y))) ∙
    ( ( ( inv
          ( distributive-neg-add-ℤ
            ( inr (inr y))
            ( inr (inr ((x *ℕ (succ-ℕ y)) +ℕ y))))) ∙
        ( ap
          ( neg-ℤ)
          ( ( add-int-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y))) ∙
            ( ap
              ( inr ∘ inr)
              ( left-successor-law-add-ℕ y ((x *ℕ (succ-ℕ y)) +ℕ y)))))) ∙
      ( ap inl (commutative-add-ℕ y ((succ-ℕ x) *ℕ (succ-ℕ y)))))
  compute-mul-ℤ (inr (inl _)) (inr (inl _)) = refl
  compute-mul-ℤ (inr (inl _)) (inr (inr y)) = refl
  compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inl _)) = refl
  compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inl _)) =
    right-zero-law-mul-ℤ (inr (inr (succ-ℕ x)))
  compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inr y)) =
    ap
      ( inr ∘ inr)
      ( inv
        ( ( ap (_+ℕ y) (left-zero-law-mul-ℕ (succ-ℕ y))) ∙
          ( left-unit-law-add-ℕ y)))
  compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr y)) =
    ( ap ((inr (inr y)) +ℤ_) (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) ∙
    ( ( add-int-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y))) ∙
      ( ap int-ℕ (commutative-add-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y)))))
```

```agda
abstract
  multiplicative-abs-ℤ' :
    (x y : ℤ) → abs-ℤ (explicit-mul-ℤ x y) ＝ (abs-ℤ x) *ℕ (abs-ℤ y)
  multiplicative-abs-ℤ' (inl x) (inl y) =
    abs-int-ℕ _
  multiplicative-abs-ℤ' (inl x) (inr (inl star)) =
    inv (right-zero-law-mul-ℕ x)
  multiplicative-abs-ℤ' (inl x) (inr (inr y)) =
    ( abs-neg-ℤ (inl ((x *ℕ (succ-ℕ y)) +ℕ y))) ∙
    ( abs-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
  multiplicative-abs-ℤ' (inr (inl star)) (inl y) =
    refl
  multiplicative-abs-ℤ' (inr (inr x)) (inl y) =
    ( abs-neg-ℤ (inl ((x *ℕ (succ-ℕ y)) +ℕ y))) ∙
    ( abs-int-ℕ (succ-ℕ ((x *ℕ (succ-ℕ y)) +ℕ y)))
  multiplicative-abs-ℤ' (inr (inl star)) (inr (inl star)) =
    refl
  multiplicative-abs-ℤ' (inr (inl star)) (inr (inr x)) =
    refl
  multiplicative-abs-ℤ' (inr (inr x)) (inr (inl star)) =
    inv (right-zero-law-mul-ℕ (succ-ℕ x))
  multiplicative-abs-ℤ' (inr (inr x)) (inr (inr y)) =
    abs-int-ℕ _

  multiplicative-abs-ℤ :
    (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ (abs-ℤ x) *ℕ (abs-ℤ y)
  multiplicative-abs-ℤ x y =
    ap abs-ℤ (compute-mul-ℤ x y) ∙ multiplicative-abs-ℤ' x y
```
