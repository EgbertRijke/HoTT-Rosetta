# Exercise 4.1

```agda
module exercise-4-1-arithmetic-operations-integers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
```

## Problem statements

### Exercise 4.1(a)

Define the predecessor function `pred : ℤ → ℤ`.

### Exercise 4.1(b)

Define the group operations

```text
  add : ℤ → (ℤ → ℤ)
  neg : ℤ → ℤ.
```

### Exercise 4.1(c)

Define the multiplication operation `mul : ℤ → (ℤ → ℤ)`.

## Solutions

### Exercise 4.1(a)

```agda
pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)
```

### Exercise 4.1(b)

```agda
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

neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

### Exercise 4.1(c)

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
```
