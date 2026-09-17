# Exercise 4.4 Lists

```agda
module exercise-4-4-lists where

open import universe-levels renaming (UU to Type)
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers 
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
```

## Problem statement

For any type `A`, we can define the type `list(A)` of **lists** of elements of `A` as the inductive type with constructors

```text
  nil : list(A)
  const : A → (list(A) → list(A))
```

```agda
data list {l : Level} (A : Type l) : Type l where
  nil : list A
  cons : A → list A → list A

{-# BUILTIN LIST list #-}
```

### Exercise 4.4(a)

Write down the induction principle and the computation rules for `list(A)`.

### Exercise 4.4(b)

Let `A` and `B` be types, suppose that `b : B`, and consider a binary operation `μ : A → (B → B)`. Define a function

```text
  fold-list(μ) : list(A) → B
```

that iterates the operation `μ`, starting with `fold-list(μ,nil) ≔ b`.

### Exercise 4.4(c)

Define the operation

```text
  map-list : (A → B) → (list(A) → list(B))
```

for any two types `A` and `B`.

### Exercise 4.4(d)

Define a function `length-list : list(A) → ℕ`.

### Exercise 4.4(e)

Define the functions

```text
      sum-list : list(ℕ) → ℕ,
  product-list : list(ℕ) → ℕ,
```

where sum-list adds all the elements in a list of natural numbers, and product-list takes their product.

### Exercise 4.4(f)

Define a function

```text
  concat-list : list(A) → (list(A) → list(A))
```

that concatenates any two lists of elements of `A`.

### Exercise 4.4(g)

Define a function

```text
  flatten-list : list(list(A)) → list(A)
```

that concatenates all the lists in a list of lists in `A`.

### Exercise 4.4(h)

Define a function `reverse-list : list(A) → list(A)` that reverses the order of the elements in any list.

## Solutions

### Exercise 4.4(a)

```agda
ind-list :
  {l1 l2 : Level} (A : Type l1) → (P : list A → Type l2) → P nil →
  ((a : A) (as : list A) → P as → P (cons a as)) → (x : list A) → P x
ind-list A P Pnil Pcons nil = Pnil
ind-list A P Pnil Pcons (cons a as) = Pcons a as (ind-list A P Pnil Pcons as)
```

### Exercise 4.4(b)

```agda
fold-list :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (b : B)
  (μ : A → B → B) → list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)
```

### Exercise 4.4(c)

```agda
map-list :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → list A → list B
map-list f = fold-list nil (λ a → cons (f a))
```

### Exercise 4.4(d)

```agda
length-list : {l : Level} {A : Type l} → list A → ℕ
length-list = fold-list 0 (λ a → succ-ℕ)
```

### Exercise 4.4(e)

```agda
sum-list : list ℕ → ℕ
sum-list = fold-list 0 add-ℕ

prod-list : list ℕ → ℕ
prod-list = fold-list 1 mul-ℕ
```

### Exercise 4.4(f)

```agda
concat-list : {l : Level} {A : Type l} → list A → list A → list A
concat-list l1 l2 = (fold-list l2 cons) l1
```

### Exercise 4.4(g)

```agda
flatten-list : {l : Level} {A : Type l} → list (list A) → list A
flatten-list = fold-list nil concat-list
```

### Exercise 4.4(h)

```agda
reverse-list : {l : Level} {A : Type} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = concat-list l (cons a nil)
```

## Agda-unimath sources

- The definition of the type of lists, its induction principle, the `fold-list` operation, and the `length-list` operation are implemented in `lists.lists`.
- The definition of `map-list` is implemented in `lists.functoriality-lists`.
- The definition of list concatenation `concat-list` is implemented in `lists.concatenation-lists`.
- The definition of list reversal `reverse-list` is implemented in `lists.reversing-lists`.
