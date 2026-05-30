# Exercise 4.4 Lists

```agda
module exercise-4-4-lists where

open import universe-levels
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

Formalize this.

## Solution

We implement the definition of the type `list` as follows:

```agda

data list {l : Level} (A : Type l) : Type l where
  nil : list A
  cons : A → (list A) → (list A)
  
```

## Problem statement

Formalize the induction principle and the computation rules for `list(A)`.

## Solution

We formalize the induction rules, and their definitions automatically yield the associated computation rules.

```agda

ind-list :
  {l1 l2 : Level} (A : Type l1) → (P : list A → Type l2) → P nil →
  ((a : A) (as : list A) → P as → P (cons a as)) → (x : list A) → P x
ind-list A P Pnil Pcons nil = Pnil
ind-list A P Pnil Pcons (cons a as) = Pcons a as (ind-list A P Pnil Pcons as)

```

## Problem statement

Let `A` and `B` be types, suppose that `b : B`, and consider a binary operation `μ : A → (B → B)`. Define a function

```text

  fold-list(μ) : list(A) → B
  
```

that iterates the operation `μ`, starting with `fold-list(μ, nil) := b`.

## Solution

```agda

fold-list :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (b : B)
  (μ : A → B → B) → list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)

```

## Problem statement

Define the operation

```text

  map-list : (A → B) → (list(A) → list(B))

```

for any two types `A` and `B`.

## Solution

One can use the operation `fold-list` constructed in the previous exercise:

```agda

map-list :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → list A → list B
map-list f = fold-list nil (λ a → cons (f a))

```

Alternatively, below is a solution directly from the definitions:

```agda

map-list2 :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A → B) → list A → list B
map-list2 f nil = nil
map-list2 f (cons a l) = cons (f a) (map-list f l)

```

## Problem statement

Define a function `length-list : list(A) → ℕ`.

## Solution

Again, one can use the `fold-list` operation:

```agda

length-list : {l : Level} {A : Type l} → list A → ℕ
length-list = fold-list 0 (λ a → succ-ℕ)

```

Alternatively, one can proceed directly from the definitions.

```agda

length-list2 : {l : Level} {A : Type l} → list A → ℕ
length-list2 nil = 0
length-list2 (cons x l) = succ-ℕ (length-list l)

```

## Problem statement

Define the functions

```text

  sum-list : list(ℕ) → ℕ
  product-list : list(ℕ) → ℕ

```

where `sum-list` adds all the elements in a list of natural numbers, and `product-list` takes their product.

## Solution

We can implement both using the `fold-list` operation.
Below is the code that defines the sum of a list of natural numbers:

```agda

sum-list : list ℕ → ℕ
sum-list = fold-list 0 add-ℕ

```

The following snippet defines the product of a list of natural numbers:

```agda

prod-list : list ℕ → ℕ
prod-list = fold-list 1 mul-ℕ

```

## Problem statement

Define a function

```text

  concat-list : list(A) → (list(A) → list(A))

```

that concatenates any two lists of elements in A.

## Solution

We present a solution assuming the constructor `cons a al` places the element `a` at the *beginning* of the list.

```agda

concat-list : {l : Level} {A : Type l} → list A → list A → list A
concat-list l1 l2 = (fold-list l2 cons) l1

```

If we instead assume that the constructor `cons a al` places the element `a` at the *end* of the list, then we swap the role of each variable to obtain a solution.

```agda

concat-list2 : {l : Level} {A : Type l} → list A → list A → list A
concat-list2 l1 = fold-list l1 cons

```

## Problem statement

Define a function

```text

  flatten-list : list(list(A)) → list(A)

```

that concatenates all the lists in a list of lists in A.

## Solution

We present a solution using both `fold-list` and `concat-list`, defined earlier.

```agda

flatten-list : {l : Level} {A : Type l} → list (list A) → list A
flatten-list = fold-list nil concat-list

```

An alternative solution is to use `concat-list2` in place of `concat-list`.

## Problem statement

Define a function `reverse-list : list(A) → list(A)` that reverses the order of the elements in any list.

## Solution

The following solution uses `concat-list` with a singleton list to ensure that the newly-added element `a` in `cons a l` appears at the end of the reversed list.

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
