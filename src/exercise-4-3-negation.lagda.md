# Exercise 4.3 Negation

```agda
module exercise-4-3-negation where

open import universe-levels
open import section-4-3-the-empty-type
open import section-4-4-coproducts
```

Let `P` and `Q` be types. We will write `P ↔ Q` for the type of *bi-implication* `P → Q × Q → P`. Use the fact that `¬ P` is defined as the type `P → ∅` of functions from `P` to the empty type to give type theoretic proofs of the constructive tautologies in this exercise.

## Problem statement

For a proposition `P`, `¬ (P × ¬ P)`.

## Solution

```agda 

record Σ {l1 l2 : Level} (A : Type l1) (B : A → Type l2) : Type (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}
{-# INLINE pair #-}

infixr 3 _,_
pattern _,_ a b = pair a b

product : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
product A B = Σ A (λ _ → B)

pair' :
  {l1 l2 : Level} {A : Type l1} {B : Type l2} → A → B → product A B
pair' = pair

infixr 15 _×_
_×_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
_×_ = product

law-of-non-contradiction : {l : Level} {P : Type l} → ¬ (P × ¬ P) 
law-of-non-contradiction (p , np) = np p 

```

## Problem statement

For a type `P`, `¬ (P ↔ ¬ P)`.

## Solution

```agda 

iff : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
iff A B = (A → B) × (B → A) 

infixr 15 _↔_
_↔_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
_↔_ = iff

law-of-non-contradiction' : {l : Level} {P : Type l} → ¬ (P ↔ (¬ P))
law-of-non-contradiction' {P = P} (pnp , npp) = nnp np
    where 
        np : ¬ P  
        np p = (pnp p) p 

        nnp : ¬ ¬ P 
        nnp np = np (npp np)

```

## Problem statement

Construction the unit of the double negation monad: 

For a type `P`, `P → ¬¬ P`.

## Solution

```agda 

double-negation-introduction : {l : Level} {P : Type l} → P → ¬¬ P 
double-negation-introduction p np = np p 
```

## Problem statement

Construction the action on maps of the double negation monad: 

For types `P` and `Q`, `(P → Q) → (¬¬ P → ¬¬ Q)`.

## Solution

```agda 

double-negation-map : {l1 l2 : Level} {P : Type l1} {Q : Type l2} → (P → Q) → (¬¬ P → ¬¬ Q)
double-negation-map pq nnp nq = nnp (λ p → nq (pq p))

```

## Problem statement

Construction the Kleisli map of the double negation monad: 

For types `P` and `Q`, `(P → ¬¬ Q) → (¬¬ P → ¬¬ Q)`.

## Solution

```agda 
double-negation-kleisli-map : {l1 l2 : Level} {P : Type l1} {Q : Type l2} → (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
double-negation-kleisli-map {Q = Q} pnnq nnp = mu (double-negation-map pnnq nnp)
    where 
        mu : ¬¬ ¬¬ Q → ¬¬ Q
        mu nnnnq nq = nnnnq (λ nnq → nnq nq) 
``` 

## Problem statement

For a type `P`, construct a canonical map `¬¬(¬¬ P → P)`.

## Solution

```agda 

not-not-double-negation-elimination : {l : Level} {P : Type l} → ¬¬(¬¬ P → P)
not-not-double-negation-elimination {P = P} ndne = ndne (λ nnp → ex-falso (nnp np))
    where 
        np : ¬ P
        np p = ndne (λ _ → p)
```

## Problem statement

For types `P` and `Q`, construct a canonical map `¬¬ (((P → Q) → P) → P)`.


## Problem statement

For type `P` and `Q`, construct a canonical map `¬¬ ((P → Q) + (Q → P))`.

## Problem statement

For a type `P`, construct a canonical map `¬¬ (P + ¬ P)`.

## Solution

```agda 
not-not-lem : {l : Level} {P : Type l} → ¬¬ (P + (¬ P)) 
not-not-lem {P = P} nlem = {!   !}
    where 
        np : ¬ P
        np p = nlem (inl p)

        nnp : ¬¬ P
        nnp np' = nlem (inr np')

```

## Problem statement

For a type `P`, construct a canonical map `(P + ¬ P) → (¬¬ P → P)`.

## Problem statement

For type `P` and `Q`, show `¬¬ (Q → P) ↔ ((P + ¬ P) → (Q → P))`.    

## Problem Statement

For a type `P`, show that `¬ P` is **double negation stable**: `¬¬¬ P → ¬ P`.

## Problem Statement

For types `P` and `Q`, show that `P → ¬¬ Q` is double negation stable:  

`¬¬(P → ¬¬ Q)→ (P → ¬¬ Q)`

## Problem Statement
For types `P` and `Q`, show that `¬¬ P × ¬¬ Q` is double negation stable:

`¬¬((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)`.

## Problem Statement

For types `P` and `Q`, show `¬¬ (P × Q) ↔ (¬¬ P) × (¬¬ Q)`.

## Problem Statement

For types `P` and `Q`, show `¬¬ (P+Q) ↔ ¬ (¬ P × ¬ Q)`.

## Problem Statement

For types `P` and `Q`, show `¬¬ (P → Q) ↔ (¬¬ P → ¬ Q)`.
