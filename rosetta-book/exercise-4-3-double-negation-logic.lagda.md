# Exercise 4.3

```agda
module exercise-4-3-double-negation-logic where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
```

## Problem statement

Let `P` and `Q` be types.
We will write `P ↔ Q` for the type of **bi-implications** `(P → Q) × (Q → P)`.
Use the fact that `¬ P` is defined as the type `P → empty` of functions from `P` to the empty type to give type theoretic proofs of the constructive tautologies in this exercise.

```agda
iff : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
iff A B = (A → B) × (B → A) 

infixr 15 _↔_

_↔_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
_↔_ = iff

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (H : A ↔ B)
  where

  forward-implication : A → B
  forward-implication = pr1 H

  backward-implication : B → A
  backward-implication = pr2 H
```

### Exercise 4.3(a)

Show that

1.  `¬ (P × ¬ P)`

2.  `¬ (P ↔ ¬ P)`.

### Exercise 4.3(b)

Construct the following maps in the structure of the **double negation monad**:

1.  `P → ¬¬ P`

2.  `(P → Q) → (¬¬ P → ¬¬ Q)`

3.  `(P → ¬¬ Q) → (¬¬ P → ¬¬ Q)`.

### Exercise 4.3(c)

Prove that the following double negations of classical laws hold:

1.  `¬¬ (¬¬ P → P)`

2.  `¬¬ (((P → Q) → P) → P)`

3.  `¬¬ ((P → Q) + (Q → P))`

4.  `¬¬ (P + ¬ P)`.

### Exercise 4.3(d)

Show that

1.  `(P + ¬ P) → (¬¬ P → P)`

2.  `¬¬ (Q → P) ↔ ((P + ¬ P) → (Q → P))`.

### Exercise 4.3(e)

Prove the following tautologies, showing that `¬ P`, `P → ¬¬ Q`, and `¬¬ P × ¬¬ Q` are **double negation stable**:

1.  `¬¬¬ P → ¬ P`

2.  `¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)`

3.  `¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)`.

### Exercise 4.3(f)

Show that

1.  `¬¬ (P × Q) ↔ (¬¬ P) × (¬¬ Q)`

2.  `¬¬ (P + Q) ↔ ¬ (¬ P × ¬ Q)`

3.  `¬¬ (P → Q) ↔ (¬¬ P → ¬¬ Q)`.

## Solutions

### Exercise 4.3(a)

```agda
law-of-non-contradiction : {l : Level} {P : Type l} → ¬ (P × ¬ P) 
law-of-non-contradiction (p , np) = np p

no-fixed-points-neg :
  {l : Level} (A : Type l) → ¬ (A ↔ ¬ A)
no-fixed-points-neg A e =
  ( λ (h : ¬ A) → h (backward-implication e h))
  ( λ (a : A) → forward-implication e a a)
```

### Exercise 4.3(b)

```agda
double-negation-introduction : {l : Level} {P : Type l} → P → ¬¬ P 
double-negation-introduction p np = np p

double-negation-map : {l1 l2 : Level} {P : Type l1} {Q : Type l2} → (P → Q) → (¬¬ P → ¬¬ Q)
double-negation-map pq nnp nq = nnp (λ p → nq (pq p))

extend-double-negation :
  {l1 l2 : Level} {P : Type l1} {Q : Type l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
extend-double-negation {P = P} {Q = Q} f nnp nq = nnp (λ p → f p nq)
```

### Exercise 4.3(c)

```agda
double-negation-double-negation-elim :
  {l : Level} {P : Type l} → ¬¬ (¬¬ P → P)
double-negation-double-negation-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ex-falso (nnp np)))
  ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))

double-negation-Peirces-law :
  {l1 l2 : Level} {P : Type l1} {Q : Type l2} → ¬¬ (((P → Q) → P) → P)
double-negation-Peirces-law {P = P} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ _ → p))

double-negation-linearity-implication :
  {l1 l2 : Level} {P : Type l1} {Q : Type l2} →
  ¬¬ ((P → Q) + (Q → P))
double-negation-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    map-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ex-falso (np p)))
  ( λ (p : P) → map-neg (inr {A = P → Q} {B = Q → P}) f (λ _ → p))

is-irrefutable-is-decidable :
  {l : Level} {P : Type l} → ¬¬ (P + ¬ P)
is-irrefutable-is-decidable H = H (inr (H ∘ inl))
```

### Exercise 4.4(d)

### Exercise 4.4(e)

### Exercise 4.4(f)
