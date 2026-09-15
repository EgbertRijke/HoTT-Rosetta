# Exercise 2.4

```agda
module exercise-2-4-swapping-variables where

open import universe-levels
```

## Problem statement

### Exercise 2.4(a)

Define the **swap function**

```text
   Γ ⊢ A type   Γ ⊢ B type   Γ, x : A, y : B ⊢ C(x,y) type
  ---------------------------------------------------------
   Γ ⊢ σ : (Π(x:A) Π(y:B) C(x,y)) → (Π(y:B) Π(x:A) C(x,y))
```

that swaps the order of the arguments.

### Exercise 2.4(b)

Show that

```text
       Γ ⊢ A type   Γ ⊢ B type   Γ, x : A, y : B ⊢ C(x,y) type
  ------------------------------------------------------------------
   Γ ⊢ σ ∘ σ ≐ id : (Π(x:A) Π(y:B) C(x,y)) → (Π(x:A) Π(y:B) C(x,y))
```

## Solution

Only the first subexercise has a solution in agda-unimath. The second exercise exists in agda-unimath as an identification, while the exercise asks for the derivation of a judgmental equality.

```agda
swap-Π :
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : A → B → Type l3} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
swap-Π f y x = f x y
```
