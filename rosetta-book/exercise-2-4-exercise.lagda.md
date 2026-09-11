# Exercise 2.4

```agda
module exercise-2-4-exercise where

```

## Problem statement

<div class="subexenum">

Define the **swap function**

<!-- rosetta-proof-tree: d7366097dc2c; review: pending -->

```text
  Γ⊢ A type   Γ⊢ B type   Γ,x:A,y:B⊢ C(x,y) type
──────────────────────────────────────────────────
Γ⊢ σ:(Π(x:A) Π(y:B) C(x,y))→(Π(y:B) Π(x:A) C(x,y))
```

that swaps the order of the arguments.

Show that

</div>

<div class="small">

<!-- rosetta-proof-tree: e2ad895faccd; review: pending -->

```text
     Γ⊢ A type   Γ⊢ B type   Γ,x:A,y:B⊢ C(x,y) type
────────────────────────────────────────────────────────
Γ⊢ σ∘σ≐id:(Π(x:A) Π(y:B) C(x,y))→ (Π(x:A) Π(y:B) C(x,y))
```

</div>

## Solution

<!-- rosetta-item: exercise-2-4 -->

```agda
{l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}

swap-Π : ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
swap-Π f y x = f x y
```
