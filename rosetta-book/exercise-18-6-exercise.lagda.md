# Exercise 18.6

```agda
module exercise-18-6-exercise where

```

## Problem statement

Consider a preorder `(A,≤)`, and define for any `a:A` the order preserving map
```text
y_a : PreOrd((A,≤)^op,{(Prop_𝒰,{→})})
```
by `y_a(x)≔(x≤ a)`.
Furthermore, define the **poset reflection** `‖A‖_Pos` to be the image of the map
```text
a↦ y_a : A→ PreOrd((A,≤)^op,{(Prop_𝒰,{→})}).
```

Show that the image of the map `a↦ y_a` satisfies the universal property of the set quotient of the equivalence relation
```text
x,y↦ (x≤ y)∧ (y≤ x).
```

Equip the type `‖A‖_Pos` with the structure of a poset and construct an order preserving map `η : A → ‖A‖_Pos` that satisfies the following universal property: For any poset `P`, any order preserving map `f:A→ P` extends uniquely along `η` to an order preserving map `g:‖A‖_Pos→ P`, as indicated in the following diagram:

```text
            A
           / \
        η /   \ f
         /     \
        /       \
       /         \
      ∨           ∨
   ‖A‖_Pos - - -> P
```

## Solution

No formalization has been curated yet.
