# Chapter 20 General inductive types

```agda
module chapter-20-general-inductive-types where

open import section-20-1-the-type-of-well-founded-trees
open import section-20-2-observational-equality-of-w-types
open import section-20-3-functoriality-of-w-types
open import section-20-4-the-elementhood-relation-on-w-types
open import section-20-5-extensional-w-types
open import section-20-6-russells-paradox-in-type-theory
open import exercise-20-1-exercise
open import exercise-20-2-exercise
open import exercise-20-3-exercise
open import exercise-20-4-exercise
open import exercise-20-5-exercise
open import exercise-20-6-exercise
open import exercise-20-7-exercise
```

Most inductive types we have seen in this book have a finite number of constructors with finite arities.
For example, the type `ℕ` has two constructors: one constant `0` and one unary constructor `succ-ℕ`.
However, there is no objection to having a nonfinite number of constructors, possibly with nonfinite arities.
W-types are general inductive types that have a *type* of constructors, whose arities are *types*.
W-types are therefore specified by a type `A` of *symbols* for the constructors, and a type family `B` over `A` specifying the arities of the constructors that the symbols represent.

An example of a W-type is the type of finitely branching rooted trees.
This inductive type has a constructor with arity `X` for each finite type `X`.
In other words, a finitely branching rooted tree is obtained by attaching finitely many finitely branching rooted trees to a root.
The root itself is therefore a finitely branching tree, obtained from the `0`-ary constructor corresponding to the empty type, and if we have any finite family of finitely branching rooted trees, we can combine them all into one finitely branching rooted tree by attaching them to a new root.
