# Exercise 12.2 Posets are sets

```agda
module exercise-12-2-posets-are-sets where
```

## Problem statement

Recall that a **partially ordered set (poset)** is defined to be a type `A`
equipped with a relation

```text
  _≤_ : A → (A → Prop_𝒰)
```

that is reflexive, antisymmetric, and transitive.
Show that the underlying type of any poset is a set.

## Solution
