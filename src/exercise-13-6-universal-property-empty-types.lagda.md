# Exercise 13.6 Universal property empty types

```agda
module exercise-13-6-universal-property-empty-types where
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is empty.
2. The type `Π(x : A) P(x)` is contractible for any family `P` of types over
   `A`.
   This property is the **dependent universal property of an empty type**.
3. The type `A → X` is contractible for any type `X`.
   This property is the **universal property of an empty type**.

## Solution
