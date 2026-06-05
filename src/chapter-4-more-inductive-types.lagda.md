# Chapter 4 More inductive types

```agda
module chapter-4-more-inductive-types where
```

In the previous section we introduced the type of natural numbers.
Many other types can also be introduced as inductive types.
In this section we will see by example how that works.
We will introduce the unit type, the empty type, coproducts, dependent pair types, and cartesian products as inductive types, and in the next section the identity type will be introduced as an inductive family of types.

From this section on, we will also start using a more informal style.
The inductive types will be specified by a description of their constructors and induction principles in terms of operations on dependent function types, which is more tightly connected with how we will use them, but we will not display the formal rules.
It is a good exercise for the reader to formally specify at least some of the inductive types of this section by stating their formal rules.

```agda
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import exercise-4-2-boolean-operations
open import exercise-4-3-negation
open import exercise-4-4-lists
```
