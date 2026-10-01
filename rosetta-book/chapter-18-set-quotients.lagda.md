# Chapter 18 Set quotients

```agda
module chapter-18-set-quotients where

open import section-18-1-equivalence-relations-and-the-replacement-axiom
open import section-18-2-the-universal-property-of-set-quotients
open import section-18-3-partitions
open import section-18-4-unique-representatives-of-equivalence-classes
open import section-18-5-set-truncations
open import exercise-18-1-exercise
open import exercise-18-2-exercise
open import exercise-18-3-exercise
open import exercise-18-4-exercise
open import exercise-18-5-exercise
open import exercise-18-6-exercise
open import exercise-18-7-exercise
open import exercise-18-8-exercise
open import exercise-18-9-exercise
open import exercise-18-10-exercise
open import exercise-18-11-exercise
open import exercise-18-12-exercise
open import exercise-18-13-exercise
open import exercise-18-14-exercise
```

In this section we construct the quotient of a type by an equivalence relation.
By an equivalence relation we understand a binary relation `R` which is reflexive, symmetric, transitive, and moreover, we require that the type `R(x,y)` relating `x` and `y` is a proposition.
Therefore, if `𝒰` is a universe that contains `R(x,y)` for each `x, y : A`, then we can view `R` as a map

```text
  R : A → (A → Prop_𝒰).
```

The quotient `A/R` is constructed as the type of equivalence classes, which is just the image of the map `R : A → (A → Prop_𝒰)`.
This construction of the quotient by an equivalence relation is very much like the construction of a quotient set in classical set theory.
Examples of set quotients are abundant in mathematics.
We cover two of them in this section: the type of rational numbers and the set truncation of a type.

There is, however, a subtle issue with our construction of the set quotient as the image of the map `R : A → (A → Prop_𝒰)`.
What universe is the quotient `A/R` in?
Note that `Prop_𝒰` is a type in the successor universe `𝒰⁺`, constructed in Definition 6.2.3.
Therefore the function type `A → Prop_𝒰` as well as the quotient `A/R` are also types in `𝒰⁺`.
That seems unfortunate, because in Zermelo-Fraenkel set theory the quotient of a set by an equivalence relation is an ordinary set, and not a more general class.

To address the size issues of set quotients, we will introduce the type theoretic replacement axiom.
This axiom is analogous to the replacement axiom in Zermelo-Fraenkel set theory, which asserts that the image of a set under any function is again a set.
The type theoretic replacement property asserts that for any map `f : A → B` from a type `A` in `𝒰` to a type `B` of which the *identity types* are equivalent to types in `𝒰`, the image of `f` is also equivalent to a type in `𝒰`.
The replacement axiom can either be assumed, or it can be proven from the assumption that universes are closed under certain *higher inductive types*, and it is therefore considered to be a very mild assumption.
