# Chapter 6 Universes

```agda
module chapter-6-universes where
```

To complete our specification of dependent type theory, we introduce type
theoretic *universes*.
Universes can be thought of as types that consist of types.
In reality, however, a universe consists of a type `𝕌` equipped with a type
family `Ty` over `𝕌`.
For any `X : 𝕌` we think of `X` as an *encoding* of the type `Ty(X)`.
The type family `Ty` is called a *universal type family*.

There are several reasons to equip type theory with universes.
One important reason is that it enables us to define new type families over
inductive types, using their induction principle.
We use this way of defining type families to define many familiar relations over
`ℕ`, such as the ordering relations `≤` and `<`.
We also introduce a relation `EqN` called the *observational equality* on `ℕ`.
This equivalence relation can be used to show that `0 ≠ 1`.

The idea of introducing an observational equality relation for a particular type
is that it should help us thinking about the identity type.
The identity type has been introduced in a very generic and uniform way.
In specific cases, however, we have a clear idea of what the equality relation
*should be*.
In the case of the natural numbers, for instance, we will use the observational
equality `EqN` to characterize the identity type of `ℕ`.
Characterizing identity types is one of the main themes in homotopy type theory.

A second reason to introduce universes is that it allows us to define many types
of types equipped with structure.
One of the most important examples is the type of groups, which is the type of
types equipped with the group operations satisfying the group laws, and for which
the underlying type is a set.
We won't discuss the condition for a type to be a set until the chapter on
propositions, sets, and the higher truncation levels, so the definition of
groups in type theory will be given much later.


```agda
open import section-6-1-specification-of-type-theoretic-universes
open import section-6-2-assuming-enough-universes
open import section-6-3-observational-equality-of-the-natural-numbers
open import section-6-4-peanos-seventh-and-eighth-axioms
open import exercise-6-1-injectivity-addition-multiplication
open import exercise-6-2-observational-equality-booleans
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import exercise-6-6-absolute-value-integers
```
