# Chapter 8 Decidability in elementary number theory

```agda
module chapter-8-decidability-in-elementary-number-theory where
```

Martin-Löf's dependent type theory is a foundation for constructive
mathematics, but in constructive mathematics there is no way to show that
`P ∨ ¬ P` holds for an arbitrary proposition `P`.
Likewise, in type theory there is no way to construct an element of type
`A + ¬ A` for an arbitrary type `A`.
Consequently, if we want to reason by case analysis over whether `A` is empty or
nonempty, we first have to *show* that `A + ¬ A` holds.

A type `A` that comes equipped with an element of type `A + ¬ A` is said to be
*decidable*.
Even though we cannot show that all types are decidable, many types are indeed
decidable.
Examples include the empty type and any type that comes equipped with a point,
such as the type of natural numbers.

Decidability is an important concept with many applications in number theory and
finite mathematics, and in this section we will explore the applications of
decidability to elementary number theory.
For example, the natural numbers satisfy a well-ordering principle with respect
to decidable type families over the natural numbers; decidability can be used to
construct the greatest common divisor of any two natural numbers; and it can
also be used to show that there are infinitely many prime numbers.


```agda
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
open import section-8-3-the-well-ordering-principle-of-natural-numbers
open import section-8-4-the-greatest-common-divisor
open import section-8-5-the-infinitude-of-primes
open import section-8-6-boolean-reflection
open import exercise-8-1-open-number-theory-conjectures
open import exercise-8-2-decidability-of-decidability
open import exercise-8-3-finite-choice-decidable
open import exercise-8-4-prime-and-prime-counting-functions
open import exercise-8-5-characterization-prime
open import exercise-8-6-decidable-equality-products
open import exercise-8-7-decidable-equality-coproducts
open import exercise-8-8-decidable-equality-sigma-types
open import exercise-8-9-finite-dependent-products
open import exercise-8-10-maximal-elements
open import exercise-8-11-bezouts-identity
open import exercise-8-12-prime-factorization
open import exercise-8-13-primes-congruent-three-mod-four
open import exercise-8-14-fields-integers-modulo-prime
open import exercise-8-15-cofibonacci-sequence
```
