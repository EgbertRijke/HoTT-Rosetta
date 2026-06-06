# Chapter 7 Modular arithmetic via the Curry-Howard interpretation

```agda
module chapter-7-modular-arithmetic-via-the-curry-howard-interpretation where
```

We have now fully described Martin-Löf's dependent type theory.
It is now up to us to start developing some mathematics in it, and
Martin-Löf's dependent type theory is great for elementary mathematics, such as
basic number theory, some algebra, and combinatorics.
The fundamental idea that is used to develop basic mathematics in type theory is
the Curry-Howard interpretation.
This is a translation of logic into type theory, which we will use to express
concepts of mathematics such as divisibility, the congruence relations, and so
on.

We will also introduce the family `Fin` of the standard finite types, indexed by
`ℕ`, and show how each `Fin(k + 1)` can be equipped with the group structure of
integers modulo `k + 1`.
Our goal here is to demonstrate how to do those things in type theory, so we
will aim for a high degree of accuracy.


```agda
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-7-5-the-cyclic-groups
open import exercise-7-1-divisibility-three-for-two
open import exercise-7-2-divisibility-poset
open import exercise-7-3-divisibility-factorials
open import exercise-7-4-successor-finite-types-addition
open import exercise-7-5-observational-equality-finite-types
open import exercise-7-6-predecessor-finite-types
open import exercise-7-7-classical-finite-types
open import exercise-7-8-ring-laws-finite-cyclic-types
open import exercise-7-9-euclidean-division
open import exercise-7-10-k-ary-natural-numbers
```
