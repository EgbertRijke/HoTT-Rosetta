# Chapter 14 Propositional truncations

```agda
module chapter-14-propositional-truncations where
```

It is common in mathematics to express the property that a certain type of
objects is inhabited, without imposing extra structure on those objects.
For example, when we assert the property that a set is finite, then we only
claim that there exists a bijection to a standard finite set `{0, ..., n - 1}`
for some `n`, not that the set is equipped with such a bijection.
There is indeed a conceptual difference between a finite set and a set equipped
with a bijection to a standard finite set.
The latter concept is that of a finite *totally ordered* set.
This difference is due to the fact that finiteness is a property, whereas there
may be many different bijections to a standard finite set.

A similar observation can be made in the case of the image of a map.
Note that being in the image of a given map `f : A → B` is a property.
When we claim that `b : B` is in the image of `f`, then we only claim that the
type of `a : A` such that `f(a) = b` is inhabited.
On the other hand, we saw in Exercise `ex:fib_replacement` that the type of
`b : B` equipped with an `a : A` such that `f(a) = b` is equivalent to the type
`A`, i.e., we have an equivalence

```text
  A ≃ Σ(b : B) Σ(a : A) f(a) = b.
```

Something is clearly off here, because the type `A` is often not a subtype of
the type `B`, while we would expect the image of `f` to be a subtype of `B`.
Therefore we see that the type `Σ(a : A) f(a) = b` does not quite capture the
concept of `b` being in the image of `f`.
The difference is again due to the fact that `fib(f, b)` is often not a
proposition, whereas we are looking to express the proposition that the
preimage of `f` at `b` is inhabited.

To correctly capture the concepts of finiteness and the image of a map in type
theory, and many further mathematical concepts, we need a way to assert the
*proposition* that a type is inhabited.
The proposition that a type `A` is inhabited is called the propositional
truncation of `A`.

```agda
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-14-4-mapping-propositional-truncations-into-sets
open import exercise-14-1-propositional-truncation-properties
open import exercise-14-2-mere-equality
open import exercise-14-3-products-of-propositional-truncations
open import exercise-14-4-dependent-universal-property-truncations
open import exercise-14-5-propositional-truncations-with-sections
open import exercise-14-6-propositional-truncations-of-decidable-types
open import exercise-14-7-precomposition-with-truncation
open import exercise-14-8-impredicative-encodings
open import exercise-14-9-interval
```
