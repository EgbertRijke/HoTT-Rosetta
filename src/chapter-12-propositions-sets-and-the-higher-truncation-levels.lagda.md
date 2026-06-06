# Chapter 12 Propositions, sets, and the higher truncation levels

```agda
module chapter-12-propositions-sets-and-the-higher-truncation-levels where
```

The set theoretic foundations of mathematics arise in two stages.
The first stage is to specify the formal system of first order logic; the
second stage is to give an axiomatization of set theory in this formal system.
Unlike set theory, type theory is its own formal system.
The logic of dependent types, as given by the inference rules, is all we need.

However, even though type theory is not built upon a separate system of logic
such as first order logic, we can find logic in type theory by recognizing
certain types as propositions.
Note that the propositions of first order logic have a virtue that could be
rather useful sometimes: First order logic does not offer any way to
distinguish between any two proofs of the same proposition.
Therefore we say that propositions in type theory are those types that have at
most one element.

This condition can be expressed with the identity type: any two elements must be
equal.
Examples of such types include the empty type `empty` and the unit type `unit`.
We call such types propositions.
Propositions are useful, because if we know that a certain type is a
proposition, then we know that any of its inhabitants are equal.
Many important conditions, such as the condition that a map is an equivalence,
will turn out to be propositions.
This fact implies that two equivalences `A ≃ B` are equal if and only if their
underlying maps `A → B` are equal.
However, the claim that being an equivalence is a proposition requires function
extensionality, the topic of the next section.

In this section we use the idea of propositions in a different way.
After we establish some basic properties of propositions, we will introduce the
*sets* as the types of which the identity types are propositions.
This is again reminiscent of the situation in set theory, where equality is a
predicate in first order logic.
We will see in Example `eg:is-set-nat` that the type of natural numbers is a
set.

Next, one might ask about the types of which the identity types are *sets*.
Such types are called *1-types*.
There is an entire hierarchy of special types that arises this way, where a
type is said to be a `(k + 1)`-type if its identity types are `k`-types.
Since the identity types of the `1`-types are sets, we see that sets are in
fact `0`-types.
Most of mathematics takes place at this level, the level of sets.
The types in higher levels, as well as types that do not belong to any finite
level in this hierarchy, are studied extensively in synthetic homotopy theory.

However, we can also go a step further down: Since the identity types of sets
are propositions, we see that the propositions are `(-1)`-types.
Moreover, the identity types of propositions are contractible.
Hence we find at the bottom of this hierarchy the contractible types as the
`(-2)`-types.
There is no point in going down further, since we have seen in
Exercise `ex:prop_contr` that the identity types of contractible types are
again contractible.

```agda
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-1-booleans-are-sets
open import exercise-12-2-posets-are-sets
open import exercise-12-3-injective-maps-into-sets
open import exercise-12-4-coproduct-truncation
open import exercise-12-5-diagonal
open import exercise-12-6-truncated-sigma-types
open import exercise-12-7-truncated-products
open import exercise-12-8-retracts-of-truncated-types
open import exercise-12-9-list-concatenation-truncated-map
open import exercise-12-10-constant-maps-truncated
open import exercise-12-11-truncated-maps-triangles
open import exercise-12-12-total-maps-truncated
open import exercise-12-13-fiber-inclusions-truncated
open import exercise-12-14-isolated-elements
```
