# Chapter 13 Function extensionality

```agda
module chapter-13-function-extensionality where
```

The function extensionality axiom asserts that for any two dependent functions
`f g : Π(x : A) B(x)`, the type of identifications `f = g` is equivalent to
the type of homotopies `f ~ g` from `f` to `g`.
In other words, two dependent functions can only be distinguished by their
values.
The function extensionality axiom therefore provides a characterization of the
identity type of dependent function types.
By the fundamental theorem of identity types it follows immediately that the
function extensionality axiom has at least three equivalent forms.
There is, however, a fourth useful equivalent form of the function
extensionality axiom: the *weak* function extensionality axiom.
This axiom asserts that any dependent product of contractible types is again
contractible.
A simple consequence of the weak function extensionality axiom is that any
dependent product of a family of `k`-types is again a `k`-type.

The function extensionality axiom is used to derive many important properties
in type theory.
One class of such properties are dependent universal properties.
Universal properties give a characterization of the type of functions into, or
out of a type.
For example, the universal property of the coproduct `A + B` characterizes the
type of maps `(A + B) → X` as the type of pairs of maps `(f, g)` consisting of
`f : A → X` and `g : B → X`, i.e., the universal property of the coproduct
`A + B` is an equivalence

```text
  ((A + B) → X) ≃ (A → X) × (B → X).
```

Note that there are function types on both sides of this equivalence.
Therefore we will need function extensionality in order to construct the
homotopies witnessing that the inverse map is both a left and a right inverse.
In fact, we leave this particular universal property as Exercise
`ex:up-coproduct`.
The universal properties that we do show in the main text are the universal
properties of `Σ`-types and of the identity type.

We end this section with two further applications of the function
extensionality axiom.
In the first, Theorem `ex:equiv_precomp`, we show that precomposition by an
equivalence is again an equivalence.
More precisely we show that `f : A → B` is an equivalence if and only if for
every type family `P` over `B`, the precomposition map

```text
  _ ∘ f : (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
```

is an equivalence.
To prove this fact we will make use of coherently invertible maps, which were
introduced in Section `sec:is-contr-map-is-equiv`.
In the second application, Theorem `thm:strong-ind-N`, we prove the strong
induction principle of the natural numbers.
Function extensionality is needed in order to derive the computation rule for
the strong induction principle.

Many important consequences of the function extensionality axiom are left as
exercises.
For example, in Exercise `ex:isprop_istrunc` you are asked to show that both
`is-contr(A)` and `is-trunc(k, A)` are propositions, and in Exercise
`ex:isprop_isequiv` you are asked to show that `is-equiv(f)` is a proposition.
The universal properties of `empty`, `unit`, and `A + B` are left as
Exercises `ex:up-emptyt`, `ex:up-unit`, and `ex:up-coproduct`.
A few more advanced properties, such as the fact that post-composition

```text
  g ∘ _ : (A → X) → (A → Y)
```

by a `k`-truncated map `g : X → Y` is itself a `k`-truncated map, appear in the
later exercises.
We encourage you to read through all of them, and get at least a basic idea of
why they are true.

```agda
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-3-universal-properties
open import section-13-4-composing-with-equivalences
open import section-13-5-the-strong-induction-principle-of-the-natural-numbers
open import exercise-13-1-homotopy-operations-equivalences
open import exercise-13-2-identity-types-of-structured-function-types
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-5-path-split-and-coherently-invertible-propositions
open import exercise-13-6-universal-property-empty-types
open import exercise-13-7-universal-property-contractible-types
open import exercise-13-8-universal-property-coproducts
open import exercise-13-9-uniqueness-of-identity-types
open import exercise-13-10-universal-property-natural-numbers
open import exercise-13-11-ordinal-induction-natural-numbers
open import exercise-13-12-dependent-products-of-truncated-maps
open import exercise-13-13-pi-types-distribute-over-coproducts
open import exercise-13-14-section-retraction-triangles
open import exercise-13-15-morphisms-over-a-type
open import exercise-13-16-equivalences-and-isomorphisms-of-sets
open import exercise-13-17-contractible-products-over-decidable-sets
open import exercise-13-18-retracts-as-limits
```
