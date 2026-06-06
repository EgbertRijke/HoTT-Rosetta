# Section 17.5 Classical mathematics with the univalence axiom

```agda
module section-17-5-classical-mathematics-with-the-univalence-axiom where
```

In classical mathematics, the axiom of choice asserts that for any collection
`X` of nonempty sets, there is a choice function `f` such that `f(x) ∈ x` for
each `x ∈ X`.
The univalence axiom is consistent with the axiom of choice, but we have to be
careful in our formulation of the axiom of choice to make it about sets.
A naive interpretation that would be applicable to all types, such as the
assertion that every family `B` of inhabited types has a section, is not
consistent with univalence.
We will use the type `BS_2` of `2`-element types for a counterexample.

## Proposition 17.5.1

The type

```text
  Σ(X : BS_2) X
```

of pointed `2`-element types is contractible.
Consequently, the canonical family of maps

```text
  (Fin(2) = X) → X
```

indexed by `X : BS_2`, is a family of equivalences.

## Proof

By the univalence axiom it follows that the type
`Σ(X : BS_2) Fin(2) ≃ X` is contractible.
In order to show that `Σ(X : BS_2) X` is contractible, it therefore suffices to
show that the map

```text
  f : (Fin(2) ≃ X) → X
```

given by `f(e) := e(star)` is an equivalence.
Since being an equivalence is a proposition by Exercise `ex:isprop_isequiv`, we
may assume an equivalence `α : Fin(2) ≃ X`, and we proceed by equivalence
induction on `α`.
Therefore, it suffices to show that the map

```text
  f : (Fin(2) ≃ Fin(2)) → Fin(2)
```

given by `f(e) := e(star)` is an equivalence.
Using the notation from Section `sec:Fin`, we define the inverse map `g` by

```text
  g(star)    := id
  g(i(star)) := succ-Fin_2,
```

and it is a straightforward verification that `f` and `g` are inverse to each
other.

## Corollary 17.5.2

There is no dependent function

```text
  Π(X : BS_2) X.
```

## Proof

By Proposition 17.5.1 and Exercise `ex:equiv-pi`, we have an equivalence

```text
  (Π(X : BS_2) Fin(2) = X) ≃ (Π(X : BS_2) X).
```

Note that `Π(X : BS_2) Fin(2) = X` is the type of contractions of `BS_2`, using
the center of contraction `Fin(2)`.
Therefore it suffices to show that `BS_2` is not contractible.
Recall from Exercise `ex:prop_contr` that the identity types of contractible
types are contractible.
On the other hand, it follows from Proposition 17.5.1 that the identity type
`Fin(2) = Fin(2)` in `BS_2` is equivalent to `Fin(2)`.
This type is not contractible by Exercise `ex:is-not-contractible-Fin`.
We conclude that `BS_2` is not contractible.

The family `X ↦ X` over `BS_2` is therefore an example of a family of nonempty
types for which there are provably no sections.
In the following corollary we conclude more generally that there is no way to
construct an element of an arbitrary inhabited type.

## Corollary 17.5.3

If `𝒰` is a univalent universe, then there is no **global choice** function

```text
  Π(A : 𝒰) ∥ A ∥ → A.
```

## Proof

Suppose `f : Π(A : 𝒰) ∥ A ∥ → A`.
By restricting `f` to the type of `2`-element types in `𝒰`, we obtain a
function

```text
  Π(A : BS_2) ∥ A ∥ → A.
```

Note that every `2`-element type is inhabited, i.e., there is an element of type
`∥ A ∥` for every `2`-element type `A`.
To see this, consider a type `A : 𝒰` such that `∥ Fin(2) ≃ A ∥`.
To obtain an element of type `∥ A ∥`, we may assume an equivalence
`e : Fin(2) ≃ A`.
Then we have `η(e(0)) : ∥ A ∥`.

Since every `2`-element type is inhabited, we obtain a function
`Π(A : BS_2) A`, which is impossible by Corollary 17.5.2.

Corollary 17.5.3 is of philosophical importance.
It shows that the **principle of global choice** is incompatible with the
univalence axiom, i.e., that there is no way to construct a function
`∥ A ∥ → A` for all types `A`.
In other words, we cannot obtain an element of `A` merely from the assumption
that the type `A` is inhabited.
The obstruction is that no such choice of an element of `A` can be invariant
under the automorphisms on `A`, i.e., under the self-equivalences on `A`.

This is perhaps a good moment to stress that the axiom of choice is really an
axiom about *sets*, not about more general types.
When we restrict the axiom of choice to sets, it turns out to be consistent
with the univalence axiom and therefore safe to assume.
In this book, however, we will not have many applications for the axiom of
choice and therefore we will not assume it, unless we explicitly say otherwise.

## Definition 17.5.4

The **axiom of choice** asserts that for any family `B` of inhabited sets
indexed by a set `A`, the type of sections of `B` is also inhabited, i.e., it
asserts that there is an element of type

```text
  AC_𝒰(A, B) := (Π(x : A) ∥ B(x) ∥) → ∥ Π(x : A) B(x) ∥,
```

for every `A : Set_𝒰` and `B : A → Set_𝒰`.

Similar care has to be taken with the type theoretic formulation of the law of
excluded middle.
It is again inconsistent to assume that every type is decidable.

## Theorem 17.5.5

There is no **global decidability function**

```text
  Π(X : 𝒰) is-decidable(X).
```

## Proof

Suppose there is such a dependent function `d`.
By restricting `d` to the subuniverse of `2`-element types, we obtain a
dependent function

```text
  d : Π(X : BS_2) is-decidable(X).
```

However, each `2`-element type `X` is inhabited.
By Exercise `ex:propositional-truncations-drill` we obtain a function

```text
  is-decidable(X) → X
```

for each `2`-element type `X`.
Therefore, we obtain from `d` a dependent function `Π(X : BS_2) X`, which does
not exist by Corollary 17.5.2.

The law of excluded middle is really an axiom of propositional logic, and it is
indeed consistent with the univalence axiom that every *proposition* is
decidable.

## Definition 17.5.6

The **law of excluded middle** asserts that every proposition is decidable,
i.e.,

```text
  LEM_𝒰 := Π(P : Prop_𝒰) is-decidable(P).
```

We will again not assume the law of excluded middle, unless we say otherwise.
Nevertheless, we have seen in Section `sec:decidability` that some
propositions are already decidable without assuming the law of excluded middle,
and decidability remains an important concept in type theory and mathematics.
