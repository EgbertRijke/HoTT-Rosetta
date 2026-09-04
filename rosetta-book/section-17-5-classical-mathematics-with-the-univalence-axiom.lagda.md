# Section 17.5 Classical mathematics with the univalence axiom

```agda
module section-17-5-classical-mathematics-with-the-univalence-axiom where
```

<!-- rosetta-item: section-17.5 -->

In classical mathematics, the axiom of choice asserts that for any collection `X` of nonempty sets, there is a choice function `f` such that `f(x)∈ x` for each `x∈ X`.
The univalence axiom is consistent with the axiom of choice, but we have to be careful in our formulation of the axiom of choice to make it about sets.
A naive interpretation that would be applicable to all types, such as the assertion that every family `B` of inhabited types has a section, is not consistent with univalence.
We will use the type `BS_2` of `2`-element types for a counterexample.

## Proposition 17.5.1

<!-- rosetta-item: proposition-17.5.1; latex-label: prp:Eq-F2 -->

The type
```text
Σ(X:BS_2) X
```
of pointed `2`-element types is contractible.
Consequently, the canonical family of maps
```text
(Fin{2}= X) → X
```
indexed by `X:BS_2`, is a family of equivalences.

### Proof

<!-- rosetta-item: subheading-17.5-proof -->

*Proof.* By the univalence axiom it follows that the type `Σ(X:BS_2) Fin{2}≃ X` is contractible.
In order to show that `Σ(X:BS_{2}) X` is contractible, it therefore suffices to show that the map
```text
f: (Fin{2}≃ X)→ X
```
given by `f(e)≔ e(⋆)`, is an equivalence.
Since being an equivalence is a proposition by Exercise 13.4, we may assume an equivalence `α:Fin{2}≃ X`, and we proceed by equivalence induction on `α`.
Therefore, it suffices to show that the map
```text
f: (Fin{2}≃ Fin{2})→Fin{2}
```
give by `f(e)≔ e(⋆)` is an equivalence.
Using the notation from Section 7.3, we define the inverse map `g` by
```text
g(⋆) ≔ id
g(i(⋆)) ≔ succ-Fin_2,
```
and it is a straightforward verification that `f` and `g` are inverse to each other. ◻

<!-- rosetta-item-end: proposition-17.5.1 -->

## Corollary 17.5.2

<!-- rosetta-item: corollary-17.5.2; latex-label: cor:no-section-F2 -->

There is no dependent function
```text
Π(X:BS_2) X.
```

### Proof

<!-- rosetta-item: subheading-17.5-proof-2 -->

*Proof.* By Proposition 17.5.1 and Exercise 13.12, we have an equivalence
```text
(Π(X:BS_2) Fin{2}=X)≃ (Π(X:BS_2) X).
```
Note that `Π(X:BS_2) Fin{2}=X` is the type of contractions of `BS_2`, using the center of contraction `Fin{2}`.
Therefore it suffices to show that `BS_2` is not contractible.
Recall from Exercise 10.1 that the identity types of contractible types are contractible.
On the other hand, it follows from Proposition 17.5.1 that the identity type `Fin{2}=Fin{2}` in `BS_2` is equivalent to `Fin{2}`.
This type isn’t contractible by Exercise 10.4.
We conclude that `BS_2` is not contractible. ◻

<!-- rosetta-item-end: corollary-17.5.2 -->

The family `X↦ X` over `BS_2` is therefore an example of a family of nonempty types for which there are provably no sections.
In the following corollary we conclude more generally that there is no way to construct an element of an arbitrary inhabited type.

## Corollary 17.5.3

<!-- rosetta-item: corollary-17.5.3; latex-label: cor:no-global-choice -->

If `𝒰` is a univalent universe, then there is no **global choice** function
```text
Π(A:𝒰) ‖A‖→ A.
```

### Proof

<!-- rosetta-item: subheading-17.5-proof-3 -->

*Proof.* Suppose `f:Π(A:𝒰) ‖A‖→ A`.
By restricting `f` to the type of `2`-element types in `𝒰`, we obtain a function
```text
Π(A:BS_2) ‖A‖→ A.
```
Note that every `2`-element type is inhabited, i.e., there is an element of type `‖A‖` for every `2`-element type `A`.
To see this, consider a type `A:𝒰` such that `‖Fin{2}≃ A‖`.
To obtain an element of type `‖A‖`, we may assume an equivalence `e:Fin{2}≃ A`.
Then we have `η(e(0)):‖A‖`.

Since every `2`-element type is inhabited, we obtain a function `Π(A:BS_2) A`, which is impossible by Corollary 17.5.2. ◻

<!-- rosetta-item-end: corollary-17.5.3 -->

Corollary 17.5.3 is of philosophical importance.
It shows that the **principle of global choice** is incompatible with the univalence axiom, i.e., that there is no way to obtain construct a function `‖A‖→ A` for all types `A`.
In other words, we cannot obtain an element of `A` merely from the assumption that the type `A` is inhabited.
What is the obstruction?
It is the fact that no such choice of an element of `A` can be invariant under the automorphisms on `A`, i.e., under the self-equivalences on `A`.
Indeed, in the example where `A` is the `2`-element type `Fin{2}` there are no fixed point of the equivalence `succ-Fin_2:Fin{2}≃Fin{2}`.
By the univalence axiom, there is an identification `p:Fin{2}=Fin{2}` in `𝒰`, such that `tr(p,x)=succ-Fin_2(x)`.
If we had a function
```text
f:Π(X:𝒰) ‖X‖→ X,
```
the dependent action on paths of `f` would give an identification
```text
apd_{f}(p):succ-Fin_2(f(Fin{2},p,H))=f(Fin{2},p,η(0)).
```
In other words, it would give us a fixed point for the successor function on `Fin{2}`.

This is perhaps a good moment to stress that the axiom of choice is really an axiom about *sets*, not about more general types.
And indeed, when we restrict the axiom of choice to sets, it turns out to be consistent with the univalence axiom and therefore safe to assume.
In this book, however, we will not have many applications for the axiom of choice and therefore we will not assume it, unless we explicitly say otherwise.

## Definition 17.5.4

<!-- rosetta-item: definition-17.5.4 -->

The **axiom of choice** asserts that for any family `B` of inhabited sets indexed by a set `A`, the type of sections of `B` is also inhabited, i.e., it asserts that there is an element of type
```text
AC_{𝒰}(A,B)≔ (Π(x:A) ‖B(x)‖)→‖Π(x:A) B(x)‖,
```
for every `A:Set_𝒰` and `B:A→Set_𝒰`.

<!-- rosetta-item-end: definition-17.5.4 -->

Similar care has to be taken with the type theoretic formulation of the law of excluded middle.
It is again inconsistent to assume that every type is decidable.

## Theorem 17.5.5

<!-- rosetta-item: theorem-17.5.5 -->

There is no **global decidability function**
```text
Π(X:𝒰) is-decidable(X).
```

### Proof

<!-- rosetta-item: subheading-17.5-proof-4 -->

*Proof.* Suppose there is such a dependent function `d`.
By restricting `d` to the subuniverse of `2`-element types, we obtain a dependent function
```text
d:Π(X:BS_2) is-decidable(X).
```
However, each `2`-element type `X` is inhabited.
By Exercise 14.1 we obtain a function
```text
is-decidable(X)→ X
```
for each `2`-element type `X`.
Therefore, we obtain from `d` a dependent function `Π(X:BS_2) X`, which does not exist by Corollary 17.5.2. ◻

<!-- rosetta-item-end: theorem-17.5.5 -->

The law of excluded middle is really an axiom of propositional logic, and it is indeed consistent with the univalence axiom that every *proposition* is decidable.

## Definition 17.5.6

<!-- rosetta-item: definition-17.5.6 -->

The **law of excluded middle** asserts that every proposition is decidable, i.e.,
```text
LEM_𝒰≔ Π(P:Prop_𝒰) is-decidable(P).
```

<!-- rosetta-item-end: definition-17.5.6 -->

We will again not assume the law of excluded middle, unless we say otherwise.
Nevertheless, we have seen in Chapter 8 that some propositions are already decidable without assuming the law of excluded middle, and decidability remains an important concept in type theory and mathematics.
