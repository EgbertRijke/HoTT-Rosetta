# Section 18.1 Equivalence relations and the replacement axiom

```agda
module section-18-1-equivalence-relations-and-the-replacement-axiom where
```

<!-- rosetta-item: section-18.1 -->

## Definition 18.1.1

<!-- rosetta-item: definition-18.1.1; latex-label: defn:eq_rel -->

Consider a type `A` and a universe `𝒰`.
Let `R:A→ (A→Prop_𝒰)` be a binary relation on `A` valued in the propositions in `𝒰`.
We say that `R` is an **equivalence relation** if `R` comes equipped with
```text
ρ : Π(x:A) R(x,x)
σ : Π(x,y:A) R(x,y)→ R(y,x)
τ : Π(x,y,z:A) R(x,y)→ (R(y,z)→ R(x,z)),
```
witnessing that `R` is reflexive, symmetric, and transitive.
We write `Eq-Rel_𝒰(A)` for the type of all equivalence relations on `A` valued in the propositions in `𝒰`.

<!-- rosetta-item-end: definition-18.1.1 -->

## Definition 18.1.2

<!-- rosetta-item: definition-18.1.2 -->

Let `R:A→ (A→Prop_𝒰)` be an equivalence relation.
A subtype `P:A→ Prop_𝒰` is said to be an **equivalence class** if it satisfies the condition
```text
is-equivalence-class(P)≔∃_{(x:A)}∀_{(y:A)}P(y)↔ R(x,y).
```
We define `A/R` to be the type of equivalence classes, i.e., we define
```text
A/R≔ Σ(P:A→Prop_𝒰) is-equivalence-class(P).
```
Furthermore, we define **equivalence class of `x:A`** to be
```text
[x]_R≔ R(x),
```
which is indeed an equivalence class.
Sometimes we will write `q_R:A→ A/R` for the map `x↦ [x]_R`.

<!-- rosetta-item-end: definition-18.1.2 -->

In other words, `A/R` is the image of the map `R:A→ (A→Prop_𝒰)`.
In the following proposition we characterize the identity type of `A/R`.
As a corollary, we obtain equivalences
```text
([x]_R=[y]_R)≃ R(x,y),
```
justifying that the quotient `A/R` is defined to be the type of equivalence classes.
Note that in our characterization of the identity type of `A/R` we make use of propositional extensionality.

## Proposition 18.1.3

<!-- rosetta-item: proposition-18.1.3; latex-label: prp:eq-quotient -->

Let `R:A→ (A→Prop_𝒰)` be an equivalence relation.
Furthermore, consider `x:A` and an equivalence class `P`.
Then the canonical map
```text
([x]_R=P)→ P(x)
```
is an equivalence.

### Proof

<!-- rosetta-item: subheading-18.1-proof -->

*Proof.* By Theorem 11.2.2 it suffices to show that the total space
```text
Σ(P:A/R) P(x)
```
is contractible.
The center of contraction is of course `[x]_R`, which satisfies `[x]_R(x)` by reflexivity of `R`.
It remains to construct a contraction.
Since `Σ(P:A/R) P(x)` is a subtype of `A/R`, we construct a contraction by showing that
```text
[x]_R=P
```
whenever `P(x)` holds.
Since `P` is an equivalence class there exists an element `y:A` such that `P=[y]_R`.
Note that our goal is a proposition, so we may assume that we have such a `y`.
From the assumption that `P(x)` holds, it follows that `R(x,y)` holds.
To complete the proof, it therefore is suffices to show that
```text
[x]_R=[y]_R,
```
assuming that `R(x,y)` holds.
By function extensionality and propositional extensionality, it is equivalent to show that
```text
Π(z:A) R(x,z)↔ R(y,z),
```
which follows directly from the assumption that `R` is an equivalence relation. ◻

<!-- rosetta-item-end: proposition-18.1.3 -->

## Corollary 18.1.4

<!-- rosetta-item: corollary-18.1.4; latex-label: cor:eq-quotient -->

Consider an equivalence relation `R` on a type `A`, and let `x,y:A`.
Then there is an equivalence
```text
([x]_R=[y]_R)≃ R(x,y).
```

<!-- rosetta-item-end: corollary-18.1.4 -->

## Remark 18.1.5

<!-- rosetta-item: remark-18.1.5 -->

Notice that type of equivalence classes of an equivalence relation in `𝒰` is a type in the universe `𝒰^+` that contains `𝒰` and every type in `𝒰`, or indeed in any universe `𝒱` containing `𝒰` and every type in `𝒰`.
Indeed, the type
```text
Prop_𝒰≐Σ(X:𝒰) is-prop(X)
```
of propositions in `𝒰` is a type in `𝒱`.
It follows that the type `A→Prop_𝒰` is a type in `𝒱`.
The type of equivalence classes of an equivalence relation `R` on `A` in `𝒰` is a subtype of `A→Prop_𝒰` in `𝒰`, so we conclude that `A/R` is a type in `𝒱`.

<!-- rosetta-item-end: remark-18.1.5 -->

In classical mathematics, on the other hand, we consider the class of equivalence classes of an equivalence relation to be a (small) set.
We will introduce the replacement axiom in order to ensure that set quotients in type theory are small.

Recall that in set theory, the replacement axiom asserts that for any family of sets `{X_i}_{i∈ I}` indexed by a set `I`, there is a set `X[I]` consisting of precisely those sets `x` for which there exists an `i∈ I` such that `x∈ X_i`.
In other words: the image of a set-indexed family of sets is again a set.
Without the replacement axiom, `X[I]` would be a class.

In type theory, we may similarly ask whether the image of a map `X:I→𝒰` is `𝒰`-small, assuming that `I` is `𝒰`-small.
The replacement axiom settles a more general variant of this question.
The key observation is that the identity types of `𝒰` are `𝒰`-small by the univalence axiom.
In other words, univalent universes are *locally small* in the following sense.

## Definition 18.1.6

<!-- rosetta-item: definition-18.1.6; latex-label: defn:locally-small-type -->

Consider a universe `𝒰`.
A type `A` is said to be **locally `𝒰`-small** if the identity type `x=y` is `𝒰`-small for every `x,y:A`.
We write
```text
is-locally-small_𝒰(A)≔ Π(x,y:A) is-small_𝒰(x=y).
```
Similarly, a map `f:A→ B` is said to be **locally `𝒰`-small** if all of its fibers are locally `𝒰`-small.

<!-- rosetta-item-end: definition-18.1.6 -->

## Example 18.1.7

<!-- rosetta-item: example-18.1.7 -->

 

1.  Any `𝒰`-small type is also locally `𝒰`-small.

2.  Any proposition is locally small with respect to any universe `𝒰`.

3.  Any univalent universe `𝒰` is locally `𝒰`-small, because by the univalence axiom we have an equivalence
```text
(A=B)≃ (A≃ B)
```
    for each `A,B:𝒰`, and the type `A≃ B` is in `𝒰`.

4.  For any family `B` of locally `𝒰`-small types over a `𝒰`-small type `A`, the dependent product `Π(x:A) B(x)` is locally `𝒰`-small.

<!-- rosetta-item-end: example-18.1.7 -->

We are now ready to assume the replacement axiom.

## Axiom 18.1.8

<!-- rosetta-item: axiom-18.1.8; latex-label: axiom:replacement -->

For any universe `𝒰`, we assume that for any map `f:A→ B` from a `𝒰`-small type `A` into a locally `𝒰`-small type `B`, the image of `f` is `𝒰`-small.

<!-- rosetta-item-end: axiom-18.1.8 -->

## Example 18.1.9

<!-- rosetta-item: example-18.1.9 -->

For any type `A:𝒰`, the type `𝒰_A` of all types in `𝒰` merely equivalent to `A` is equivalent to the image of the constant map `const_A:unit→ 𝒰` is small.
Since `unit` is small and `𝒰` is locally `𝒰`-small, it follows from the replacement axiom that `𝒰_A` is `𝒰`-small.

<!-- rosetta-item-end: example-18.1.9 -->

## Example 18.1.10

<!-- rosetta-item: example-18.1.10 -->

The type `𝔽` of all finite types in `𝒰` is equivalent to be the image of the map
```text
Fin : ℕ→𝒰.
```
Since `ℕ` is `𝒰`-small and `𝒰` is locally `𝒰`-small, it follows from the replacement axiom that `𝔽` is `𝒰`-small.

<!-- rosetta-item-end: example-18.1.10 -->

## Example 18.1.11

<!-- rosetta-item: example-18.1.11 -->

Consider a type `A` in `𝒰` and an equivalence relation `R` on `A` in `𝒰`.
Then the type `A/R` is `𝒰`-small, since it is equivalent to the image of
```text
R:A→ (A→Prop_𝒰),
```
which maps the `𝒰`-small type `A` into the locally `𝒰`-small type `A→Prop_𝒰`.

<!-- rosetta-item-end: example-18.1.11 -->
