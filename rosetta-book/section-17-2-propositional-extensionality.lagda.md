# Section 17.2 Propositional extensionality

```agda
module section-17-2-propositional-extensionality where
```

<!-- rosetta-item: section-17.2 -->

An important direct consequence of the univalence axiom is the principle of propositional extensionality.
This principle asserts that any two logically equivalent propositions `P` and `Q` can be identified.
Propositional extensionality is an important principle on its own, which is sometimes assumed in formal systems without the univalence axiom.

In order to prove propositional extensionality, we first observe that the univalence axiom also characterizes the identity type of any subuniverse.

## Proposition 17.2.1

<!-- rosetta-item: proposition-17.2.1; latex-label: prp:univalence-subuniverse -->

Consider a universe `𝒰`, and let `P` be a family of propositions over `𝒰`.
Then the family of maps
```text
equiv-eq:(A=B)→ (pr 1(A) ≃ pr 1(B))
```
indexed by `A,B:Σ(X:𝒰) P(X)`, given by `equiv-eq(refl):=id` is an equivalence.

### Proof

<!-- rosetta-item: subheading-17.2-proof -->

*Proof.* Since `P` is a subuniverse, it follows from Corollary 12.2.4 that the projection map is an embedding.
Therefore we see that the asserted map is the composite of the equivalences
<!-- rosetta-diagram: d11fe49a2933; review: pending -->

*Linear diagram (automatic draft).*

```text
[(A=B)]---->[(pr 1(A)=pr 1(B))]---->[[2em] (pr 1(A)≃ pr 1(B))]

Arrows:
- (A=B) --ap{pr 1}--> (pr 1(A)=pr 1(B))
- (pr 1(A)=pr 1(B)) --equiv-eq--> [2em] (pr 1(A)≃ pr 1(B))
```
 ◻

<!-- rosetta-item-end: proposition-17.2.1 -->

## Remark 17.2.2

<!-- rosetta-item: remark-17.2.2 -->

Often, when `P` is a subuniverse, i.e., a subtype of the a universe `𝒰`, we will also write `A` for the type `pr 1(A)` if `A:Σ(X:𝒰) P(X)`.
Using this shorthand notation, the equivalence in Proposition 17.2.1 is displayed as
```text
(A=B)≃ (A≃ B).
```

<!-- rosetta-item-end: remark-17.2.2 -->

Important examples of subuniverses include the subuniverse `Prop_𝒰` of propositions in `𝒰`, the subuniverse `Set_𝒰` of sets in `𝒰`, and the subuniverse `𝒰^{≤ k}` of `k`-truncated types in `𝒰`.
The subuniverse `𝔽` of finite types in `𝒰_0`, and the subuniverses `BS_k` of `k`-element types are further important subuniverses to which Proposition 17.2.1 applies.
Note that by the univalence axiom, any subuniverse is automatically closed under equivalences.
Indeed, if we have `X≃ Y`, then we have `P(X)→ P(Y)` by transporting along the equality `X=Y` induced by univalence.

## Theorem 17.2.3

<!-- rosetta-item: theorem-17.2.3; latex-label: prp:propositional-extensionality -->

Propositions satisfy **propositional extensionality**: For any two propositions `P` and `Q`, the canonical map
```text
iff-eq:(P=Q)→ (P\iffprop Q)
```
defined by `iff-eq(refl):=(id,id)` is an equivalence.
It follows that the type `Prop_𝒰` of propositions in `𝒰` is a set.

### Proof

<!-- rosetta-item: subheading-17.2-proof-2 -->

*Proof.* Recall from Exercise 13.3 that `is-prop(X)` is a proposition for any type `X`.
Proposition 17.2.1 therefore applies, which gives
```text
(P=Q)≃ (P≃ Q)≃ (P↔ Q).
```
The last equivalence follows from Proposition 12.1.4, using the fact that `(P≃ Q)` is a proposition by Exercise 13.4. ◻

<!-- rosetta-item-end: theorem-17.2.3 -->

## Corollary 17.2.4

<!-- rosetta-item: corollary-17.2.4; latex-label: cor:decidable-Prop -->

The type
```text
decidable-Prop_𝒰 ≔ Σ(P:Prop_𝒰) is-decidable(P)
```
of decidable propositions in any universe `𝒰` is equivalent to `bool`.

### Proof

<!-- rosetta-item: subheading-17.2-proof-3 -->

*Proof.* Note that `Σ` distributes from the left over coproducts, so we have an equivalence
```text
(Σ(P:Prop_𝒰) P+¬ P)≃ (Σ(P:Prop_𝒰) P)+(Σ(Q:Prop_𝒰) ¬ Q).
```
Therefore it suffices to show that both `Σ(P:Prop_𝒰) P` and `Σ(Q:Prop_𝒰) ¬ Q` are contractible.
At the centers of contraction we have `(unit,⋆)` and `(empty,id)`, respectively.
For the contractions, note that both types are subtypes of the types of propositions.
Therefore it suffices to show that `unit=P` for any proposition `P` equipped with `p:P`, and that `empty=Q` for any proposition `Q` equipped with `q:¬ Q`.
Both identifications are obtained immediately from propositional extensionality. ◻

<!-- rosetta-item-end: corollary-17.2.4 -->
