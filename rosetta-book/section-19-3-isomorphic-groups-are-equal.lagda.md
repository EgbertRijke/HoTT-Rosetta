# Section 19.3 Isomorphic groups are equal

```agda
module section-19-3-isomorphic-groups-are-equal where
```

<!-- rosetta-item: section-19.3 -->

## Lemma 19.3.1

<!-- rosetta-item: lemma-19.3.1; latex-label: lem:grp_iso -->

A (semi)group homomorphism `h:hom(G,H)` is an isomorphism if and only if its underlying map is an equivalence.
Consequently, there is an equivalence
```text
(G≅ H)≃ Σ(e:G≃ H) Π(x,y:G) e(μ_G(x,y))=μ_H(e(x),e(y))
```

### Proof

<!-- rosetta-item: subheading-19.3-proof -->

*Proof.* If `h:hom(G,H)` is an isomorphism, then the inverse semigroup homomorphism also provides an inverse of the underlying map of `h`.
Thus we obtain that `h` is an equivalence.
For the converse, suppose that the underlying map of `f:G→ H` is an equivalence.
Then its inverse is also a semigroup homomorphism, since we have
```text
f^{-1}(μ_H(x,y)) = f^{-1}(μ_H(f(f^{-1}(x)),f(f^{-1}(y))))
= f^{-1}(f(μ_G(f^{-1}(x),f^{-1}(y))))
= μ_G(f^{-1}(x),f^{-1}(y)).
```
 ◻

<!-- rosetta-item-end: lemma-19.3.1 -->

## Definition 19.3.2

<!-- rosetta-item: definition-19.3.2 -->

Let `G` and `H` be a semigroups in a univalent universe `𝒰`.
We define the family of maps
```text
iso-eq : (G=H)→ (G≅ H)
```
indexed by `H:Semigroup_𝒰` by `iso-eq(refl)≔id[G]`.

<!-- rosetta-item-end: definition-19.3.2 -->

## Theorem 19.3.3

<!-- rosetta-item: theorem-19.3.3; latex-label: thm:iso-eq-semigroup -->

Consider a semigroup `G` in a univalent universe `𝒰`.
Then the family of maps
```text
iso-eq : (G=H)→ (G≅ H)
```
indexed by `H:Semigroup_𝒰` is a family of equivalences.

### Proof

<!-- rosetta-item: subheading-19.3-proof-2 -->

*Proof.* By the fundamental theorem of identity types Theorem 11.2.2 it suffices to show that the total space
```text
Σ(H:Semigroup_𝒰) G≅ H
```
is contractible.
Since the type of isomorphisms from `G` to `H` is equivalent to the type of equivalences from `G` to `H` it suffices to show that the type
```text
Σ(H:Semigroup_𝒰) Σ(e:G ≃ H) Π(x,y:G) e(μ_G(x,y))=μ_{H}(e(x),e(y)))
```
is contractible.
Since `Semigroup_𝒰≐Σ(H:Set_𝒰) has-associative-mul(H)` we are in position to apply the structure identity principle stated in Theorem 11.6.2.
Note that `H↦ G≃ H` is an identity system on `Set_𝒰` at the set `G`.
By condition (v) of Theorem 11.6.2 it therefore suffices to show that the type
```text
Σ(μ':has-associative-mul(G)) Π(x,y:G) μ_G(x,y)=μ'(x,y)
```
is contractible.
This follows by function extensionality, since associativity of a binary operation on a set is a proposition. ◻

<!-- rosetta-item-end: theorem-19.3.3 -->

## Corollary 19.3.4

<!-- rosetta-item: corollary-19.3.4 -->

The type `Semigroup_𝒰` is a `1`-type.

### Proof

<!-- rosetta-item: subheading-19.3-proof-3 -->

*Proof.* The identity types of `Semigroup_𝒰` are sets because they are equivalent to the sets of isomorphisms between semigroups. ◻

<!-- rosetta-item-end: corollary-19.3.4 -->

We now turn to the proof that isomorphic groups are equal.
Analogously to the map `iso-eq` of semigroups, we have a map `iso-eq` of groups.
Note, however, that the domain of this map is now the identity type `G=H` of the *groups* `G` and `H`, so the maps `iso-eq` of semigroups and groups are not exactly the same maps.

## Definition 19.3.5

<!-- rosetta-item: definition-19.3.5 -->

Let `G` and `H` be groups in a univalent universe `𝒰`.
We define the family of maps
```text
iso-eq : (G=H)→ (G≅ H)
```
indexed by `H:Group_𝒰` by `iso-eq(refl)≔id[G]`.

<!-- rosetta-item-end: definition-19.3.5 -->

## Theorem 19.3.6

<!-- rosetta-item: theorem-19.3.6 -->

For any two groups `G` and `H` in a univalent universe `𝒰`, the map
```text
iso-eq:(G=H)→ (G≅ H)
```
is an equivalence.

### Proof

<!-- rosetta-item: subheading-19.3-proof-4 -->

*Proof.* Let `G` and `H` be groups in `𝒰`, and write `UG` and `UH` for their underlying semigroups, respectively.
Then we have a commuting triangle
<!-- rosetta-diagram: 980c674aeb1d; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[(G=H)]                  [(UG=UH)]

            [(G≅ H)]

Arrows:
- (G=H) --ap{pr 1}--> (UG=UH)
- (G=H) --iso-eq--> (G≅ H)
- (UG=UH) --iso-eq--> (G≅ H)
```
Since being a group is a property of semigroups it follows that the projection map `Group_𝒰→Semigroup_𝒰` forgetting the unit and inverses, is an embedding.
Thus the top map in this triangle is an equivalence.
The map on the right is an equivalence by Theorem 19.3.3, so the claim follows by the 3-for-2 property. ◻

<!-- rosetta-item-end: theorem-19.3.6 -->

## Corollary 19.3.7

<!-- rosetta-item: corollary-19.3.7 -->

The type of groups is a `1`-type.

<!-- rosetta-item-end: corollary-19.3.7 -->
