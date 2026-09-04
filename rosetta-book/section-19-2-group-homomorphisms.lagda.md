# Section 19.2 Group homomorphisms

```agda
module section-19-2-group-homomorphisms where
```

<!-- rosetta-item: section-19.2 -->

## Definition 19.2.1

<!-- rosetta-item: definition-19.2.1 -->

Let `G` and `H` be (semi)groups.
A **homomorphism** of (semi)groups from `G` to `H` is a pair `(f,μ_f)` consisting of a function `f:G→ H` between their underlying types, and a homotopy
```text
μ_f:Π(x,y:G) f(μ_G(x,y))=μ_H(f(x),f(y))
```
witnessing that `f` preserves the binary operation of `G`.
We will write
```text
hom(G,H)
```
for the type of all (semi)group homomorphisms from `G` to `H`.

<!-- rosetta-item-end: definition-19.2.1 -->

## Remark 19.2.2

<!-- rosetta-item: remark-19.2.2; latex-label: rmk:is-set-hom-semigroup -->

Since it is a property for a function to preserve the multiplication of a semigroup, it follows easily that equality of semigroup homomorphisms is equivalent to the type of homotopies between their underlying functions.
In particular, it follows that the type of homomorphisms of semigroups is a set.

<!-- rosetta-item-end: remark-19.2.2 -->

## Remark 19.2.3

<!-- rosetta-item: remark-19.2.3; latex-label: rmk:category-semigroup -->

The **identity homomorphism** on a (semi)group `G` is defined to be the pair consisting of
```text
id : G → G
λ x. λ y. refl : Π(x,y:G) μ_G(x,y) = μ_G(x,y).
```
Let `f:G→ H` and `g:H→ K` be (semi)group homomorphisms.
Then the composite function `g∘ f:G→ K` is also a (semi)group homomorphism, since we have the identifications
<!-- rosetta-diagram: c5bcc022bbdb; review: pending -->

*Linear diagram (automatic draft).*

```text
[g(f(μ_G(x,y)))]---->[g(μ_H(f(x),f(y)))]---->[μ_K(g(f(x)),g(f(y)))]

Arrows:
- g(f(μ_G(x,y))) --unlabeled--> g(μ_H(f(x),f(y)))
- g(μ_H(f(x),f(y))) --unlabeled--> μ_K(g(f(x)),g(f(y)))
```
Since the identity type of (semi)group homomorphisms is equivalent to the type of homotopies between (semi)group homomorphisms it is easy to see that (semi)group homomorphisms satisfy the laws of a category, i.e., that we have the identifications
```text
id∘ f = f
g∘ id = g
(h∘ g) ∘ f = h ∘ (g ∘ f)
```
for any composable (semi)group homomorphisms `f`, `g`, and `h`.

<!-- rosetta-item-end: remark-19.2.3 -->

## Definition 19.2.4

<!-- rosetta-item: definition-19.2.4 -->

Let `h:hom(G,H)` be a homomorphism of (semi)groups.
Then `h` is said to be an **isomorphism** if it comes equipped with an element of type `is-iso(h)`, consisting of triples `(h^{-1},p,q)` consisting of a homomorphism `h^{-1}:hom(H,G)` of semigroups and identifications
```text
p:h^{-1}∘ h=id[G] and q:h∘ h^{-1}=id[H]
```
witnessing that `h^{-1}` satisfies the inverse lawsWe write `G≅ H` for the type of all isomorphisms of semigroups from `G` to `H`, i.e.,
```text
G≅ H ≔ Σ(h:hom(G,H)) Σ(k:hom(H,G)) (k∘ h = id[G])× (h∘ k=id[H]).
```

<!-- rosetta-item-end: definition-19.2.4 -->

If `f` is an isomorphism, then its inverse is unique.
In other words, being an isomorphism is a property.

## Lemma 19.2.5

<!-- rosetta-item: lemma-19.2.5 -->

For any semigroup homomorphism `h:hom(G,H)`, the type
```text
is-iso(h)
```
is a proposition.
It follows that the type `G≅ H` is a set for any two semigroups `G` and `H`.

### Proof

<!-- rosetta-item: subheading-19.2-proof -->

*Proof.* Let `k` and `k'` be two inverses of `h`.
In Remark 19.2.2 we have observed that the type of semigroup homomorphisms between any two semigroups is a set.
Therefore it follows that the types `h∘ k=id` and `k∘ h=id` are propositions, so it suffices to check that `k=k'`.
In Remark 19.2.2 we also observed that the equality type `k=k'` is equivalent to the type of homotopies `k~ k'` between their underlying functions.
We construct a homotopy `k~ k'` by the usual argument:
<!-- rosetta-diagram: 6531376d1fa9; review: pending -->

*Linear diagram (automatic draft).*

```text
[k(y)]---->[k(h(k'(y))]---->[k'(y)]

Arrows:
- k(y) --unlabeled--> k(h(k'(y))
- k(h(k'(y)) --unlabeled--> k'(y)
```
 ◻

<!-- rosetta-item-end: lemma-19.2.5 -->
