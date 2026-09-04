# Section 19.1 The type of all groups

```agda
module section-19-1-the-type-of-all-groups where
```

<!-- rosetta-item: section-19.1 -->

In order to efficiently characterize the identity type of the type of all groups in a universe `𝒰`, we introduce the type of groups in two stages: first we introduce the type of *semigroups*, and then we introduce groups as semigroups that possess a unit element and inverses.
Since semigroups can have at most one unit element and since elements of semigroups can have at most one inverse, it follows that the type of groups is a subtype of the type of semigroups, and this will help us with the characterization of the identity type of the type of all groups.

## Remark 19.1.1

<!-- rosetta-item: remark-19.1.1 -->

In order to show that isomorphic (semi)groups can be identified, it has to be part of the definition of a (semi)group that its underlying type is a set.
This is an important observation: in many branches of algebra the objects of study are *set-level* structures.

A notable exception is formed by categories, which are objects at truncation level `1`, i.e., at the level of *groupoids*.
We will not cover categories in this book.
For more about categories we recommend Chapter 9 of .

<!-- rosetta-item-end: remark-19.1.1 -->

## Definition 19.1.2

<!-- rosetta-item: definition-19.1.2 -->

A **semigroup** in a universe `𝒰` is a triple `(G,μ,α)` consisting of a set `G` in `𝒰` equipped with a binary operation `μ:G→ (G→ G)` and a homotopy
```text
α : Π(x,y,z:G) μ(μ(x,y),z)=μ(x,μ(y,z))
```
witnessing that `μ` is **associative**.
We write `Semigroup_𝒰` for the type of all semigroups in `𝒰`, i.e., for the type
```text
Σ(G:Set_𝒰) Σ(μ:G→(G→ G)) Π(x,y,z:G) μ(μ(x,y),z)=μ(x,μ(y,z)).
```

<!-- rosetta-item-end: definition-19.1.2 -->

## Definition 19.1.3

<!-- rosetta-item: definition-19.1.3 -->

A semigroup `G` is said to be **unital** if it comes equipped with a **unit** `e:G` that satisfies the left and right unit laws
```text
left-unit : Π(y:G) μ(e,y)=y
right-unit : Π(x:G) μ(x,e)=x.
```
We write `is-unital(G)` for the type of such triples `(e,left-unit,right-unit)`.
Unital semigroups are also called **monoids**, so we define
```text
Monoid_𝒰≔Σ(G:Semigroup_𝒰) is-unital(G).
```

<!-- rosetta-item-end: definition-19.1.3 -->

The unit of a semigroup is of course unique once it exists.
In univalent mathematics we express this fact by asserting that the type `is-unital(G)` is a proposition for each semigroup `G`.
In other words, being unital is a *property* of semigroups rather than structure on it.
This is typical for univalent mathematics: we express that a structure is a property by proving that this structure is a proposition.

## Lemma 19.1.4

<!-- rosetta-item: lemma-19.1.4 -->

For a semigroup `G` the type `is-unital(G)` is a proposition.

### Proof

<!-- rosetta-item: subheading-19.1-proof -->

*Proof.* Let `G` be a semigroup.
Note that since `G` is a set, it follows that the types of the left and right unit laws are propositions.
Therefore it suffices to show that any two elements `e,e':G` satisfying the left and right unit laws can be identified.
This is easy:
```text
e = μ(e,e') = e'.
```
 ◻

<!-- rosetta-item-end: lemma-19.1.4 -->

## Definition 19.1.5

<!-- rosetta-item: definition-19.1.5 -->

Let `G` be a unital semigroup.
We say that `G` **has inverses** if it comes equipped with an operation `x↦ x^{-1}` of type `G→ G`, satisfying the left and right inverse laws
```text
left-inv : Π(x:G) μ(x^{-1},x)=e
right-inv : Π(x:G) μ(x,x^{-1}) = e.
```
We write `is-group'(G,e)` for the type of such triples `((_)^{-1},left-inv,right-inv)`, and we write
```text
is-group(G)≔Σ(e:is-unital(G)) is-group'(G,e)
```
A **group** is a unital semigroup with inverses.
We write `Group` for the type of all groups in `𝒰`.

<!-- rosetta-item-end: definition-19.1.5 -->

## Lemma 19.1.6

<!-- rosetta-item: lemma-19.1.6 -->

For any semigroup `G` the type `is-group(G)` is a proposition.

### Proof

<!-- rosetta-item: subheading-19.1-proof-2 -->

*Proof.* We have already seen that the type `is-unital(G)` is a proposition.
Therefore it suffices to show that the type `is-group'(G,e)` is a proposition for any `e:is-unital(G)`.

Since a semigroup `G` is assumed to be a set, we note that the types of the inverse laws are propositions.
Therefore it suffices to show that any two inverse operations satisfying the inverse laws are homotopic.

Let `x↦ x^{-1}` and `x↦ x^{-1'}` be two inverse operations on a unital semigroup `G`, both satisfying the inverse laws.
Then we have the following identifications
```text
x^{-1} = μ(e,x^{-1})
= μ(μ(x^{-1'},x),x^{-1})
= μ(x^{-1'},μ(x,x^{-1}))
= μ(x^{-1'},e)
= x^{-1'}
```
for any `x:G`.
Thus the two inverses of `x` are the same, and the claim follows. ◻

<!-- rosetta-item-end: lemma-19.1.6 -->

## Example 19.1.7

<!-- rosetta-item: example-19.1.7 -->

The type `ℤ` of integers has the structure of a group, with the group operation being addition.
The fact that `ℤ` is a set was shown in Exercise 12.4, and the group laws were shown in Exercise 5.7.

<!-- rosetta-item-end: example-19.1.7 -->

## Example 19.1.8

<!-- rosetta-item: example-19.1.8 -->

Given a set `X`, we define the **automorphism group** of `X` by
```text
Aut(X)≔ (X≃ X).
```
The group operation of `Aut(X)` is given by composition of equivalences, and the unit of the group is the identity function.
An important special case of the automorphism groups is the **symmetric group**
```text
S_n≔ Aut(Fin{n}).
```

<!-- rosetta-item-end: example-19.1.8 -->
