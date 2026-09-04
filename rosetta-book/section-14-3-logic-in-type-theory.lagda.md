# Section 14.3 Logic in type theory

```agda
module section-14-3-logic-in-type-theory where
```

<!-- rosetta-item: section-14.3 -->

In Chapter 7 we interpreted logic in type theory via the Curry-Howard correspondence, which stipulates that disjunction (`∨`) is interpreted by coproducts and the existential quantifier (`∃`) is interpreted by `Σ`-types.
However, when the existential quantifier is interpreted by `Σ`-types, then it is not possible to express certain concepts correctly, such as finiteness of a type or being in the image a map, and therefore we will add a second interpretation of logic in type theory, where logical propositions are interpreted by type theoretic propositions, i.e., the types of truncation level `-1`.

We have seen that the propositions are closed under cartesian products, implication, and dependent products indexed by arbitrary types.
However, they are not closed under coproducts, and if `P` is a family of propositions over a type `A`, then it is not necessarily the case that `Σ(x:A) P(x)` is a proposition.
We will therefore use propositional truncations to interpret disjunctions and existential quantifiers in type theory.

## Definition 14.3.1

<!-- rosetta-item: definition-14.3.1 -->

Given two propositions `P` and `Q`, we define their **disjunction**
```text
P∨ Q ≔ ‖P+Q‖.
```

<!-- rosetta-item-end: definition-14.3.1 -->

## Proposition 14.3.2

<!-- rosetta-item: proposition-14.3.2 -->

Consider two propositions `P` and `Q`.
Then the disjunction `P∨ Q` comes equipped with maps `i:P→ P∨ Q` and `j:Q→ P∨ Q`.
Moreover, the proposition `P∨ Q` satisfies the universal property of the disjunction: For any proposition `R`, we have
```text
(P∨ Q→ R)↔ ((P→ R)× (Q→ R)).
```

### Proof

<!-- rosetta-item: subheading-14.3-proof -->

*Proof.* The maps `i` and `j` are defined by
```text
i ≔ η∘inl
j ≔ η∘inr.
```
Now consider the following composition of maps, for an arbitrary proposition `R`:
<!-- rosetta-diagram: f50f266e955f; review: pending -->

*Linear diagram (automatic draft).*

```text
[(P∨ Q→ R)]---->[(P+Q→ R)]---->[[3.6em] (P→ R)× (Q→ R)]

Arrows:
- (P∨ Q→ R) --_∘η--> (P+Q→ R)
- (P+Q→ R) --{h ↦ (h∘ inl,h∘ inr)}--> [3.6em] (P→ R)× (Q→ R)
```
The first map is an equivalence by the universal property of the propositional truncation, and the second map is an equivalence by the universal property of coproducts (Exercise 13.8). ◻

<!-- rosetta-item-end: proposition-14.3.2 -->

## Definition 14.3.3

<!-- rosetta-item: definition-14.3.3 -->

Given a family `P` of propositions over a type `A`, we define the **existential quantification**
```text
∃_{(x:A)}P(x)≔ ‖Σ(x:A) P(x)‖.
```

<!-- rosetta-item-end: definition-14.3.3 -->

## Proposition 14.3.4

<!-- rosetta-item: proposition-14.3.4 -->

Consider a family `P` of propositions over a type `A`.
Then the existential quantification `∃_{(x:A)}P(x)` comes equipped with a dependent function
```text
Π(a:A) (P(a)→ ∃_{(x:A)}P(x)).
```
Furthermore, the proposition `∃_{(x:A)}P(x)` satisfies the universal property of the existential quantification: For any proposition `Q`, we have
```text
((∃_{(x:A)}P(x))→ Q)↔(Π(x:A) P(x)→ Q).
```

### Proof

<!-- rosetta-item: subheading-14.3-proof-2 -->

*Proof.* The dependent function `ε : Π(a:A) (P(a)→ ∃_{(x:A)}P(x))` is given by `ε(a,p):=η(a,p)`.
Now consider the following composition of maps
<!-- rosetta-diagram: d76076261c30; review: pending -->

*Linear diagram (automatic draft).*

```text
[((∃_{(x:A)}P(x))→ Q)]---->[((Σ(x:A) P(x))→ Q)]---->[(Π(x:A) P(x)→ Q)]

Arrows:
- ((∃_{(x:A)}P(x))→ Q) --unlabeled--> ((Σ(x:A) P(x))→ Q)
- ((Σ(x:A) P(x))→ Q) --unlabeled--> (Π(x:A) P(x)→ Q)
```
The first map in this composite is an equivalence by the universal property of the propositional truncation, and the second map is an equivalence by the universal property of `Σ`-types (Theorem 13.3.1). ◻

<!-- rosetta-item-end: proposition-14.3.4 -->

In the following table we give an overview of the interpretation of the logical connectives using the propositions in type theory.

<!-- unsupported LaTeX environment: center -->

| logical connective      | interpretation in type theory |
|:------------------------|:------------------------------|
| `⊤`                | `unit`                     |
| `empty`                | `empty`                   |
| `P⇒ Q`      | `P→ Q`                    |
| `P∧ Q`            | `P× Q`                 |
| `P∨ Q`             | `‖P+Q‖`                |
| `P↔ Q`  | `P↔ Q`        |
| `∃_{(x:A)}P(x)` | `‖Σ(x:A) P(x)‖`       |
| `∀_{(x:A)}P(x)` | `Π(x:A) P(x)`             |
