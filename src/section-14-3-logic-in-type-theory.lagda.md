# Section 14.3 Logic in type theory

```agda
module section-14-3-logic-in-type-theory where
```

In Section `sec:modular-arithmetic` we interpreted logic in type theory via the
Curry-Howard correspondence, which stipulates that disjunction is interpreted
by coproducts and the existential quantifier is interpreted by `Σ`-types.
However, when the existential quantifier is interpreted by `Σ`-types, then it
is not possible to express certain concepts correctly, such as finiteness of a
type or being in the image a map.
Therefore we will add a second interpretation of logic in type theory, where
logical propositions are interpreted by type theoretic propositions, i.e., the
types of truncation level `-1`.

We have seen that the propositions are closed under cartesian products,
implication, and dependent products indexed by arbitrary types.
However, they are not closed under coproducts, and if `P` is a family of
propositions over a type `A`, then it is not necessarily the case that
`Σ(x : A) P(x)` is a proposition.
We will therefore use propositional truncations to interpret disjunctions and
existential quantifiers in type theory.

## Definition 14.3.1

Given two propositions `P` and `Q`, we define their **disjunction**

```text
  P ∨ Q := ∥ P + Q ∥.
```

## Proposition 14.3.2

Consider two propositions `P` and `Q`.
Then the disjunction `P ∨ Q` comes equipped with maps `i : P → P ∨ Q` and
`j : Q → P ∨ Q`.
Moreover, the proposition `P ∨ Q` satisfies the universal property of the
disjunction: For any proposition `R`, we have

```text
  (P ∨ Q → R) ↔ ((P → R) × (Q → R)).
```

## Proof

The maps `i` and `j` are defined by

```text
  i := η ∘ inl
  j := η ∘ inr.
```

Now consider the following composition of maps, for an arbitrary proposition
`R`:

```text
  (P ∨ Q → R) → (P + Q → R) → (P → R) × (Q → R).
```

The first map is an equivalence by the universal property of the propositional
truncation, and the second map is an equivalence by the universal property of
coproducts, Exercise `ex:up-coproduct`.

## Definition 14.3.3

Given a family `P` of propositions over a type `A`, we define the
**existential quantification**

```text
  ∃(x : A), P(x) := ∥ Σ(x : A) P(x) ∥.
```

## Proposition 14.3.4

Consider a family `P` of propositions over a type `A`.
Then the existential quantification `∃(x : A), P(x)` comes equipped with a
dependent function

```text
  Π(a : A) (P(a) → ∃(x : A), P(x)).
```

Furthermore, the proposition `∃(x : A), P(x)` satisfies the universal property
of the existential quantification: For any proposition `Q`, we have

```text
  ((∃(x : A), P(x)) → Q) ↔ (Π(x : A) P(x) → Q).
```

## Proof

The dependent function
`ε : Π(a : A) (P(a) → ∃(x : A), P(x))` is given by
`ε(a, p) := η(a, p)`.
Now consider the following composition of maps

```text
  ((∃(x : A), P(x)) → Q) →
  ((Σ(x : A) P(x)) → Q) →
  (Π(x : A) P(x) → Q).
```

The first map in this composite is an equivalence by the universal property of
the propositional truncation, and the second map is an equivalence by the
universal property of `Σ`-types, Theorem 13.3.1.

In the following table we give an overview of the interpretation of the logical
connectives using the propositions in type theory.

| Logical connective | Interpretation in type theory |
| --- | --- |
| `⊤` | `unit` |
| `⊥` | `empty` |
| `P ⇒ Q` | `P → Q` |
| `P ∧ Q` | `P × Q` |
| `P ∨ Q` | `∥ P + Q ∥` |
| `P ⇔ Q` | `P ↔ Q` |
| `∃(x : A), P(x)` | `∥ Σ(x : A) P(x) ∥` |
| `∀(x : A), P(x)` | `Π(x : A) P(x)` |
