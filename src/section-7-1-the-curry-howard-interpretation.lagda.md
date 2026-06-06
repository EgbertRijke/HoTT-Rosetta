# Section 7.1 The Curry-Howard interpretation

```agda
module section-7-1-the-curry-howard-interpretation where
```

The *Curry-Howard interpretation* is an interpretation of logic into type
theory.
Recall that in type theory there is no separation between the logical framework
and the general theory of collections of mathematical objects the way there is
in the more traditional setup with Zermelo-Fraenkel set theory, which is
postulated by axioms in first order logic.
These two aspects of the foundations of mathematics are unified in type theory.
The idea of the Curry-Howard interpretation is therefore to express propositions
as types, and to think of the elements of those types as their proofs.
We illustrate this idea with an example.

## Example 7.1.1

A natural number `d` is said to divide a natural number `n` if there exists a
natural number `k` such that `d · k = n`.
To represent the divisibility predicate in type theory, we need to define a
*type*

```text
  d | n,
```

of which the elements are witnesses that `d` divides `n`.
In other words, `d | n` should be the type that consists of natural numbers `k`
equipped with an identification `d · k = n`.
In general, the type of `x : A` equipped with `y : B(x)` is represented as the
type `Σ(x : A) B(x)`.
The interpretation of the existential quantification `∃` into type theory via
the Curry-Howard interpretation is therefore using `Σ`-types.

## Definition 7.1.2

Consider two natural numbers `d` and `n`.
We say that `d` **divides** `n` if there is an element of type

```text
  d | n := Σ(k : ℕ) d · k = n.
```

## Remark 7.1.3

This type-theoretical definition of the divisibility relation using `Σ`-types
has two important consequences:

1. The principal way to show that `d | n` holds is to construct a pair `(k, p)`
consisting of a natural number `k` and an identification `p : d · k = n`.
2. The principal way to use a hypothesis `H : d | n` in a proof is to proceed by
`Σ`-induction on the variable `H`.
We then get to assume a natural number `k` and an identification
`p : d · k = n`, in order to proceed with the proof.

## Example 7.1.4

Just as existential quantification `∃` is translated via the Curry-Howard
interpretation to `Σ`-types, the translation of the universal quantification `∀`
in type theory via the Curry-Howard interpretation is to `Π`-types.
For example, the assertion that every natural number is divisible by `1` is
expressed in type theory as

```text
  Π(x : ℕ) 1 | x.
```

In other words, in order to show that every number `x : ℕ` is divisible by `1`
we need to construct a dependent function

```text
  λ x. p(x) : Π(x : ℕ) 1 | x.
```

We do this by constructing an element

```text
  p(x) : Σ(k : ℕ) 1 · k = x
```

indexed by `x : ℕ`.
Such an element `p(x)` is constructed as the pair `(x, q(x))`, where the
identification `q(x) : 1 · x = x` is obtained from the left unit law of
multiplication on `ℕ`, which was constructed in Exercise 5.5.

Similarly, the type theoretic proof that every natural number `k` divides `0`,
i.e., that `k | 0`, is the pair `(0, p)` consisting of the natural number `0`
and the identification `p : k · 0 = 0` obtained from the right annihilation law
of multiplication on `ℕ`.
This identification was also constructed in Exercise 5.5.

In the following proposition we will see examples of how a hypothesis of type
`d | x` can be used.

## Proposition 7.1.5

Consider three natural numbers `d`, `x` and `y`.
If `d` divides any two of the three numbers `x`, `y`, and `x + y`, then it also
divides the third.

## Proof

We will only show that if `d` divides `x` and `y`, then it divides `x + y`.
The remaining two claims, that if `d` divides `y` and `x + y` then it divides
`x`, and that if `d` divides `x` and `x + y` then it divides `y`, are left as
Exercise 7.1.

Suppose that `d` divides both `x` and `y`.
By assumption we have elements

```text
  H : Σ(k : ℕ) d · k = x,
  K : Σ(k : ℕ) d · k = y.
```

Since the types of the variables `H` and `K` are `Σ`-types, we proceed by
`Σ`-induction on `H` and `K`.
Therefore we get to assume a natural number `k : ℕ` equipped with an
identification `p : d · k = x`, and a natural number `l : ℕ` equipped with an
identification `q : d · l = y`.
Our goal is now to construct an identification

```text
  d · (k + l) = x + y.
```

We construct such an identification as a concatenation `α ∙ (β ∙ γ)`, where
the types of the identifications `α`, `β`, and `γ` form the chain

```text
  d · (k + l) = d · k + d · l = x + d · l = x + y.
```

The identification `α` is obtained from the fact that multiplication on `ℕ`
distributes over addition, which was shown in Exercise 3.1.
The identifications `β` and `γ` are constructed using the action on paths of a
function:

```text
  β := ap (λ t. t + d · l) p
  γ := ap (λ t. x + t) q.
```

To conclude the proof that `d | x + y`, note that we have constructed the pair

```text
  (k + l, α ∙ (β ∙ γ)) : Σ(k : ℕ) d · k = x + y.
```

The full Curry-Howard interpretation of logic into type theory also involves
interpretations of disjunction, conjunction, implication, and equality.

The introduction and elimination rules for disjunction say that `P ∨ Q` holds
provided that `P` holds, that `P ∨ Q` holds provided that `Q` holds, and that to
derive `R` from `P ∨ Q` it suffices to derive `R` from `P` and from `Q`.
These rules are analogous to the introduction rules for coproduct, which assert
that there are functions `inl : A → A + B` and `inr : B → A + B`.
Furthermore, the non-dependent elimination principle for coproducts gives a
function

```text
  (A → C) → ((B → C) → (A + B → C))
```

for any type `C`, which is again analogous to the elimination rule of
disjunction.
The Curry-Howard interpretation of disjunction into type theory is therefore as
coproducts.

To interpret conjunction into type theory we observe that conjunction has a
pairing introduction rule and two projection elimination rules.
Product types possess such structure, where we have the pairing operation
`pair : A → (B → A × B)` and the projections `pr1 : A × B → A` and
`pr2 : A × B → B`.
The Curry-Howard interpretation of conjunction into type theory is therefore by
products.
We summarize the full Curry-Howard interpretation as follows:

| Logic | Type theory |
| --- | --- |
| Propositions | Types |
| Proofs | Elements |
| Predicates | Type families |
| `⊤` | `𝟙` |
| `⊥` | `∅` |
| `P ∨ Q` | `A + B` |
| `P ∧ Q` | `A × B` |
| `P ⇒ Q` | `A → B` |
| `¬ P` | `A → ∅` |
| `∃_x P(x)` | `Σ(x : A) B(x)` |
| `∀_x P(x)` | `Π(x : A) B(x)` |
| `x = y` | `x = y` |

## Remark 7.1.6

We should note, however, that despite the similarities between logic and type
theory that are highlighted in the Curry-Howard interpretation, there are also
some differences.
One important difference is that types may contain many elements, whereas in
logic, propositions are usually considered to be *proof irrelevant*.
This means that to establish the truth of a proposition it only matters
*whether* it can be proven, not in how many different ways it can be proven.
To address this dissimilarity between general types and logic, we will introduce
in the part on univalent foundations a more refined way of interpreting logic
into type theory.
In the chapter on propositions, sets, and the higher truncation levels we will
define the type `is-prop(A)`, which expresses the property that the type `A` is
a proposition.
Furthermore, we will introduce the *propositional truncation* operation in the
chapter on propositional truncations, which we will use to interpret logic into
type theory in such a way that all logical assertions are interpreted as types
that satisfy the condition of being a proposition.
