# Section 14.2 Propositional truncations as higher inductive types

```agda
module section-14-2-propositional-truncations-as-higher-inductive-types where
```

<!-- rosetta-item: section-14.2 -->

We have given a specification of the propositional truncation of a type `A`, and we have seen that this specification by a universal property determines the propositional truncation up to equivalence if it exists.
However, the propositional truncation is not guaranteed to exist, so we will add new rules to the type theory that ensure that any type has a propositional truncation.
We do this by presenting the propositional truncation of a type `A` as a higher inductive type.
The propositional truncation `‖A‖` of a type `A` was one of the first examples of a higher inductive type, along with the circle, which we will discuss in Chapters 21 and 22.

The idea of higher inductive types is similar to the idea of ordinary inductive types, with the added feature that constructors of higher inductive types can also be used to generate *identifications*.
In other words, higher inductive types may be specified by two kinds of constructors:

1.  The *point constructors* are used to generate elements of the higher inductive types.

2.  The *path constructors* are used to generate identifications between elements of the higher inductive type.

The induction principle of the higher inductive type then tells us how to construct sections of families over it.
The rules for higher inductive types therefore come in four sets, just as the rules for ordinary inductive types in Chapter 4: the formation rule, the constructors, the induction principle, and the computation rules.

### The formation rules and the constructors

<!-- rosetta-item: subheading-14.2-the-formation-rules-and-the-constructors -->

The formation rule of the propositional truncation postulates that for every type `A` we can form the propositional truncation of `A`.
The formation rule is therefore as follows:

<!-- rosetta-proof-tree: f37dfce44a83; review: pending -->

*Proof tree (automatic faithful draft).*

```text
  Γ⊢ A \type
──────────────
$Γ⊢ ‖A‖ \type$
```

Furthermore, we will assume that all universes are closed under propositional truncations.
In other words, for any universe `𝒰` we will assume the rules

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 19605e39c500; review: pending -->

*Proof tree (automatic faithful draft).*

```text

────────────────────
X:𝒰⊢ \brckcheck{X}:𝒰
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 5c8275c99809; review: pending -->

*Proof tree (automatic faithful draft).*

```text

───

```

The constructors of a (higher) inductive type tell what structure the type comes equipped with.
In the case of a higher inductive type there may be point constructors and path constructors.
The point constructors generate elements of the higher inductive type, and the path constructors generate identifications between those elements.
In the case of the propositional truncation, there is one point constructor and one path constructor:
```text
η : A → ‖A‖
α : Π(x,y:‖A‖) x=y.
```
The point constructor `η` is sometimes called the **unit** of the propositional truncation.
It gives us that any element of `A` also generates an element of `‖A‖`.
The path constructor `α` simply identifies any two elements of `‖A‖`.
Therefore it follows immediately that `‖A‖` is a proposition.

## Lemma 14.2.1

<!-- rosetta-item: lemma-14.2.1 -->

For any type `A`, the type `‖A‖` is a proposition.`□`

<!-- rosetta-item-end: lemma-14.2.1 -->

### The induction principle and computation rules

<!-- rosetta-item: subheading-14.2-the-induction-principle-and-computation-rules -->

The induction principle for the propositional truncation tells us how to construct dependent functions
```text
h:Π(t:‖A‖) Q(t).
```
The induction principle will imply that such a dependent function `h` is entirely determined by its behavior on the constructors of `‖A‖`.
The type `‖A‖` has two constructors: a point constructor `η` and a path constructor `α`, so we have two cases to consider:

1.  Applying `h` to points of the form `η(a)` gives us a dependent function
```text
h∘ η : Π(a:A) Q(η(a)).
```
The induction principle of `‖A‖` has therefore the requirement that we can construct
```text
f:Π(a:A) Q(η(a))
```

2.  To apply `h` to the paths `α(x,y)`, we need to use the dependent action on paths from Definition 5.4.2.
For each `x,y:‖A‖` we obtain an identification
```text
apd_{h}(α(x,y)):tr_Q(α(x,y),h(x))=h(y)
```
    in the type `Q(y)`. Note, however, that `h(x)` and `h(y)` are not determined by our choice of `f:Π(a:A) Q(η(a))`. The second requirement of the induction principle of `‖A‖` is therefore that, no matter what values `h` takes, they must always be related via the dependent action on paths of `h`. This second requirement is therefore that
```text
tr_P(α(x,y),u)=v
```
    for any `u:Q(x)` and `v:Q(y)`.

## Definition 14.2.2

<!-- rosetta-item: definition-14.2.2 -->

The **induction principle** of the propositional truncation `‖A‖` of `A` asserts that for any family `Q` of types over `‖A‖`, if we have
```text
f:Π(a:A) Q(η(a))
```
and if we can construct identifications
```text
tr_Q(α(x,y),u)=v
```
for any `u:Q(x)`, `v:Q(y)` and any `x,y:‖A‖`, then we obtain a dependent function
```text
h:Π(t:‖A‖) Q(t)
```
equipped with a homotopy `h∘η~ f`.

<!-- rosetta-item-end: definition-14.2.2 -->

## Remark 14.2.3

<!-- rosetta-item: remark-14.2.3 -->

In fact, a family `Q` over `‖A‖` satisfies the second requirement in the induction principle of the propositional truncation if and only if `Q` is a family of propositions.
To see this, simply note that transporting along `α(x,y)` is an embedding.
Therefore we have
```text
(tr_Q(α(x,y),u)=tr_Q(α(x,y),v))≃ (u=v)
```
for any `u,v:Q(x)`.
By assumption, there is an identification on the left hand side, so any two elements `u` and `v` in `Q(x)` are equal.

Since the induction principle of the propositional truncation is only applicable to families of propositions over `‖A‖`, it also follows that there are no interesting computation rules to state: any identification in a proposition just holds.

<!-- rosetta-item-end: remark-14.2.3 -->

### The universal property

<!-- rosetta-item: subheading-14.2-the-universal-property -->

We have now completed the description of the propositional truncation as a higher inductive type, so it is time to show that it meets the specification we gave for the propositional truncations.
In other words, we have to show that the map `η:A→‖A‖` satisfies the universal property of the propositional truncation.

## Theorem 14.2.4

<!-- rosetta-item: theorem-14.2.4 -->

The map `η:A→‖A‖` satisfies the universal property of the propositional truncation.

### Proof

<!-- rosetta-item: subheading-14.2-proof -->

*Proof.* In order to prove that `η:A→‖A‖` satisfies the universal property of the propositional truncation of `A`, it suffices to construct a map
```text
(A→ Q)→ (‖A‖→ Q)
```
for any proposition `Q`.
Consider a map `f:A→ Q`.
Then we will construct a function `‖A‖→ Q` by the induction principle of the propositional truncation.
We have to provide a function `A→ Q`, which we have assumed already, and we have to show that
```text
tr_{λ x. Q}(α(x,y),u)=v.
```
for any `u,v:Q` and any `x,y:‖A‖`.
However, we have such identifications by the assumption that `Q` is a proposition, so the proof is complete. ◻

<!-- rosetta-item-end: theorem-14.2.4 -->

One simple application of the universal property of the propositional truncation is that `‖_‖` acts on functions in a functorial way.

## Proposition 14.2.5

<!-- rosetta-item: proposition-14.2.5 -->

There is a map
```text
‖_‖:(A→ B)→ (‖A‖→‖B‖)
```
for any two types `A` and `B`, such that
```text
‖id‖ ~ id
‖g∘ f‖ ~ ‖g‖∘‖f‖.
```

### Proof

<!-- rosetta-item: subheading-14.2-proof-2 -->

*Proof.* For any `f:A→ B`, the map `‖f‖:‖A‖→‖B‖` is defined to be the unique extension
<!-- rosetta-diagram: 5d4d1dc58188; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
 [A] ----> [B]
  |         |
[‖A‖]---->[‖B‖]

Arrows:
- A --η--> ‖A‖
- A --f--> B
- B --η--> ‖B‖
- ‖A‖ --‖f‖--> ‖B‖
```
To see that `‖_‖` preserves identity maps and compositions, simply note that `id[‖A‖]` is an extension of `id[A]`, and that `‖g‖∘‖f‖` is an extension of `g∘ f`.
Hence the homotopies are obtained by uniqueness. ◻

<!-- rosetta-item-end: proposition-14.2.5 -->
