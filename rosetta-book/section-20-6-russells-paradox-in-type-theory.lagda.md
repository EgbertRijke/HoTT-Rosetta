# Section 20.6 Russell's paradox in type theory

```agda
module section-20-6-russells-paradox-in-type-theory where
```

<!-- rosetta-item: section-20.6 -->

Russell’s paradox tells us that there cannot be a set of all sets.
If there were such a set `S`, then we could form the set
```text
R≔ {x∈ S| x∉ x},
```
for which we have `R∈ R↔ R∉ R`, a contradiction.
To reproduce Russell’s paradox in type theory, we first recall a crucial difference between the type theoritic judgment `a:A` and the set theoretic proposition `x∈ y`.
Although the judgment `a:A` plays a similar role in type theory as the elementhood relation, types and their elements are fundamentally different entities, whereas in Zermelo-Fraenkel set theory there are only sets, and the proposition `x∈ y` can be formed for any two sets `x` and `y`.
In type theory, there is no relation on the universe that is similar to the elementhood relation.

However, we have seen in Section 20.5 that it is possible to define an elementhood relation on arbitrary W-types.
We will use this elementhood relation on the W-type `W(𝒰,Ty)` to derive a paradox analogous to Russell’s paradox, and we will see that `𝒰` cannot be equivalent to a type in `𝒰`.

The type `W(𝒰,Ty)` possesses a lot of further structure.
In fact, it can be used to encode constructive set theory in type theory.
There is, however, one significant difference with ordinary set theory: the elementhood relation is type-valued.
In other words, there may be many ways in which `x∈ y` holds.
The type `W(𝒰,Ty)` is therefore also called the type of **multisets**.
It was first studied by Aczel in , with refinements in , and in the setting of univalent mathematics it has been studied extensively by Gylterud in .

## Definition 20.6.1

<!-- rosetta-item: definition-20.6.1 -->

Consider a `𝒰` with universal type family `Ty`.
We define the type
```text
M_𝒰 ≔ W(𝒰,Ty),
```
and the elements of `M_𝒰` are called **multisets in `𝒰`**.
We will write
```text
{f(x)| x:A}
```
for the multiset in `𝒰` of the form `tree(A,f)`.
More generally, given an element `t(x_0,…,x_n):M_𝒰` in context `x_0:A_0,…,x_n:A_n(x_0,…,x_{n-1})`, where each `A_i` is in `𝒰`, we will write
```text
{t(x_0,…,x_n)| x_0:A_0,…,x_n:A_n(x_0,…,x_{n-1})}
```
for the multiset in `𝒰` of the form
```text
tree(Σ(x_0:A_0) ⋯ A_n(x_0,…,x_{n-1}),λ (x_0,…,x_n). t(x_0,…,x_n)).
```

Given a multiset `X≐ {f(x)| x:A}` in `𝒰`, the **cardinality** of `X` is the type `A`, and the **elements** of `X` are the multisets `f(x)` in `𝒰`, for each `x:A`.

<!-- rosetta-item-end: definition-20.6.1 -->

In the notation of multisets, the elementhood relation `{∈}:M_𝒰→M_𝒰 →𝒰^+` is defined by
```text
(X∈ {g(y)| y:B}) ≐ Σ(y:B) g(y)=X.
```
In other words, a multiset `X` is in a multiset of the form `{g(y)| y:B}` if and only if `X` comes equipped with an element `y:B` and an identification `g(y)=X`.
The W-type of multisets is extensional by Theorem 20.5.2 and the univalence axiom.

Recall from Definition 17.1.3 that for a universe `𝒰`, we say that a type `A` is (essentially) `𝒰`-small if `A` comes equipped with an element of type
```text
is-small_{𝒰}(A)≔ Σ(X:𝒰) A≃ X.
```
Our goal in this section is to show, via Russell’s paradox, that the universe `𝒰` is not `𝒰`-small, i.e., that there cannot be a type `U:𝒰` equipped with an equivalence `𝒰≃ U`.
We will use a similar condition of smallness for multisets.

## Definition 20.6.2

<!-- rosetta-item: definition-20.6.2 -->

Let `𝒰` and `𝒱` be universes.
We say that a multiset `{f(x)| x:A}` in `𝒱` **is `𝒰`-small** if the type `A` is `𝒰`-small and if each mulitset `f(x)` in `𝒱` is `𝒰`-small.
In other words, the type family
```text
is-small_M_𝒰 : M_𝒱→ 𝒱⊔𝒰^+
```
is defined recursively by
```text
is-small_M_𝒰({f(x)| x:A}) ≔ is-small_{𝒰}(A)× Π(x:A) is-small_M_𝒰(f(x)).
```

<!-- rosetta-item-end: definition-20.6.2 -->

We will need quite a few properties of smallness before we can reproduce Russell’s paradox.
We begin with a simple lemma.

## Lemma 20.6.3

<!-- rosetta-item: lemma-20.6.3; latex-label: lem:is-small-comprehension-multiset -->

Consider a `𝒰`-small multiset `{f(x)| x:A}` in `𝒱`, and let `B` be a family of `𝒰`-small types over `A`.
Then the multiset
```text
{f(x)| x:A, y:B(x)}
```
is again `𝒰`-small.

### Proof

<!-- rosetta-item: subheading-20.6-proof -->

*Proof.* If the multiset `{f(x)| x:A}` is `𝒰`-small, then the type `A` is `𝒰`-small.
By the assumption that `B` is a family of `𝒰`-small types together with the fact that `𝒰`-small types are closed under formation of `Σ`-types, it follows that the type
```text
Σ(x:A) B(x)
```
is `𝒰`-small.
Furthermore, since each `f(x)` is `𝒰`-small, we conclude that the multiset `{f(x)| x:A,y:B(x)}` is `𝒰`-small. ◻

<!-- rosetta-item-end: lemma-20.6.3 -->

The main purpose of the following lemma is to know that the elementhood relation takes values in the `𝒰`-small types, when it is applied to `𝒰`-small multisets.
We will use the univalence axiom to prove this fact.

## Proposition 20.6.4

<!-- rosetta-item: proposition-20.6.4; latex-label: prp:is-small-elementhood-multiset -->

Consider two univalent universes `𝒰` and `𝒱`, and let `X` and `Y` be `𝒰`-small multisets in `𝒱`.
We make two claims:

1.  The type `X=Y` is `𝒰`-small.

2.  The type `X∈ Y` is `𝒰`-small.

### Proof

<!-- rosetta-item: subheading-20.6-proof-2 -->

*Proof.* For the first claim, let `X≐{f(x)| x : A}` and let `Y≐{g(y)| y:B}`.
The proof is by induction.
Via Theorem 20.2.3 it follows that the type `X=Y` is equivalent to the type
```text
Σ(p:A=B) Π(x:A) f(x)=g(equiv-eq(p)).
```
The type `A=B` is `𝒰`-small because it is equivalent to the type `A≃ B`, which is `𝒰`-small.
Therefore it suffices to show that the type
```text
Π(x:A) f(x)=g(equiv-eq(p))
```
is `𝒰`-small, for every `p:A=B`.
Here we proceed by identification elimination, and the type `Π(x:A) f(x)=g(x)` is a product of `𝒰`-small types by the induction hypothesis.
This concludes the proof of the first claim.

For the second claim, let `Y≐{g(y)| y:B}`.
Then the type
```text
Σ(y:B) g(y)=X
```
is a dependent sum of `𝒰`-small types, indexed by an `𝒰`-small type, which is again `𝒰`-small. ◻

<!-- rosetta-item-end: proposition-20.6.4 -->

The condition that a multiset `{f(x)| x:A}` in `𝒱` is `𝒰`-small suggests that there is an ‘equivalent’ multiset in `𝒰`.

## Definition 20.6.5

<!-- rosetta-item: definition-20.6.5; latex-label: defn:inclusion-small-multisets -->

Given two universes `𝒰` and `𝒱`, we define an inclusion function
```text
i : (Σ(X:M_𝒱) is-small_M_𝒰(X))→M_𝒰,
```
of the `𝒰`-small multisets in `𝒱` into the multisets in `𝒰`, inductively by
```text
i({f(x)| x:A})≔ {i(f(e^{-1}(y))) | y:B}.
```
for any multiset `{f(x)| x:A}` of which the type `A` is equipped with an equivalence `e:A≃ B` for some `B` in `𝒰`, and such that the multiset `f(x)` in `𝒱` is `𝒰`-small for each `x:A`.

<!-- rosetta-item-end: definition-20.6.5 -->

## Proposition 20.6.6

<!-- rosetta-item: proposition-20.6.6; latex-label: prp:is-embedding-inclusion-small-multisets -->

The inclusion function `i` of `𝒰`-small multisets in `𝒱` into the multisets in `𝒰` satisfies the following properties

1.  For each `𝒰`-small multiset `X` in `𝒱`, the multiset `i(X)` in `𝒰` is `𝒱`-small.

2.  The induced map
```text
(Σ(X:M_𝒱) is-small_M_𝒰(X))→(Σ(Y:M_𝒰) is-small_M_𝒱(Y))
```
    is an equivalence.

Consequently, the inclusion function `i` is an embedding.

### Proof

<!-- rosetta-item: subheading-20.6-proof-3 -->

*Proof.* To see that `i({f(x)| x:A})` is `𝒱`-small for each `𝒰`-small multiset `{f(x)| x:A}` in `𝒱`, note that the assumption that `{f(x)| x:A}` is `𝒰`-small gives us an equivalence `e:A≃ B` and an element `H(x):is-small_M_𝒰(f(x))` for each `x:A`.
The type `B` is the indexing type of `i({f(x)| x:A})`, and `B` is `𝒱`-small because it is equivalent to the type `A` in `𝒱`.
Furthermore, each multiset `i(f(e^{-1}(y)))` is `𝒱`-small by the inductive hypothesis.
This completes the proof of the first claim.

We therefore have inclusion functions
<!-- rosetta-diagram: 1c65ead2ba08; review: pending -->

*Linear diagram (automatic draft).*

```text
[(Σ(X:M_𝒱) is-small_M_𝒰(X))]<--->[(Σ(Y:M_𝒰) is-small_M_𝒱(Y))]

Arrows:
- (Σ(X:M_𝒱) is-small_M_𝒰(X)) --i--> (Σ(Y:M_𝒰) is-small_M_𝒱(Y))
- (Σ(Y:M_𝒰) is-small_M_𝒱(Y)) --i--> (Σ(X:M_𝒱) is-small_M_𝒰(X))
```
To see that the maps `i` and `i` are mutual inverses, it suffices to show that `i(i(X))=X`.
This follows by induction from the following calculation, where we assume an equivalence `e:A≃ B` into a `B` in `𝒰`.
```text
i(i({f(x)| x :A})) ≐ i({i(f(e^{-1}(y)))| y:B})
≐ {i(i(f(e^{-1}(e(x))))) | x:A}
= {i(i(f(x)))| x:A}
= {f(x)| x:A}.
```

For the last claim, note that we have factored `i` as an equivalence followed by an embedding
<!-- rosetta-diagram: dcfee14f5fc4; review: pending -->

*Linear diagram (automatic draft).*

```text
[(Σ(X:M_𝒱) is-small_M_𝒰(X))]---->[(Σ(Y:M_𝒰) is-small_M_𝒱(Y))]---->[M_𝒱]

Arrows:
- (Σ(X:M_𝒱) is-small_M_𝒰(X)) --unlabeled--> (Σ(Y:M_𝒰) is-small_M_𝒱(Y))
- (Σ(Y:M_𝒰) is-small_M_𝒱(Y)) --unlabeled--> M_𝒱
```
and therefore `i` is an embedding. ◻

<!-- rosetta-item-end: proposition-20.6.6 -->

Furthermore, the embedding `i` induces equivalences on the elementhood relation on multisets.

## Proposition 20.6.7

<!-- rosetta-item: proposition-20.6.7; latex-label: prp:elementhood-small-multisets -->

Consider a multiset `X` in `𝒰` and a multiset `Y` in `𝒱`.
Furthermore, suppose that `X` is `𝒱`-small and that `Y` is `𝒰`-small.
Then we have
```text
(i(X)∈ Y)≃ (X∈ i(Y)).
```

### Proof

<!-- rosetta-item: subheading-20.6-proof-4 -->

*Proof.* Let `X≐{f(x)| x:A}` and `Y≐{g(y)| y:B}`.
By the assumption that `Y` is `𝒰`-small we have an equivalence `e:B≃ B'` to a type `B'` in `𝒰`.
Then we have the equivalences
```text
i(X) ∈ {g(y)| y:B} ≐ Σ(y:B) g(y)=i(X)
≃ Σ(y:B) i(g(y))=X
≃ Σ(y':B') i(g(e^{-1}(y')))=X
≐ X∈ i(Y).
```
 ◻

<!-- rosetta-item-end: proposition-20.6.7 -->

We are now almost in position to reproduce Russell’s paradox.
We will need one more ingredient: the universal tree, i.e., the multiset of all multisets in `𝒰`.

## Definition 20.6.8

<!-- rosetta-item: definition-20.6.8 -->

Let `𝒰` be a universe.
Then we define the **universal tree** `Y_𝒰` to be the multiset
```text
Y_𝒰:={i(X) | X:M_𝒰}
```
in `𝒰^{+}`, where `i:M_𝒰→M_𝒰^+` is the inclusion of the multisets in `𝒰` to the multisets in `𝒰^+` given by the fact that each multiset in `𝒰` is `𝒰^+`-small.

<!-- rosetta-item-end: definition-20.6.8 -->

## Proposition 20.6.9

<!-- rosetta-item: proposition-20.6.9; latex-label: prp:is-small-universal-tree -->

Consider two universes `𝒰` and `𝒱`, and suppose that `𝒰` as well as each `X:𝒰` are `𝒱`-small.
Then the universal tree `Y_𝒰` is also `𝒱`-small.

### Proof

<!-- rosetta-item: subheading-20.6-proof-5 -->

*Proof.* To show that the universal tree `{i(X)| X:M_𝒰}` is `𝒱`-small, we first have to show that the type `M_𝒰` is `𝒱`-small.
This follows from the more general fact that the subuniverse of `𝒱`-small types is closed under the formation of W-types.
Indeed, if a type `A` is `𝒱`-small, and if `B(x)` is `𝒱`-small for each `x:A`, then we have an equivalence `α:A≃ A'` to a type `A'` in `𝒱`, and for each `x':A'` we have an equivalence `B(α^{-1}(x'))≃ B'(x')` in `𝒱`.
These equivalences induce an equivalence
```text
W(A,B)≃ W(A',B')
```
into the type `W(A',B')`, which is in `𝒱`.
This concludes the proof that `M_𝒰` is `𝒱`-small.

It remains to show that the multiset `i(X)` in `𝒰^+` is `𝒱`-small, for each `X:M_𝒰`.
Equivalently, we have to show that each multiset `X` in `𝒰` is `𝒱`-small.
This follows by recursion: given a multiset `{f(x)| x:A}`, the type `A` is `𝒱`-small by assumption, and the multiset `f(x)` is `𝒱`-small by the induction hypothesis. ◻

<!-- rosetta-item-end: proposition-20.6.9 -->

We are finally ready to employ **Russell’s paradox** to prove that a univalent universe cannot be equivalent to any type it contains.

## Theorem 20.6.10

<!-- rosetta-item: theorem-20.6.10; latex-label: thm:russell -->

Consider a univalent universe `𝒰`.
Then `𝒰` cannot be `𝒰`-small.

### Proof

<!-- rosetta-item: subheading-20.6-proof-6 -->

*Proof.* Suppose that `𝒰` is `𝒰`-small, and consider the multiset
```text
R≔ {i(X) | X:M_𝒰, H : X∉ X}
```
in `𝒰^+`, where `i:M_𝒰→M_𝒰^+` is the inclusion of the multisets in `𝒰` to the multisets in `𝒰^+` given by the fact that each multiset in `𝒰` is `𝒰^+`-small.

First, we note that `R` is `𝒰`-small.
This follows from Lemma 20.6.3, using the fact that the universal tree `{i(X)| X:M_𝒰}` is `𝒰`-small by Proposition 20.6.9, and the fact that `X∈ X` is `𝒰`-small by Proposition 20.6.4.

Since `R` is `𝒰`-small, there is a multiset `R':M_𝒰` such that `i(R')=R`.
Now it follows that
```text
R∈ R ≃ Σ(X:M_𝒰) Σ(H:X∉ X) i(X)=R
≃ Σ(X:M_𝒰) Σ(H:X∉ X) X=R'
≃ R'∉ R'
≃ R∉ R.
```
In the second step we used Proposition 20.6.6, where we showed that `i` is an embedding, and in the last step we used Proposition 20.6.7.
Now we obtain a contradiction, because it follows from Exercise 4.3 that no type is (logically) equivalent to its own negation. ◻

<!-- rosetta-item-end: theorem-20.6.10 -->
