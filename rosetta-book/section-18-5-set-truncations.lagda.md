# Section 18.5 Set truncations

```agda
module section-18-5-set-truncations where
```

<!-- rosetta-item: section-18.5 -->

An important instance of set quotients in the univalent foundations of mathematics is the notion of set truncation.
Analogous to the propositional truncation, the set truncation of a type `A` is a map `η:A→ ‖A‖_0` into a set `‖A‖_0` such that any map `f:A→ X` into a set `X` extends uniquely along `η`:
<!-- rosetta-diagram: 1273e5fb6567; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
  [A]
   |
[‖A‖_0]----> [X]

Arrows:
- A --f--> X
- A --η--> ‖A‖_0
- ‖A‖_0 --unlabeled--> X
```
In other words, the set truncation `η:A→‖A‖_0` is the universal way of mapping `A` into a set.
We first specify what it means for a map `f:A→ B` into a set `B` to be a set truncation of `A`.

## Definition 18.5.1

<!-- rosetta-item: definition-18.5.1 -->

We say that a map `f:A→ B` into a set `B` is a **set truncation** if the precomposition function
```text
_∘ f : (B→ X)→ (A→ X)
```
is an equivalence for every set `X`.

<!-- rosetta-item-end: definition-18.5.1 -->

In the following theorem we prove several conditions that are equivalent to being a set truncation.

## Theorem 18.5.2

<!-- rosetta-item: theorem-18.5.2; latex-label: thm:set-truncation -->

Consider a map `f:A→ B` into a set `B`.
Then the following are equivalent:

1.  The map `f` is a set truncation.

2.  The map `f` satisfies the **dependent universal property** of the set truncation: For every family `X` of sets over `B`, the precomposition function
```text
_∘ f : (Π(b:B) X(b))→(Π(a:A) X(f(a)))
```
    is an equivalence.

3.  The map `f` is surjective and effective with respect to the equivalence relation `x,y↦‖x=y‖`, i.e., we have equivalences
```text
(f(x)=f(y))≃ ‖x=y‖
```
    for every `x,y:A`.

### Proof

<!-- rosetta-item: subheading-18.5-proof -->

*Proof.* The fact that (2) implies (1) is immediate.
Moreover, the fact that (1) is equivalent to (3) follows from the fact that any map `h:A→ X` into a set `X` comes equipped with a function
```text
‖x=y‖→ (h(x)=h(y))
```
for every `x,y:A`.

It remains to prove that (1) implies (2).
Consider a family `X` of sets over `B`, and consider the commuting square
<!-- rosetta-diagram: 6bbb9693a0b2; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[Σ(g:B→ B) Π(b:B) X(g(b))]---->[Σ(h:A→ B) Π(a:A) X(h(a))]
            |                              |
    [(B→Σ(b:B) X(b))]     ---->    [(A→Σ(b:B) X(b))]

Arrows:
- Σ(g:B→ B) Π(b:B) X(g(b)) --≃--> (B→Σ(b:B) X(b))
- Σ(g:B→ B) Π(b:B) X(g(b)) --{(g,s)↦ (g∘ f,s∘ f)}--> Σ(h:A→ B) Π(a:A) X(h(a))
- Σ(h:A→ B) Π(a:A) X(h(a)) --≃--> (A→Σ(b:B) X(b))
- (B→Σ(b:B) X(b)) --_∘ f--> (A→Σ(b:B) X(b))
```
The side maps are equivalences by the distributivity of `Π` over `Σ`, and the bottom map is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows that the top map is an equivalence.
Furthermore, note that the map
```text
_∘ f : (B→ B)→ (A→ B)
```
is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows from Theorem 11.1.6 that the map
```text
_∘ f : (Π(b:B) X(g(b)))→ (Π(a:A) X(g(f(a))))
```
is an equivalence for every `g:B→ B`.
Now we take `g≔ id` to complete the proof that (1) implies (2). ◻

<!-- rosetta-item-end: theorem-18.5.2 -->

## Corollary 18.5.3

<!-- rosetta-item: corollary-18.5.3 -->

On any universe `𝒰`, there is an operation `‖_‖_0:𝒰→Set_𝒰` such that every type `A` in `𝒰` comes equipped with a map
```text
η:A→‖A‖_0
```
that satisfies the universal property of the set truncation.
The set `‖A‖_0` is called the **set truncation** of `A`.

### Proof

<!-- rosetta-item: subheading-18.5-proof-2 -->

*Proof.* By Theorem 18.5.2 it follows that a map `f:A→ B` into a set `B` is a set truncation if and only if it is a quotient map with respect to the equivalence relation `x,y↦‖x=y‖`.
Given a type `A` in `𝒰`, the quotient of `A` by `x,y↦‖x=y‖` is equivalent to a type in `𝒰` by the replacement axiom. ◻

<!-- rosetta-item-end: corollary-18.5.3 -->

## Corollary 18.5.4

<!-- rosetta-item: corollary-18.5.4 -->

The set truncation `η:A→‖A‖_0` is surjective and effective with respect to the equivalence relation `x,y↦‖x=y‖`, i.e., we have an equivalence
```text
(η(x)=η(y))≃ ‖x=y‖
```
for each `x,y:A`.

<!-- rosetta-item-end: corollary-18.5.4 -->

By this corollary, we may think of the set truncation `‖A‖_0` of `A` as the set of connected components of `A`.
Indeed, if we have an unspecified identification `‖x=y‖` in `A`, then we think of `x` and `y` as being in the same connected component.
For example, any `k`-element set is a type that is in the same connected component of `𝒰` as the type `Fin{k}`.

## Definition 18.5.5

<!-- rosetta-item: definition-18.5.5 -->

A type `A` is said to be **connected** if its set truncation `‖A‖_0` is contractible.
We define
```text
is-conn(A)≔is-contr‖A‖_0.
```
Furthermore, we say that a map `f:A→ B` is **connected** if all its fibers are connected.

<!-- rosetta-item-end: definition-18.5.5 -->

## Remark 18.5.6

<!-- rosetta-item: remark-18.5.6 -->

In particular, every connected type is inhabited, because if `‖A‖_0` is contractible, then we have equivalences
```text
‖A‖≃ (‖A‖_0→‖A‖) ≃ (A→ ‖A‖),
```
and the latter type contains the unit of the propositional truncation.

<!-- rosetta-item-end: remark-18.5.6 -->

Using the notion of connectivity, we can add one more property to the list of equivalent characterizations of set truncations given in Theorem 18.5.2.

## Theorem 18.5.7

<!-- rosetta-item: theorem-18.5.7; latex-label: thm:unit-set-truncation-connected -->

Consider a map `f:A→ B` into a set `B`.
Then the following are equivalent:

1.  The map `f` is a set truncation.

2.  The map `f` is connected.

### Proof

<!-- rosetta-item: subheading-18.5-proof-3 -->

*Proof.* First, suppose that `f` is a set truncation, and consider `b:B`.
Our goal is to show that the type
```text
‖fib(f, b)‖_0
```
is contractible.
Since `f` is surjective by Theorem 18.5.2, there exists an element `a:A` equipped with an identification `f(a)=b`.
We are proving a proposition, so it suffices to show that `‖fib(f, f(a))‖_0` is contractible.
At the center of contraction we have
```text
η(a,refl):‖fib(f, f(a))‖_0.
```
In order to construct the contraction, we use the dependent universal property of the set truncation, by which it suffices to construct a function
```text
Π(x:A) Π(p:f(x)=f(a)) η(a,refl)=η(x,p)
```
Recall from Theorem 18.5.2 that the map `f` is effective, so we have an equivalence `e:‖x=a‖≃ (f(x)=f(a))` for every `x:A`.
Furthermore, equality in set truncations are propositions, so we may even eliminate the propositional truncation from `‖x=a‖`.
Therefore it suffices to prove
```text
Π(x:A) Π(p:x=a) η(a,refl)=η(x,e(η(p)))
```
This is immediate, since `e(η(refl))=refl`.
This completes the proof of (1) implies (2).

For the converse, suppose that `f` is connected, and consider a set `X`.
Note that we have a commuting square
<!-- rosetta-diagram: 788b395e94a0; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
[(Π(b:B) ‖fib(f, b)‖_0→ X)]---->[(Π(b:B) fib(f, b)→ X)]
             |                             |
          [(B→ X)]         ---->        [(A→ X)]

Arrows:
- (Π(b:B) ‖fib(f, b)‖_0→ X) --{h↦λ b. {t}h(b,η(t))}--> (Π(b:B) fib(f, b)→ X)
- (Π(b:B) fib(f, b)→ X) --{h↦λ a. h(f(a),(a,refl))}--> (A→ X)
- (B→ X) --_∘ f--> (A→ X)
- (B→ X) --h↦λ b. λ u. h(b)--> (Π(b:B) ‖fib(f, b)‖_0→ X)
```
In this commuting square, the map on the left is an equivalence since `‖fib(f, b)‖_0` is contractible for each `b:B`.
The top map is an equivalence because `X` is a set, and the right map is an equivalence by Exercise 13.15.
Therefore it follows that the bottom map is an equivalence, which completes the proof that (2) implies (1). ◻

<!-- rosetta-item-end: theorem-18.5.7 -->

## Remark 18.5.8

<!-- rosetta-item: remark-18.5.8 -->

There are truncation operations for every truncation level.
That is, we can define for every type `A` a map `η:A→‖A‖_k` such that the map
```text
_∘η : (‖A‖_k→ X)→ (A→ X)
```
is an equivalence for every `k`-truncated type `X`.
To learn more about general `k`-truncations, we refer to Chapter 7 of .

<!-- rosetta-item-end: remark-18.5.8 -->
