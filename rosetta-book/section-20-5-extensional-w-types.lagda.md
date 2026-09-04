# Section 20.5 Extensional W-types

```agda
module section-20-5-extensional-w-types where
```

<!-- rosetta-item: section-20.5 -->

It is tempting to think that an element `w:W(A,B)` is completely determined by the elements `z:W(A,B)` equipped with a proof `z∈ w`.
However, this may not be the case.
For instance, a W-type `W(A,B)` might have *two* unary constructors, e.g., when `A≔ unit+bool` and the family `B` over `A` is given by
```text
B(inl(x)) ≔ empty
B(inr(y)) ≔ unit.
```
If we write `f` and `g` for the two unary constructors of `W(A,B)`, then we see that for any element `w:W(A,B)`, the elements
```text
u≔tree(inr(false),const_w) and v≔tree(inr(true),const_w)
```
both only contain the element `w`.
However, the elements `u` and `v` are distinct in `W(A,B)`.

Something similar happens in the type of oriented binary rooted trees.
Given two binary rooted trees `S` and `T`, there are two ways to combine `S` and `T` into a new binary tree: we have `[S,T]` and `[T,S]`.
Both contain precisely the elements `S` and `T`, but they are distinct.
Nevertheless, there are many important W-types in which the elements `w` are uniquely determined by the elements `z∈ w`.
Such W-types are called extensional.

## Definition 20.5.1

<!-- rosetta-item: definition-20.5.1 -->

We say that a W-type `W(A,B)` is **extensional** if the canonical map
```text
(x=y)→Π(z:W(A,B)) (z∈ x)≃ (z∈ y)
```
is an equivalence.

<!-- rosetta-item-end: definition-20.5.1 -->

In the following theorem we give a precise characterization of the inhabited extensional W-types.

## Theorem 20.5.2

<!-- rosetta-item: theorem-20.5.2; latex-label: thm:extensional-W -->

Consider an inhabited W-type `W(A,B)`.
Then the following are equivalent:

1.  The W-type `W(A,B)` is extensional.

2.  The family `B` is **univalent** in the sense that the map
```text
tr_B:(x=y)→ (B(x)≃ B(y))
```
    is an equivalence, for every `x,y:A`.

<!-- rosetta-item-end: theorem-20.5.2 -->

## Remark 20.5.3

<!-- rosetta-item: remark-20.5.3 -->

Note that if the W-type `W(A,B)` is empty, then it is vacuously extensional.
However, we saw in Proposition 20.1.5 that any family `B` of inhabited types over `A` gives rise to an empty W-type `W(A,B)`, so there is no hope of showing that `B` is a univalent family if `W(A,B)` is empty.

We also note that a type family `B` over `A` is univalent if and only if the map `B:A→ 𝒰` is an embedding.
In other words, the claim in Theorem 20.5.2 is that an inhabited W-type `W(A,B)` is extensional if and only if `B` is the canonical type family over a subuniverse `A` of `𝒰`.

### Proof

<!-- rosetta-item: subheading-20.5-proof -->

*Proof.* We will first show that (ii) is equivalent to the following property:

1.  The map
```text
tr_B : (symbol(x)=y)→ (B(symbol(x))≃ B(y))
```
    is an equivalence for every `x:W(A,B)` and every `y:A`.

Clearly, (ii) implies (ii’).
For the converse we use the assumption that `W(A,B)` is inhabited.
Since the property in (ii) is a proposition, we may assume an element `w:W(A,B)`.
Using `w`, we obtain for every `x:A` the element
```text
tree(x,const_w):W(A,B)
```
The symbol of `tree(x,const_w)` is `x`, and therefore the hypothesis that (ii’) holds implies that the map `(x=y)→ (B(x)≃ B(y))` is an equivalence.
This concludes the proof that (ii) is equivalent to (ii’).
It remains to show that (i) is equivalent to (ii’).

Let `x:W(A,B)`.
By the fundamental theorem of identity types, the W-type `W(A,B)` is extensional if and only if the total space
```text
Σ(y:W(A,B)) Π(z:W(A,B)) (z∈ x)≃ (z∈ y)
```
is contractible, for any `x:W(A,B)`.
When `x` is of the form `tree(a,α)`, the type `z∈ x` is just the fiber `fib(α, z)`.
Using this observation, we see that the above type is equivalent to the type
```text
Σ(b:A) Σ(β:B(b)→W(A,B)) Π(z:W(A,B)) fib(α, z)≃fib(β, z).(*)
```
By Exercise 13.15 it follows that this type is equivalent to the type
```text
Σ(y:A) Σ(β:B(y)→W(A,B)) Σ(e:B(x)≃ B(y)) α~ e∘ β.
```
Note that the type `Σ(β:B(y)→W(A,B)) α~ e∘β` is contractible for any equivalence `e:B(x)≃ B(y)`.
Therefore, it follows that the above type is contractible if and only if the type
```text
Σ(y:A) B(x)≃ B(y)
```
is contractible, which is the case if and only if the map `(x=y)→(B(x)≃ B(y))` is an equivalence for all `y:A`. ◻

<!-- rosetta-item-end: remark-20.5.3 -->

## Example 20.5.4

<!-- rosetta-item: example-20.5.4 -->

The type `N` of Example 20.1.6, the type of binary rooted trees Example 20.1.8, and the type of finitely branching rooted trees Example 20.1.9 are all examples extensional W-types.
On the other hand, the type of oriented binary rooted trees of Example 20.1.7 and the type of oriented finitely branching rooted trees of Example 20.1.9 are not extensional.

<!-- rosetta-item-end: example-20.5.4 -->
