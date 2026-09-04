# Section 6.1 Specification of type theoretic universes

```agda
module section-6-1-specification-of-type-theoretic-universes where
```

<!-- rosetta-item: section-6.1 -->

A universe consists of a type `𝒰` of which the elements can be thought of as ‘codes’ for types.
A universe also comes equipped with a type family `Ty` indexed by `𝒰`.
Given an element `X:𝒰`, we think of the type `Ty(X)` as the type of elements of `X`.
The family `Ty` is called the **universal type family**.

One of the distinguishing features of universes is that they are closed under all the type constructors.
Given a universe `𝒰` with universal type family `Ty`, how do we express that `𝒰` is closed under `Σ`-types, for example?
Recall that a `Σ`-type is formed using a type `A` and a type family `B` over `A`.
Thus, if `A` is a type in `𝒰` and `B` is a family of types in `𝒰`, we would like to express that the `Σ`-type is also a type in `𝒰`.
However, we cannot just assert that `Σ(x:A) B(x)` is an element of the universe, because type theory carefully distinguishes between types and elements.

We express that `𝒰` is closed under `Σ`-types using a new operation `Σ̌`, which takes two arguments.
The first argument is an element `X:𝒰`, and the second argument is a family of types in `𝒰` indexed by the elements of `X`, i.e., a map `Ty(X)→𝒰`.
Thus we say that `𝒰` is closed under `Σ`-types by asserting that `𝒰` comes equipped with an operation
```text
Σ̌ : Π(X:𝒰) (Ty(X)→𝒰)→𝒰
```
Furthermore, we ask that the element `Σ̌(X,Y):𝒰` satisfies the judgmental equality
```text
Ty(Σ̌(X,Y))≐Σ(x:Ty(X)) Ty(Y(x)).
```
This judgmental equality asserts that the element `Σ̌(X,Y)` of the universe `𝒰` *represents* the `Σ`-type `Σ(x:Ty(X)) Ty(Y(x))`.

We will similarly assume that universes are closed under `Π`-types and the other ways of forming types.
However, there is an important restriction: it would be inconsistent to assume that the universe is contained in itself.
One way of thinking about this is that universes are types of *small* types, and it cannot be the case that the universe is small with respect to itself.
In Section 20.6 we will use a variant of Russell’s paradox to derive a contradiction when `𝒰` is assumed to be (equivalent to a type) in `𝒰`.
Instead of assuming that the universe contains itself, we will assume that there are plenty of universes: enough universes so that any type family can be obtained by substituting into the universal type family of some universe.

## Definition 6.1.1

<!-- rosetta-item: definition-6.1.1; latex-label: defn:universe -->

A **universe** in type theory is a type `𝒰` in the empty context, equipped with a type family `Ty` over `𝒰` called a **universal family**, that is closed under the type forming operations in the sense that it comes equipped with the following structure:

1.  `𝒰` is closed under `Π`, in the sense that it comes equipped with a function
```text
Π̌ :Π(X:𝒰) (Ty(X)→𝒰)→𝒰
```
    for which the judgmental equality
```text
Ty(Π̌(X,Y))≐ Π(x:Ty(X)) Ty(Y(x)).
```
    holds, for every `X:𝒰` and `Y:Ty(X)→𝒰`.

2.  `𝒰` is closed under `Σ` in the sense that it comes equipped with a function
```text
Σ̌ :Π(X:𝒰) (Ty(X)→𝒰)→𝒰
```
    for which the judgmental equality
```text
Ty(Σ̌(X,Y)) ≐ Σ(x:Ty(X)) Ty(Y(x))
```
    holds, for every `X:𝒰` and `Y:Ty(X)→𝒰`.

3.  `𝒰` is closed under identity types, in the sense that it comes equipped with a function
```text
Ǐ : Π(X:𝒰) Ty(X)→(Ty(X)→𝒰)
```
    for which the judgmental equality
```text
Ty(Ǐ(X,x,y))≐ (x = y)
```
    holds, for every `X:𝒰` and `x,y:Ty(X)`.

4.  `𝒰` is closed under coproducts, in the sense that it comes equipped with a function
```text
\mathbin{+̌}:𝒰→ (𝒰→𝒰)
```
    that satisfies `Ty(X\mathbin{+̌}Y)≐ Ty(X)+Ty(Y)`.

5.  `𝒰` contains elements `empty̌,uniť,ℕ̌:𝒰` that satisfy the judgmental equalities
```text
Ty(empty̌) ≐ empty
Ty(uniť) ≐ unit
Ty(ℕ̌) ≐ ℕ.
```

Consider a universe `𝒰` and a type `A` in context `Γ`.
We say that `A` is a type in `𝒰`, or that `𝒰` **contains** `A`, if `𝒰` comes equipped with an element `Ǎ:𝒰` in context `Γ`, for which the judgment
```text
Γ⊢Ty(Ǎ)≐ A \type
```
holds.
If `A` is a type in `𝒰`, we usually write simply `A` for `Ǎ` and also `A` for `Ty(Ǎ)`.

<!-- rosetta-item-end: definition-6.1.1 -->

## Remark 6.1.2

<!-- rosetta-item: remark-6.1.2 -->

Since ordinary function types are defined as a special case of dependent function types, we don’t have to assume separately that universes are closed under ordinary function types.
Similarly, it follows from the assumption that universes are closed under dependent pair types that universes are closed under cartesian product types.

<!-- rosetta-item-end: remark-6.1.2 -->
