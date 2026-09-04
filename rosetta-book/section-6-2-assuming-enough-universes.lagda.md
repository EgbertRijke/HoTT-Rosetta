# Section 6.2 Assuming enough universes

```agda
module section-6-2-assuming-enough-universes where
```

<!-- rosetta-item: section-6.2 -->

Most of the time we will get by with assuming one universe `𝒰`, and indeed we recommend on a first reading of this text to simply assume that there is one universe `𝒰`.
However, sometimes we might want to consider the universe `𝒰` itself to be a type in some universe.
In such situations we cannot get by with a single universe, because the assumption that `𝒰` is a element of itself would lead to inconsistencies like the Russell’s paradox.

Russell’s paradox is the famous argument that there cannot be a set of all sets.
If there were such a set `S`, then we could consider Russell’s subset
```text
R:={x∈ S| x∉ x}.
```
Russell then observed that `R∈ R` if and only if `R∉ R`, so we reach a contradiction.
A variant of this argument reaches a similar contradiction when we assume that `𝒰` is a universe that contains an element `𝒰̌:𝒰` such that `T(𝒰̌)≐ 𝒰`.
In order to avoid such paradoxes, Russell and Whitehead formulated the *ramified theory of types* in their book *Principia Mathematica*.
The ramified theory of types is a precursor of Martin Löf’s type theory that we are studying in this book.

Even though the universe is not an element of itself, it is still convenient if every type, including any universe, is in *some* universe.
Therefore we will assume that there are sufficiently many universes:

## Postulate 6.2.1

<!-- rosetta-item: postulate-6.2.1; latex-label: enough-universes -->

We assume that there are **enough universes**, i.e., that for every finite list of types in context
```text
Γ_1⊢ A_1 \type ⋯ Γ_n⊢ A_n \type,
```
there is a universe `𝒰` that contains each `A_i` in the sense that `𝒰` comes equipped with
```text
Γ_i⊢ Ǎ_i:𝒰
```
for which the judgment
```text
Γ_i⊢ Ty(Ǎ_i)≐ A_i \type
```
holds.

<!-- rosetta-item-end: postulate-6.2.1 -->

With this assumption it will rarely be necessary to work with more than one universe at the same time.
Using the assumption that for any finite list of types in context there is a universe that contains those types, we obtain many specific universes.

## Definition 6.2.2

<!-- rosetta-item: definition-6.2.2 -->

The **base universe** `𝒰_0` is the universe that we obtain using Postulate 6.2.1 with the empty list of types in context.

<!-- rosetta-item-end: definition-6.2.2 -->

In other words, the base universe is a universe that is closed under all the ways of forming types, but it isn’t specified to contain any further types.

## Definition 6.2.3

<!-- rosetta-item: definition-6.2.3; latex-label: defn:successor-universe -->

The **successor universe** of a universe `𝒰` is the universe `𝒰^+` obtained using Postulate 6.2.1 with the finite list
```text
⊢ 𝒰 \type
X:𝒰 ⊢ T(X) \type.
```

<!-- rosetta-item-end: definition-6.2.3 -->

## Remark 6.2.4

<!-- rosetta-item: remark-6.2.4; latex-label: rmk:successor-universe -->

The successor universe `𝒰^+` of `𝒰` therefore contains the type `𝒰` as well as every type in `𝒰`, in the following sense
```text
⊢ 𝒰̌:𝒰^+  ⊢ T^+(𝒰̌)≐𝒰 \type
X:𝒰 ⊢ Ť(X) :𝒰^+ X:𝒰 ⊢ T^+(Ť(X))≐ T(X) \type.
```
In particular, we obtain a function `i:𝒰→𝒰^+` that includes the types in `𝒰` into `𝒰^+`, given by
```text
i≔ λ X. Ť(X).
```

Using successor universes we can create an infinite tower
```text
𝒰,\ 𝒰^+,\ 𝒰^{++},\ …
```
of universes, starting at any universe `𝒰`, in which each universe is contained in the next.
However, such towers of universes need not be exhaustive in the sense that it might not be the case that every type is contained in a universe in this tower.

<!-- rosetta-item-end: remark-6.2.4 -->

## Definition 6.2.5

<!-- rosetta-item: definition-6.2.5; latex-label: defn:join-universe -->

The **join** of two universes `𝒰` and `𝒱` is the universe `𝒰⊔𝒱` that we obtain using Postulate 6.2.1 with the two types
```text
X:𝒰 ⊢ T_{𝒰}(X) \type
Y:𝒱 ⊢ T_{𝒱}(Y) \type.
```

<!-- rosetta-item-end: definition-6.2.5 -->

## Remark 6.2.6

<!-- rosetta-item: remark-6.2.6; latex-label: rmk:join-universe -->

Since the join `𝒰⊔𝒱` contains all the types in `𝒰` and `𝒱`, there are maps
```text
i : 𝒰→𝒰⊔𝒱
j : 𝒱→𝒰⊔𝒱
```
Note that we don’t postulate any relations between the universes.
In general it will therefore be the case that the universes `(𝒰⊔𝒱)⊔W` and `𝒰⊔(𝒱⊔W)` will be unrelated.

<!-- rosetta-item-end: remark-6.2.6 -->
