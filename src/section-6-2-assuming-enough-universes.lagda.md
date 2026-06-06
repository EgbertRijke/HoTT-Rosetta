# Section 6.2 Assuming enough universes

```agda
module section-6-2-assuming-enough-universes where
```

Most of the time we will get by with assuming one universe `𝕌`, and indeed we
recommend on a first reading of this text to simply assume that there is one
universe `𝕌`.
However, sometimes we might want to consider the universe `𝕌` itself to be a
type in some universe.
In such situations we cannot get by with a single universe, because the
assumption that `𝕌` is an element of itself would lead to inconsistencies like
Russell's paradox.

Russell's paradox is the famous argument that there cannot be a set of all sets.
If there were such a set `S`, then we could consider Russell's subset

```text
  R := {x ∈ S | x ∉ x}.
```

Russell then observed that `R ∈ R` if and only if `R ∉ R`, so we reach a
contradiction.
A variant of this argument reaches a similar contradiction when we assume that
`𝕌` is a universe that contains an element `𝕌̌ : 𝕌` such that
`Ty(𝕌̌) ≐ 𝕌`.
In order to avoid such paradoxes, Russell and Whitehead formulated the
*ramified theory of types* in their book *Principia Mathematica*.
The ramified theory of types is a precursor of Martin-Löf's type theory that we
are studying in this book.

Even though the universe is not an element of itself, it is still convenient if
every type, including any universe, is in *some* universe.
Therefore we will assume that there are sufficiently many universes:

## Postulate 6.2.1

We assume that there are **enough universes**, i.e., that for every finite list
of types in context

```text
  Γ₁ ⊢ A₁ type    ...    Γₙ ⊢ Aₙ type,
```

there is a universe `𝕌` that contains each `Aᵢ` in the sense that `𝕌` comes
equipped with

```text
  Γᵢ ⊢ Ǎᵢ : 𝕌
```

for which the judgment

```text
  Γᵢ ⊢ Ty(Ǎᵢ) ≐ Aᵢ type
```

holds.

With this assumption it will rarely be necessary to work with more than one
universe at the same time.
Using the assumption that for any finite list of types in context there is a
universe that contains those types, we obtain many specific universes.

## Definition 6.2.2

The **base universe** `𝕌₀` is the universe that we obtain using the postulate of
enough universes with the empty list of types in context.

In other words, the base universe is a universe that is closed under all the ways
of forming types, but it isn't specified to contain any further types.

## Definition 6.2.3

The **successor universe** of a universe `𝕌` is the universe `𝕌⁺` obtained using
the postulate of enough universes with the finite list

```text
        ⊢ 𝕌 type
  X : 𝕌 ⊢ Ty(X) type.
```

## Remark 6.2.4

The successor universe `𝕌⁺` of `𝕌` therefore contains the type `𝕌` as well as
every type in `𝕌`, in the following sense

```text
        ⊢ 𝕌̌ : 𝕌⁺              ⊢ Ty⁺(𝕌̌) ≐ 𝕌 type
  X : 𝕌 ⊢ Ty̌(X) : 𝕌⁺    X : 𝕌 ⊢ Ty⁺(Ty̌(X)) ≐ Ty(X) type.
```

In particular, we obtain a function `i : 𝕌 → 𝕌⁺` that includes the types in `𝕌`
into `𝕌⁺`, given by

```text
  i := λ X. Ty̌(X).
```

Using successor universes we can create an infinite tower

```text
  𝕌, 𝕌⁺, 𝕌⁺⁺, ...
```

of universes, starting at any universe `𝕌`, in which each universe is contained
in the next.
However, such towers of universes need not be exhaustive in the sense that it
might not be the case that every type is contained in a universe in this tower.

## Definition 6.2.5

The **join** of two universes `𝕌` and `𝕍` is the universe `𝕌 ⊔ 𝕍` that we obtain
using the postulate of enough universes with the two types

```text
  X : 𝕌 ⊢ Ty_𝕌(X) type
  Y : 𝕍 ⊢ Ty_𝕍(Y) type.
```

## Remark 6.2.6

Since the join `𝕌 ⊔ 𝕍` contains all the types in `𝕌` and `𝕍`, there are maps

```text
  i : 𝕌 → 𝕌 ⊔ 𝕍
  j : 𝕍 → 𝕌 ⊔ 𝕍.
```

Note that we don't postulate any relations between the universes.
In general it will therefore be the case that the universes
`(𝕌 ⊔ 𝕍) ⊔ 𝕎` and `𝕌 ⊔ (𝕍 ⊔ 𝕎)` will be unrelated.
