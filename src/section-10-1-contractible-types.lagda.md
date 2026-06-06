# Section 10.1 Contractible types

```agda
module section-10-1-contractible-types where
```

## Definition 10.1.1

We say that a type `A` is **contractible** if it comes equipped with an element
of type

```text
  is-contr(A) := Σ(c : A) Π(x : A) c = x.
```

Given a pair `(c, C) : is-contr(A)`, we call `c : A` the **center of
contraction** of `A`, and we call `C : Π(x : A) c = x` the **contraction** of
`A`.

## Remark 10.1.2

Suppose `A` is a contractible type with center of contraction `c` and
contraction `C`.
Then the type of `C` is judgmentally equal to the type

```text
  const_c ~ id_A.
```

In other words, the contraction `C` is a *homotopy* from the constant function
to the identity function.

## Example 10.1.3

The unit type is easily seen to be contractible.
For the center of contraction we take `⋆ : 𝟙`.
Then we define a contraction `Π(x : 𝟙) ⋆ = x` by the induction principle of
`𝟙`.
Applying the induction principle, it suffices to construct an identification of
type `⋆ = ⋆`, for which we just take `refl(⋆)`.

## Theorem 10.1.4

For any `a : A`, the type

```text
  Σ(x : A) a = x
```

is contractible.

## Proof

For the center of contraction we take

```text
  (a, refl(a)) : Σ(x : A) a = x.
```

The contraction is constructed later as Proposition 11.2.2.
