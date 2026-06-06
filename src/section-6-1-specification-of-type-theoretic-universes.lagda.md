# Section 6.1 Specification of type theoretic universes

```agda
module section-6-1-specification-of-type-theoretic-universes where
```

A universe consists of a type `𝕌` of which the elements can be thought of as
`codes` for types.
A universe also comes equipped with a type family `Ty` indexed by `𝕌`.
Given an element `X : 𝕌`, we think of the type `Ty(X)` as the type of elements
of `X`.
The family `Ty` is called the **universal type family**.

One of the distinguishing features of universes is that they are closed under
all the type constructors.
Given a universe `𝕌` with universal type family `Ty`, how do we express that
`𝕌` is closed under `Σ`-types, for example?
Recall that a `Σ`-type is formed using a type `A` and a type family `B` over
`A`.
Thus, if `A` is a type in `𝕌` and `B` is a family of types in `𝕌`, we would
like to express that the `Σ`-type is also a type in `𝕌`.
However, we cannot just assert that `Σ(x : A) B(x)` is an element of the
universe, because type theory carefully distinguishes between types and
elements.

We express that `𝕌` is closed under `Σ`-types using a new operation `Σ̌`, which
takes two arguments.
The first argument is an element `X : 𝕌`, and the second argument is a family of
types in `𝕌` indexed by the elements of `X`, i.e., a map `Ty(X) → 𝕌`.
Thus we say that `𝕌` is closed under `Σ`-types by asserting that `𝕌` comes
equipped with an operation

```text
  Σ̌ : Π(X : 𝕌) (Ty(X) → 𝕌) → 𝕌.
```

Furthermore, we ask that the element `Σ̌(X, Y) : 𝕌` satisfies the judgmental
equality

```text
  Ty(Σ̌(X, Y)) ≐ Σ(x : Ty(X)) Ty(Y(x)).
```

This judgmental equality asserts that the element `Σ̌(X, Y)` of the universe
`𝕌` *represents* the `Σ`-type `Σ(x : Ty(X)) Ty(Y(x))`.

We will similarly assume that universes are closed under `Π`-types and the other
ways of forming types.
However, there is an important restriction: it would be inconsistent to assume
that the universe is contained in itself.
One way of thinking about this is that universes are types of *small* types, and
it cannot be the case that the universe is small with respect to itself.
In the section on Russell's paradox in type theory we will use a variant of
Russell's paradox to derive a contradiction when `𝕌` is assumed to be
equivalent to a type in `𝕌`.
Instead of assuming that the universe contains itself, we will assume that there
are plenty of universes: enough universes so that any type family can be
obtained by substituting into the universal type family of some universe.

## Definition 6.1.1

A **universe** in type theory is a type `𝕌` in the empty context, equipped with
a type family `Ty` over `𝕌` called a **universal family**, that is closed under
the type forming operations in the sense that it comes equipped with the
following structure:

1. `𝕌` is closed under `Π`, in the sense that it comes equipped with a function

```text
  Π̌ : Π(X : 𝕌) (Ty(X) → 𝕌) → 𝕌
```

for which the judgmental equality

```text
  Ty(Π̌(X, Y)) ≐ Π(x : Ty(X)) Ty(Y(x))
```

holds, for every `X : 𝕌` and `Y : Ty(X) → 𝕌`.

2. `𝕌` is closed under `Σ` in the sense that it comes equipped with a function

```text
  Σ̌ : Π(X : 𝕌) (Ty(X) → 𝕌) → 𝕌
```

for which the judgmental equality

```text
  Ty(Σ̌(X, Y)) ≐ Σ(x : Ty(X)) Ty(Y(x))
```

holds, for every `X : 𝕌` and `Y : Ty(X) → 𝕌`.

3. `𝕌` is closed under identity types, in the sense that it comes equipped with
a function

```text
  Ǐ : Π(X : 𝕌) Ty(X) → (Ty(X) → 𝕌)
```

for which the judgmental equality

```text
  Ty(Ǐ(X, x, y)) ≐ (x = y)
```

holds, for every `X : 𝕌` and `x, y : Ty(X)`.

4. `𝕌` is closed under coproducts, in the sense that it comes equipped with a
function

```text
  _+̌_ : 𝕌 → (𝕌 → 𝕌)
```

that satisfies `Ty(X +̌ Y) ≐ Ty(X) + Ty(Y)`.

5. `𝕌` contains elements `∅̌, 𝟙̌, ℕ̌ : 𝕌` that satisfy the judgmental equalities

```text
  Ty(∅̌) ≐ ∅
  Ty(𝟙̌) ≐ 𝟙
  Ty(ℕ̌) ≐ ℕ.
```

Consider a universe `𝕌` and a type `A` in context `Γ`.
We say that `A` is a type in `𝕌`, or that `𝕌` **contains** `A`, if `𝕌` comes
equipped with an element `Ǎ : 𝕌` in context `Γ`, for which the judgment

```text
  Γ ⊢ Ty(Ǎ) ≐ A type
```

holds.
If `A` is a type in `𝕌`, we usually write simply `A` for `Ǎ` and also `A` for
`Ty(Ǎ)`.

## Remark 6.1.2

Since ordinary function types are defined as a special case of dependent
function types, we don't have to assume separately that universes are closed
under ordinary function types.
Similarly, it follows from the assumption that universes are closed under
dependent pair types that universes are closed under cartesian product types.
