# Section 11.2 The fundamental theorem

```agda
module section-11-2-the-fundamental-theorem where
```

The fundamental theorem of identity types is a general theorem that can be used
to characterize the identity type of a given type.
It describes necessary and sufficient conditions on a type family `B` over a
type `A` equipped with a point `a : A` to obtain an equivalence
`(a = x) ≃ B(x)` for each `x : A`.

One of those conditions is that the family `B` satisfies an induction principle
that is similar to the identification elimination principle.
Such families are called *identity systems*, which we introduce now.

## Definition 11.2.1

Let `A` be a type equipped with a term `a : A`.
A **unary identity system** on `A` at `a` consists of a type family `B` over `A`
equipped with `b : B(a)`, such that for any family of types `P(x, y)` indexed by
`x : A` and `y : B(x)`, the function

```text
  h ↦ h(a, b) :
    (Π(x : A) Π(y : B(x)) P(x, y)) → P(a, b)
```

has a section.

In other words, if `B` is an identity system on `A` at `a` and `P` is a family
of types indexed by `x : A` and `y : B(x)`, then there is for each
`p : P(a, b)` a dependent function

```text
  f : Π(x : A) Π(y : B(x)) P(x, y)
```

such that `f(a, b) = p`.
This is a variant of identification elimination, where the computation rule is
given by an identification rather than as a judgmental equality.

We will state the fundamental theorem of identity types in a way that makes it
maximally applicable.
The fundamental theorem starts off with assuming a type `A` equipped with a base
point `a : A`, and a type family `B` over `A` equipped with a point `b : B(a)`.
Furthermore it assumes an arbitrary family of maps

```text
  f : Π(x : A) (a = x) → B(x)
```

equipped with an identification `f(a, refl(a)) = b`.
The theorem asserts conditions that are equivalent to `f` being a family of
equivalences.

In the setup of the fundamental theorem of identity types we can always
construct the family of maps

```text
  f := path-ind_a(b) : Π(x : A) (a = x) → B(x)
```

for which the judgmental equality `f(a, refl(a)) ≐ b` holds.
We formulate the theorem using a general family of maps `f` because it is common
to apply the theorem to conclude that a non-canonical family of maps is a family
of equivalences.

The most important implication in the fundamental theorem is that the
contractibility of the total space implies that `f` is a family of equivalences.
Occasionally we will also use the third equivalent statement.

## Theorem 11.2.2

Let `A` be a type with `a : A`, and let `B` be a type family over `A` equipped
with a point `b : B(a)`.
Furthermore, consider a family of maps

```text
  f : Π(x : A) (a = x) → B(x)
```

equipped with an identification `f(a, refl(a)) = b`.
Then the following are equivalent:

1. The family of maps `f` is a family of equivalences.
2. The total space

```text
  Σ(x : A) B(x)
```

is contractible.
3. The family `B` equipped with `b : B(a)` is an identity system.

In particular, we see that for any `b : B(a)`, the canonical family of maps

```text
  path-ind_a(b) : Π(x : A) (a = x) → B(x)
```

is a family of equivalences if and only if `Σ(x : A) B(x)` is contractible.

## Proof

First we show that the first and second statements are equivalent.
By Theorem 11.1.3 it follows that the family of maps `f` is a family of
equivalences if and only if it induces an equivalence

```text
  (Σ(x : A) a = x) ≃ (Σ(x : A) B(x))
```

on total spaces.
We have that `Σ(x : A) a = x` is contractible, so it follows by Exercise 10.3
that `tot(f)` is an equivalence if and only if `Σ(x : A) B(x)` is contractible.

Now we show that the second and third statements are equivalent.
There is a commuting triangle

```text
  Π(t : Σ(x : A) B(x)) P(t)  -->  Π(x : A) Π(y : B(x)) P(x, y)
              \                         /
               \                       /
                    P(a, b).
```

In this diagram the top map has a section.
Therefore it follows by Exercise 9.4 that the left map has a section if and only
if the right map has a section.
Recall from Definition 10.2.1 that the type `Σ(x : A) B(x)` satisfies singleton
induction if and only if the left map in the triangle has a section for each
`P`.
Therefore we conclude our proof with Theorem 10.2.3, which shows that the type
`Σ(x : A) B(x)` satisfies singleton induction if and only if it is contractible.
