# Section 9.2 Bi-invertible maps

```agda
module section-9-2-bi-invertible-maps where
```

We use homotopies to define sections and retractions of a map `f`, and to define
what it means for a map `f` to be an equivalence.

## Definition 9.2.1

Let `f : A → B` be a function.

1. The type of **sections** of `f` is defined to be the type

```text
  sections(f) := Σ(g : B → A) f ∘ g ~ id_B.
```

In other words, a **section** of `f` is a map `g : B → A` equipped with a
homotopy `f ∘ g ~ id`.

2. The type of **retractions** of `f` is defined to be the type

```text
  retractions(f) := Σ(h : B → A) h ∘ f ~ id_A.
```

If a map `f : A → B` has a retraction, we also say that `A` is a **retract** of
`B`.

3. We say that a function `f : A → B` is an **equivalence** if it has both a
section and a retraction, i.e., if it comes equipped with an element of type

```text
  is-equiv(f) := sections(f) × retractions(f).
```

We will write `A ≃ B` for the type `Σ(f : A → B) is-equiv(f)` of all
equivalences from `A` to `B`.
For any equivalence `e : A ≃ B` we define `e⁻¹` to be the section of `e`.

## Remark 9.2.2

An equivalence, as we defined it here, can be thought of as a *bi-invertible
map*, since it comes equipped with a separate left and right inverse.
Explicitly, if `f` is an equivalence, then there are

```text
  g : B → A                       h : B → A
  G : f ∘ g ~ id_B                H : h ∘ f ~ id_A.
```

## Example 9.2.3

For any type `A`, the identity function `id : A → A` is an equivalence, since it
is its own section and its own retraction.

## Example 9.2.4

Since we have seen in Remark 9.1.1 that the negation function
`neg-bool : bool → bool` on the booleans is its own inverse, it follows that
`neg-bool` is an equivalence.

## Example 9.2.5

The successor and predecessor functions on `ℤ` are equivalences by Exercise 5.6.
Furthermore, the function

```text
  x ↦ x + k
```

is an equivalence from `ℤ` to `ℤ`, for each `k : ℤ`.
This follows from the group laws on `ℤ`, proven in Exercise 5.7.
Indeed, the inverse of `x ↦ x + k` is the map `x ↦ x + (-k)`.
Finally, it also follows from the group laws on `ℤ` that the map `x ↦ -x` is an
equivalence.

The same holds for the finite types: the maps `succ-Fin_k`, `pred-Fin_k`,
`add-Fin_k(x)` and `neg-Fin_k` are all equivalences on `Fin(k)`.

## Remark 9.2.6

More generally, if `f` **has an inverse** in the sense that we have a function
`g : B → A` equipped with homotopies `f ∘ g ~ id_B` and `g ∘ f ~ id_A`, then `f`
is an equivalence.
We write

```text
  has-inverse(f) :=
    Σ(g : B → A) (f ∘ g ~ id_B) × (g ∘ f ~ id_A).
```

However, we did *not* define equivalences to be functions that have inverses.
The reason is that we would like that being an equivalence is a *property*, not
a non-trivial structure on the map `f`.
This fact requires the function extensionality axiom, but we can already say
that if a map `f` is an equivalence, then it has up to homotopy only one section
and only one retraction.

The type `has-inverse(f)` on the other hand, turns out to be homotopically
complicated.
Later we will see that the identity function `id : S¹ → S¹` on the circle is an
example of a map for which

```text
  has-inverse(id_S¹) ≃ ℤ.
```

Even though `is-equiv(f)` and `has-inverse(f)` can be wildly different types,
there are maps back and forth between the two.
We have already observed in Remark 9.2.6 that there is a map

```text
  has-inverse(f) → is-equiv(f).
```

The following proposition gives the converse implication.

## Proposition 9.2.7

Any map `f : A → B` which is an equivalence can be given the structure of an
invertible map, i.e., there is a map

```text
  is-equiv(f) → has-inverse(f).
```

## Proof

First we construct for any equivalence `f` with right inverse `g` and left
inverse `h` a homotopy `K : g ~ h`.
For any `y : B`, we have the chain of identifications

```text
  g(y) = h(f(g(y))) = h(y).
```

In other words, the homotopy `K : g ~ h` is defined to be
`(H · g)⁻¹ ∙ (h · G)`.
Using the homotopy `K` we are able to show that `g` is also a left inverse of
`f`.
For `x : A` we have the identification

```text
  g(f(x)) = h(f(x)) = x.
```

## Corollary 9.2.8

The inverse of an equivalence is again an equivalence.

## Proof

Let `f : A → B` be an equivalence.
By Proposition 9.2.7 it follows that the section of `f` is also a retraction.
Therefore it follows that the section is itself an invertible map, with inverse
`f`.
Hence it is an equivalence.

## Example 9.2.9

Types, just as sets in classical mathematics, satisfy the usual laws of
coproducts and products, such as unit laws, commutativity, and associativity.
These laws are formulated as equivalences:

```text
  ∅ + B ≃ B                         A + ∅ ≃ A
  A + B ≃ B + A                     (A + B) + C ≃ A + (B + C)
  ∅ × B ≃ ∅                         A × ∅ ≃ ∅
  𝟙 × B ≃ B                         A × 𝟙 ≃ A
  A × B ≃ B × A                     (A × B) × C ≃ A × (B × C)
  A × (B + C) ≃ (A × B) + (A × C)
  (A + B) × C ≃ (A × C) + (B × C).
```

All of these equivalences are constructed in a similar way: the maps back and
forth as well as the required homotopies are constructed using induction, or,
more efficiently, using pattern matching.
For example, to show that cartesian products distribute from the left over
coproducts, we construct maps

```text
  α : A × (B + C) → (A × B) + (A × C)
  β : (A × B) + (A × C) → A × (B + C)
```

as follows:

```text
  α(x, inl(y)) := inl(x, y)       β(inl(x, y)) := (x, inl(y))
  α(x, inr(z)) := inr(x, z)       β(inr(x, z)) := (x, inr(z)).
```

The homotopies `G : α ∘ β ~ id` and `H : β ∘ α ~ id` are then defined by

```text
  G(inl(x, y)) := refl           H(x, inl(y)) := refl
  G(inr(x, z)) := refl           H(x, inr(z)) := refl.
```

We encourage the reader to write out the definitions of at least a few of these
equivalences.

## Example 9.2.10

The laws for cartesian products can be generalized to arbitrary `Σ`-types.
The absorption laws and unit laws, for instance, are as follows:

```text
  Σ(x : ∅) B(x) ≃ ∅              Σ(x : A) ∅ ≃ ∅
  Σ(x : 𝟙) B(x) ≃ B(⋆)           Σ(x : A) 𝟙 ≃ A.
```

Note that the right absorption law and the right unit law are exactly the same
as the right absorption and unit laws for cartesian products.
The left absorption and unit laws are, however, formulated with a type family
`B` over `∅` and over `𝟙`, and therefore they are slightly more general.

Commutativity cannot be generalized to `Σ`-types.
Associativity, on the other hand, can be expressed in two ways:

```text
  Σ(w : Σ(x : A) B(x)) C(w) ≃
    Σ(x : A) Σ(y : B(x)) C(pair(x, y))

  Σ(w : Σ(x : A) B(x)) C(pr1(w), pr2(w)) ≃
    Σ(x : A) Σ(y : B(x)) C(x, y).
```

In the first of these equivalences associativity is stated using a type family
`C` over `Σ(x : A) B(x)` while in the second it is stated using a family of
types `C(x, y)` indexed by `x : A` and `y : B(x)`.

Finally, we note that `Σ` also distributes over coproducts.
In other words, there are the following two equivalences:

```text
  Σ(x : A) (B(x) + C(x)) ≃
    (Σ(x : A) B(x)) + (Σ(x : A) C(x))

  Σ(w : A + B) C(w) ≃
    (Σ(x : A) C(inl(x))) + (Σ(y : B) C(inr(y))).
```

## Remark 9.2.11

We haven't stated any laws involving function types or dependent function types,
because it requires the function extensionality principle to prove them.
