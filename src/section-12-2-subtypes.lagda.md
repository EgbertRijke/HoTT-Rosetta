# Section 12.2 Subtypes

```agda
module section-12-2-subtypes where
```

In set theory, a set `y` is said to be a subset of a set `x` if any element of
`y` is an element of `x`, i.e., if the condition

```text
  ∀ z, (z ∈ y) → (z ∈ x)
```

holds.
We have already noted that type theory is different from set theory in that
terms in type theory come equipped with a *unique* type.
Moreover, in set theory the proposition `x ∈ y` is well-formed for any two sets
`x` and `y`, whereas in type theory we can only judge that `a : A` by applying
the rules of inference of type theory in such a manner that we arrive at the
conclusion that `a : A`.
Because of these differences we must find a different way to talk about
subtypes.

Note that in set theory there is a correspondence between the subsets of a set
`x`, and the *predicates* on `x`.
A predicate on `x` is just a proposition `P(z)` that varies over the elements
`z ∈ x`.
Indeed, if `y` is a subset of `x`, then the corresponding predicate is the
proposition `z ∈ y`.
Conversely, if `P` is a predicate on `x`, then we obtain the subset

```text
  { z ∈ x | P(z) }
```

of `x`.
This observation suggests that in type theory we should define a subtype of a
type `A` to be a family of propositions over `A`.

## Definition 12.2.1

A type family `B` over `A` is said to be a **subtype** of `A` if for each
`x : A` the type `B(x)` is a proposition.
When `B` is a subtype of `A`, we also say that `B(x)` is a **property** of
`x : A`.

One reason why subtypes are important and useful is that for any

```text
  (x, p), (y, q) : Σ(x : A) P(x)
```

in a subtype of `A`, we have `(x, p) = (y, q)` if and only if `x = y`.
In other words, two terms of a subtype of `A` are equal if and only if they are
equal as terms of `A`.
This fact is properly expressed using embeddings: we claim that the projection
map

```text
  pr1 : (Σ(x : A) P(x)) → A
```

is an embedding, for any subtype `P` of `A`.
This claim can be strengthened slightly.
We will prove the following two closely related facts:

1. A map `f : A → B` is an embedding if and only if its fibers are propositions.
2. A family of types `B` over `A` is a subtype of `A` if and only if the
   projection map

```text
  (Σ(x : A) B(x)) → A
```

is an embedding.

The first fact is analogous to the fact that a map is an equivalence if and
only if its fibers are contractible, which we saw in
Theorems `thm:contr_equiv` and `thm:equiv_contr`.
To prove the above claims, we will need that propositions are closed under
equivalences.

## Lemma 12.2.2

Let `A` and `B` be types, and let `e : A ≃ B`.
Then we have

```text
  is-prop(A) ↔ is-prop(B).
```

## Proof

We will show that `is-prop(B)` implies `is-prop(A)`.
This suffices, because the converse follows from the fact that
`e⁻¹ : B → A` is also an equivalence.

Since `e` is assumed to be an equivalence, it follows by Corollary
`cor:emb_equiv` that

```text
  ap_e : (x = y) → (e(x) = e(y))
```

is an equivalence for any `x y : A`.
If `B` is a proposition, then in particular the type `e(x) = e(y)` is
contractible for any `x y : A`, so the claim follows from
Theorem `thm:contr_equiv`.

## Theorem 12.2.3

Consider a map `f : A → B`.
The following are equivalent:

1. The map `f` is an embedding.
2. The fiber `fib(f, b)` is a proposition for each `b : B`.

## Proof

By the fundamental theorem of identity types, it follows that `f` is an
embedding if and only if

```text
  Σ(x : A) f(x) = f(y)
```

is contractible for each `y : A`.
In other words, `f` is an embedding if and only if `fib(f, f(y))` is
contractible for each `y : A`.
Note that we obtain equivalences

```text
  fib(f, f(y)) ≃ fib(f, b)
```

for any `b : B` and `p : f(y) = b`, by transporting along `p`.
Therefore it follows by Lemma 12.2.2 that `fib(f, f(y))` is contractible for
each `y : A` if and only if `fib(f, b)` is contractible for each `y : A`, and
each `b : B` such that `p : f(y) = b`.
The latter condition holds if and only if we have

```text
  fib(f, b) → is-contr(fib(f, b))
```

for any `b : B`, which is by Proposition 12.1.3 equivalent to the condition
that each `fib(f, b)` is a proposition.

## Corollary 12.2.4

Consider a family `B` of types over `A`.
The following are equivalent:

1. The map `pr1 : (Σ(x : A) B(x)) → A` is an embedding.
2. The type `B(x)` is a proposition for each `x : A`.

## Proof

This corollary follows at once from Exercise `ex:proj_fiber`, where we showed
that

```text
  fib(pr1, x) ≃ B(x).
```
