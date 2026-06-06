# Section 16.3 Finite types

```agda
module section-16-3-finite-types where
```

The type of all finite types is the subtype of the base universe `𝒰₀`
consisting of all types `X` for which there exists an unspecified equivalence
`Fin(k) ≃ X` for some `k : ℕ`.

## Definition 16.3.1

A type `X` is said to be **finite** if it comes equipped with an element of type

```text
  is-finite(X) := ∥ Σ(k : ℕ) Fin(k) ≃ X ∥.
```

The type `𝔽` of all finite types is defined to be

```text
  𝔽 := Σ(X : 𝒰₀) is-finite(X).
```

In other words, the type `𝔽` of finite types is the image of the map
`Fin : ℕ → 𝒰₀`.
We also define the type `BS_k` of **k-element types** by

```text
  BS_k := Σ(X : 𝒰₀) ∥ Fin(k) ≃ X ∥.
```

## Remark 16.3.2

It follows directly from the definition of finiteness that any type `X`
equipped with a counting is finite.
In particular, any `Fin(k)` is finite.
Furthermore, it follows that if `X` is equivalent to a finite type `Y`, then
`X` is also finite.
Indeed, we can use the functoriality of the propositional truncation to obtain
a function

```text
  ∥ Σ(k : ℕ) Fin(k) ≃ Y ∥ → ∥ Σ(k : ℕ) Fin(k) ≃ X ∥
```

from a map

```text
  (Σ(k : ℕ) Fin(k) ≃ Y) → (Σ(k : ℕ) Fin(k) ≃ X).
```

Given an equivalence `e : X ≃ Y`, such a map is given as the map induced on
total spaces from the family of maps `f ↦ e^{-1} ∘ f`.

Similarly, it follows that any finite type has decidable equality, and that
every finite type is a set.

In the following proposition we will show that each finite type can be assigned
a unique cardinality.

## Theorem 16.3.3

For any type `X`, consider the type `is-finite'(X)` defined by

```text
  is-finite'(X) := Σ(k : ℕ) ∥ Fin(k) ≃ X ∥.
```

Then the type `is-finite'(X)` is a proposition, and there is an equivalence

```text
  is-finite(X) ↔ is-finite'(X).
```

If `X` is a finite type, then the unique number `k` such that
`∥ Fin(k) ≃ X ∥` is the **cardinality** of `X`.
We write `|X|` for the cardinality of `X`.

## Proof

We first prove the claim that the type `is-finite'(X)` is a proposition.
In other words, we need to show that any two natural numbers `k` and `k'` for
which there are respective elements of the types `∥ Fin(k) ≃ X ∥` and
`∥ Fin(k') ≃ X ∥`, can be identified.

Since the type of natural numbers is a set, the type `k = k'` is a proposition.
Therefore, we may assume that we have equivalences `Fin(k) ≃ X` and
`Fin(k') ≃ X`.
Consequently, we have an equivalence `Fin(k) ≃ Fin(k')`.
Now it follows from Theorem 16.2.2 that `k = k'`.

The second claim is that the propositions `is-finite(X)` and `is-finite'(X)`
are equivalent, which we will show by constructing functions back and forth.
Since we have shown that the type `is-finite'(X)` is a proposition, we obtain a
map `is-finite(X) → is-finite'(X)` via the universal property of the
propositional truncation, from the map

```text
  (Σ(k : ℕ) Fin(k) ≃ X) → Σ(k : ℕ) ∥ Fin(k) ≃ X ∥
```

given by `(k, e) ↦ (k, η(e))`.

To construct a map `is-finite'(X) → is-finite(X)`, it suffices to construct a
map

```text
  ∥ Fin(k') ≃ X ∥ → ∥ Σ(k : ℕ) Fin(k) ≃ X ∥
```

for each `k' : ℕ`.
Again by the universal property of the propositional truncation, we obtain this
map from the function

```text
  (Fin(k') ≃ X) → ∥ Σ(k : ℕ) Fin(k) ≃ X ∥
```

given by `e ↦ η(k', e)`.

## Corollary 16.3.4

There is an equivalence

```text
  𝔽 ≃ Σ(k : ℕ) BS_k.
```

## Proof

This equivalence can be obtained by composing the equivalences

```text
  Σ(X : 𝒰₀) is-finite(X)
    ≃ Σ(X : 𝒰₀) Σ(k : ℕ) ∥ Fin(k) ≃ X ∥
    ≃ Σ(k : ℕ) Σ(X : 𝒰₀) ∥ Fin(k) ≃ X ∥.
```

We now aim to extend Theorem 16.1.7 to obtain some closure properties of finite
types.
Before we do so, we prove the **principle of finite choice**.

## Proposition 16.3.5

Consider a type family `B` over a finite type `A`.
Then there is a **finite choice** map

```text
  (Π(x : A) ∥ B(x) ∥) → ∥ Π(x : A) B(x) ∥.
```

## Proof

Note that the type `∥ Π(x : A) B(x) ∥` is a proposition.
Therefore we may assume that the type `A` comes equipped with a counting
`e : Fin(k) ≃ A`.
By this equivalence, it suffices to show that for every type family `B` over
`Fin(k)`, there is a map

```text
  (Π(x : Fin(k)) ∥ B(x) ∥) → ∥ Π(x : Fin(k)) B(x) ∥.
```

We proceed by induction on `k`.
In the base case, `Fin(k)` is empty and therefore the type
`Π(x : Fin(k)) B(x)` is contractible.
The asserted function therefore exists.

For the inductive step, note that by the dependent universal property of
coproducts, Exercise `ex:up-coproduct`, we have the equivalences

```text
  (Π(x : Fin(k + 1)) ∥ B(x) ∥)
    ≃ (Π(x : Fin(k)) ∥ B(i(x)) ∥) × ∥ B(star) ∥
  ∥ Π(x : Fin(k)) B(x) ∥
    ≃ ∥ (Π(x : Fin(k)) B(i(x))) × B(star) ∥.
```

Recall from Exercise 14.3 that `∥ X × Y ∥ ≃ ∥ X ∥ × ∥ Y ∥` for any two types
`X` and `Y`.
This fact together with the inductive hypothesis finishes the proof.

## Theorem 16.3.6

1. For any two types `X` and `Y`, the following are equivalent:

   1. Both `X` and `Y` are finite.
   2. The coproduct `X + Y` is finite.

2. For any two types `X` and `Y`, we make two claims:

   1. If both `X` and `Y` are finite, then the cartesian product `X × Y` is
      finite.
   2. If the type `X × Y` is finite, then we have two functions

```text
  Y → is-finite(X)
  X → is-finite(Y).
```

3. Consider a type family `B` over `A`, and consider the following three
   conditions:

   1. The type `A` is finite.
   2. The type `B(x)` is finite for each `x : A`.
   3. The type `Σ(x : A) B(x)` is finite.

   If (a) holds, then (b) is equivalent to (c).
   Moreover, if (b) and (c) hold, then (a) holds if and only if `A` is a set
   and the type `Σ(x : A) ¬ B(x)` is finite.
   Furthermore, if (b) and (c) hold and `B` has a section, then (a) holds.

## Proof

To prove claim (1), first suppose that both `X` and `Y` are finite.
Since the type `is-finite(X + Y)` is a proposition, we may assume that `X` and
`Y` come equipped with countings.
It follows from Theorem 16.1.7 that `X + Y` has a counting, so it is finite.
Conversely, suppose that the type `X + Y` is finite.
Since the types `is-finite(X)` and `is-finite(Y)` are both propositions, we may
assume that the coproduct `X + Y` comes equipped with a counting.
Again it follows from Theorem 16.1.7 that the types `X` and `Y` have countings,
so they are finite.

The proof of claim (2) is similar to the proof of claim (1), hence we omit it.

It remains to prove claim (3).
First, suppose that the type `A` is finite, and that each `B(x)` is finite.
By Proposition 16.3.5 we have a map

```text
  (Π(x : A) is-finite(B(x))) → ∥ Π(x : A) count(B(x)) ∥.
```

Since our goal is to construct an element of a proposition, we may therefore
assume that each `B(x)` comes equipped with a counting.
We may also assume that `A` comes equipped with a counting.
It follows from Theorem 16.1.7 that the type `Σ(x : A) B(x)` has a counting,
so it is finite.

Next, assume that `A` is finite and that the type `Σ(x : A) B(x)` is finite,
and let `a : A`.
The type `is-finite(B(a))` is a proposition, so we may assume that the types
`A` and `Σ(x : A) B(x)` come equipped with countings.
It follows from Theorem 16.1.7 that `B(a)` has a counting, so it is finite.

The final claim has two parts.
First, assume that each `B(x)` is finite, that the type `Σ(x : A) B(x)` is
finite, and that the type family `B` has a section `f : Π(x : A) B(x)`.
It follows that the map

```text
  A → Σ(x : A) B(x)
```

given by `x ↦ (x, f(x))` is a decidable embedding, because the fiber at
`(x, y)` of this map is equivalent to the identity type `f(x) = y` in `B(x)`,
which is a decidable proposition.
It follows from the fact that (a) and (b) together imply (c) that `A` is finite.

For the remaining part of the final claim, assume that `A` is a set.
Note that the assumption that each `B(x)` is finite implies that each `B(x)` is
either inhabited or empty.
It follows that we have an equivalence

```text
  A ≃ (Σ(x : A) ∥ B(x) ∥) + (Σ(x : A) ¬ B(x)).
```

We assume that the type `Σ(x : A) ¬ B(x)` is finite.
In order to show that `A` is finite, it therefore suffices to show that the type
`Σ(x : A) ∥ B(x) ∥` is finite.
Without loss of generality, we assume that each `B(x)` is inhabited.
To finish the proof, it suffices to show that there is an element of type

```text
  ∥ Π(x : A) B(x) ∥
```

using the assumption that `Π(x : A) ∥ B(x) ∥`.
To construct such an element, we may assume a counting
`e : Fin(k) ≃ Σ(x : A) B(x)`.
We claim that there is a function

```text
  ∥ B(a) ∥ → B(a),
```

i.e., that the type `B(a)` satisfies the principle of global choice of
Remark 14.4.2 for each `a : A`.
Recall from Example 14.4.1 that the decidable subtypes of `Fin(k)` satisfy
global choice.
Therefore it also follows that the decidable subtypes of `Σ(x : A) B(x)`
satisfy global choice.
Thus, it suffices to show that `B(x)` is a decidable subtype of
`Σ(x : A) B(x)`.

The assumption that `A` is a set implies by Exercise 12.13 that the fiber
inclusion `i_a : B(a) → Σ(x : A) B(x)` is an embedding for each `a : A`.
Furthermore, we note that we have the following equivalence computing the
fibers of `i_a` at `(x, y)`:

```text
  (Σ(z : B(a)) (a, z) = (x, y)) ≃ (a = x).
```

The type on the left hand side is decidable, so it follows that the type `A`
has decidable equality.
We conclude that each `B(a)` is a decidable subtype of `Σ(x : A) B(x)`.
