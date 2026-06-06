# Section 14.4 Mapping propositional truncations into sets

```agda
module section-14-4-mapping-propositional-truncations-into-sets where
```

The universal property of the propositional truncation only applies when we
want to define a map into a proposition.
However, in some situations we might want to map the propositional truncation
into a type that is not a proposition.
Here we will see what we might do in such a case.

One strategy, if we want to define a map `∥ A ∥ → X`, is to find a type family
`P` over `X` such that the type `Σ(x : X) P(x)` is a proposition.
In that case, we may use the universal property of the propositional truncation
to obtain a map `∥ A ∥ → Σ(x : X) P(x)` from a map
`A → Σ(x : X) P(x)`, and then we simply compose with the projection map.

## Example 14.4.1

Consider a **decidable subtype** `P` of the natural numbers, i.e., a subtype
`P : ℕ → Prop_𝒰` such that each `P(n)` is decidable.
We claim that there is a function

```text
  ∥ Σ(x : ℕ) P(x) ∥ → Σ(x : ℕ) P(x).
```

Of course, we cannot directly use the universal property of the propositional
truncation here.
However, there is at most one *minimal* natural number `x` in `P`.
In other words, we claim that the type

```text
  Σ(x : ℕ) P(x) × is-lower-bound_P(x)       (*)
```

is a proposition.
To see this, note that the type `is-lower-bound_P(x)` is a proposition.
By the assumption that each `P(x)` is a proposition, it now follows that any
two natural numbers `x y : ℕ` that are in `P` and that are both lower bounds of
`P` are equal as elements in the type of `(*)` if and only if they are equal as
natural numbers.
Furthermore, since both `x` and `y` are lower bounds of `P`, it follows that
`x ≤ y` and `y ≤ x`, so indeed `x = y` holds.

By the observation that the type in `(*)` is a proposition, we may define a map

```text
  ∥ Σ(x : ℕ) P(x) ∥ → Σ(x : ℕ) P(x) × is-lower-bound_P(x)
```

by the universal property of the propositional truncation.
A map

```text
  Σ(x : ℕ) P(x) → Σ(x : ℕ) P(x) × is-lower-bound_P(x)
```

was constructed in Theorem `thm:well-ordering-principle-N` using the
decidability of `P`.

As a corollary of this observation, we observe that there is also a map

```text
  ∥ Σ(x : Fin(k)) P(x) ∥ → Σ(x : Fin(k)) P(x)
```

for any decidable subtype `P` over `Fin(k)`.

## Remark 14.4.2

The function of type

```text
  ∥ Σ(x : ℕ) P(x) ∥ → Σ(x : ℕ) P(x)
```

we constructed in Example 14.4.1 for decidable subtypes of `ℕ` is a rare case
in which it is possible to obtain a function

```text
  ∥ A ∥ → A.
```

We say that the type `A` satisfies the **principle of global choice** if there
is such a function `∥ A ∥ → A`.
Using the univalence axiom, we will see in Corollary `cor:no-global-choice`
that not every type satisfies the principle of global choice.

More generally, we may wish to define a map `∥ A ∥ → B` where the type `B` is a
set.
In this situation it is helpful to think of the propositional truncation of `A`
as the quotient of the type `A` by the equivalence relation that relates every
two elements of `A` with each other.
Propositional truncations can therefore also be characterized by the universal
property of this quotient, which can be used to extend maps `f : A → B` to maps
`∥ A ∥ → B` when the type `B` is a set.
The idea is that a map `f : A → B` into a set `B` extends to a map
`∥ A ∥ → B` if it satisfies `f(x) = f(y)` for all `x y : A`.

## Definition 14.4.3

A map `f : A → B` is said to be **weakly constant** if it comes equipped with
an element of type

```text
  is-weakly-constant(f) := Π(x y : A) f(x) = f(y).
```

## Remark 14.4.4

A constant map `A → B` is a map of the form `const_b`.
A map `f : A → B` is therefore constant if comes equipped with an element
`b : B` and a homotopy `f ~ const_b`.
This is a stronger notion than the notion of weakly constant maps, which
doesn't require there to be an element in `B`.

One of the differences between constant maps and weakly constant maps manifests
itself as follows: A type `A` is contractible if and only if the identity map on
`A` is constant, while a type `A` is a proposition if and only if the identity
map on `A` is weakly constant.

## Lemma 14.4.5

Consider a commuting triangle

```text
  A ----f----> B
  |
  η
  v
  ∥ A ∥ --g--> B
```

where `B` is an arbitrary type.
Then the map `f` is weakly constant.

## Proof

Since `f` is assumed to be homotopic to `g ∘ η`, it suffices to show that
`g ∘ η` is weakly constant.
For any `x y : A`, we have the identification `α(x, y) : η(x) = η(y)` in
`∥ A ∥`.
Using the action on paths of `g`, we obtain the identification

```text
  ap_g(α(x, y)) : g(η(x)) = g(η(y))
```

in `B`.

We now show, in a theorem due to Kraus, that any weakly constant map
`f : A → B` into a set `B` extends uniquely to a map `∥ A ∥ → B`.
We therefore conclude that, in order to define a map `∥ A ∥ → B` into a set
`B`, it suffices to define a map `f : A → B` and show that it is weakly
constant.

## Theorem 14.4.6

Let `A` be a type and let `B` be a set.
Then the map

```text
  (∥ A ∥ → B) → Σ(f : A → B) Π(x y : A) f(x) = f(y)
```

given by `g ↦ (g ∘ η, λ x → λ y → ap_g(α(x, y)))` is an equivalence.

## Proof

Consider a map `f : A → B` equipped with
`H : Π(x y : A) f(x) = f(y)`.
We first show that `f` extends in at most one way to a map `∥ A ∥ → B`.
Let `g h : ∥ A ∥ → B` be two maps equipped with homotopies
`f ~ g ∘ η` and `f ~ h ∘ η`.
In order to construct a homotopy `g ~ h`, note that each identity type
`g(x) = h(x)` is a proposition by the assumption that `B` is a set.
We can therefore construct a homotopy `g ~ h` by the induction principle of
propositional truncations.
By the induction principle, it suffices to construct a homotopy
`g ∘ η ~ h ∘ η`, which we obtain from the homotopies `f ~ g ∘ η` and
`f ~ h ∘ η`.

Since we have already proven uniqueness, it remains to construct an extension
of the map `f`.
We first claim that the type

```text
  Σ(b : B) ∥ Σ(x : A) f(x) = b ∥
```

is a proposition.
To see this, consider two elements `b` and `b'` in this subtype of `B`.
It suffices to show that `b = b'`.
Since `B` is assumed to be a set, the identity type `b = b'` is a proposition.
Therefore we may assume an element `x : A` equipped with `p : f(x) = b` and an
element `x' : A` equipped with `p' : f(x') = b'`.
Using the assumption that `f` is weakly constant, we obtain the identification

```text
  b = f(x) = f(x') = b',
```

where the first path is `p^{-1}`, the second is `H(x, x')`, and the third is
`p'`.

Now we observe that the map `f : A → B` factors uniquely as follows

```text
  A ----g----> Σ(b : B) ∥ Σ(x : A) f(x) = b ∥
   \              |
    \ f           pr1
     \            |
      v           v
        B.
```

Indeed, the map `g` is given by `x ↦ (f(x), η(x, refl))`.
Since the codomain of `g` is a proposition, we obtain via the universal
property of the propositional truncation of `A` a unique map

```text
  h : ∥ A ∥ → Σ(b : B) ∥ Σ(x : A) f(x) = b ∥
```

equipped with a homotopy `g ~ h ∘ η`.
Now we obtain the map `pr1 ∘ h : ∥ A ∥ → B` equipped with the concatenated
homotopy

```text
  (pr1 ∘ h) ∘ η ≐ pr1 ∘ (h ∘ η) ~ pr1 ∘ g ~ f.
```
