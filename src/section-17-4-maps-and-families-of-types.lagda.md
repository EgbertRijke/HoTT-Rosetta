# Section 17.4 Maps and families of types

```agda
module section-17-4-maps-and-families-of-types where
```

Using the univalence axiom, we can establish a fundamental relation between
maps into a type `A`, and families of types indexed by `A`.
A special case of this relation asserts that the type of all pairs `(X, e)`
consisting of a type `X` and an embedding `e : X ↪ A` is equivalent to the type
of all subtypes of `A`, i.e., the type of all families `P` of propositions
indexed by `A`.

## Theorem 17.4.1

For any type `A` and any univalent universe `𝒰` containing `A`, the map

```text
  (Σ(X : 𝒰) X → A) → (A → 𝒰)
```

given by `(X, f) ↦ fib_f` is an equivalence.

## Proof

The map in the converse direction is given by

```text
  B ↦ (Σ(x : A) B(x), pr1).
```

To verify that this map is a section of the asserted map, we have to prove that

```text
  fib(pr1) = B
```

for any `B : A → 𝒰`.
By function extensionality and the univalence axiom, this is equivalent to

```text
  Π(x : A) fib(pr1, x) ≃ B(x).
```

Such a family of equivalences was constructed in Exercise `ex:proj_fiber`.

It remains to verify that

```text
  (X, f) = (Σ(x : A) fib(f, x), pr1).
```

Before we do this, we claim that the identity type

```text
  (X, f) = (Y, g)
```

in the type `Σ(X : 𝒰) X → A` is equivalent to the type of pairs `(e, H)`
consisting of an equivalence `e : X ≃ Y` equipped with a homotopy
`H : f ~ g ∘ e`.
This fact follows from Theorem `thm:id_fundamental`, because the type

```text
  Σ(Y : 𝒰) Σ(g : Y → A) Σ(e : X ≃ Y) f ~ g ∘ e
```

is contractible by the structure identity principle, Theorem
`thm:structure-identity-principle`.

To finish the proof, it therefore suffices to construct an equivalence

```text
  e : X ≃ Σ(a : A) fib(f, a)
```

equipped with a homotopy `f ~ pr1 ∘ e`.
Such an equivalence `e` equipped with a homotopy was constructed in
Exercise `ex:fib_replacement`.

The following corollary is so important that we call it again a theorem.

## Theorem 17.4.2

Consider a type `A` and a univalent universe `𝒰` containing `A`.
Furthermore, let `P` be a family of types indexed by `𝒰`, and write

```text
  𝒰_P := Σ(X : 𝒰) P(X).
```

Then the map

```text
  (Σ(X : 𝒰) Σ(f : X → A) Π(a : A) P(fib(f, a))) → (A → 𝒰_P)
```

given by `(X, f, p) ↦ λ a → (fib(f, a), p(a))` is an equivalence.

## Proof

The asserted map is homotopic to the composition of the equivalences

```text
  Σ(X : 𝒰) Σ(f : X → A) Π(a : A) P(fib(f, a))
    ≃ Σ((X, f) : Σ(X : 𝒰) X → A) Π(a : A) P(fib(f, a))
    ≃ Σ(B : A → 𝒰) Π(a : A) P(B(a))
    ≃ A → Σ(X : 𝒰) P(X).
```

Theorem 17.4.2 applies to any subuniverse.
Examples include the subuniverse of `k`-types, for any truncation level `k`,
the subuniverse of decidable propositions, the subuniverse of finite types, the
subuniverse of inhabited types, and so on.
It also applies to type families over `𝒰` that are not families of
propositions.
The families `P := is-decidable` and `P := count` are examples.

## Corollary 17.4.3

Consider a type `A` and a univalent universe `𝒰` containing `A`.
Then the map

```text
  (Σ(X : 𝒰) X ↪ A) → (A → Prop_𝒰)
```

given by `(X, f) ↦ fib_f` is an equivalence.

In other words, a subtype of a type `A` is equivalently described as a type `X`
equipped with an embedding `e : X ↪ A`.
This brings us to an important point about equality of subtypes.

## Remark 17.4.4

By function extensionality and propositional extensionality, it follows that
two subtypes `P Q : A → Prop_𝒰` are the same if and only if

```text
  P(a) ↔ Q(a)
```

holds for all `a : A`.
In other words, two subtypes of `A` are the same if and only if they contain
the same elements of `A`.

On the other hand, by Corollary 17.4.3 we can also consider two types `X` and
`Y` equipped with embeddings `f : X ↪ A` and `g : Y ↪ A` as subtypes of `A`.
Using the structure identity principle, Theorem `thm:structure-identity-principle`,
we see that the identity type `(X, f) = (Y, g)` in the type
`Σ(X : 𝒰) X ↪ A` is equivalent to the type

```text
  Σ(e : X ≃ Y) f ~ g ∘ e.
```

In other words, two subtypes `(X, f)` and `(Y, g)` of `A` are equal if and only
if there is an equivalence `X ≃ Y` that is compatible with the embeddings
`f : X ↪ A` and `g : Y ↪ A`.
Indeed, this condition is equivalent to the previous condition that two
subtypes are the same if and only if they have the same elements.

We see that the combination of the structure identity principle and the
univalence axiom automatically characterizes equality of subtypes in the most
natural way, and we will see similar natural characterizations of identity
types throughout the remainder of this book.
