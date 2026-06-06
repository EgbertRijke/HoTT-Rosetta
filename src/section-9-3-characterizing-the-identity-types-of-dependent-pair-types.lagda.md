# Section 9.3 Characterizing the identity types of dependent pair types

```agda
module section-9-3-characterizing-the-identity-types-of-dependent-pair-types where
```

In this section we characterize the identity type of a `Σ`-type as a `Σ`-type of
identity types.
Characterizing identity types is a task that a homotopy type theorist routinely
performs, so we will follow the general outline of how such a characterization
goes:

1. First we define a binary relation `R : A → A → 𝕌` on the type `A` that we are
interested in.
This binary relation is intended to be equivalent to its identity type.
2. Then we will show that this binary relation is reflexive, by constructing a
dependent function of type

```text
  Π(x : A) R(x, x).
```

3. Using the reflexivity we will show that there is a canonical map

```text
  (x = y) → R(x, y)
```

for every `x, y : A`.
This map is just constructed by path induction, using the reflexivity of `R`.
4. Finally, it has to be shown that the map

```text
  (x = y) → R(x, y)
```

is an equivalence for each `x, y : A`.

The last step is usually the most difficult, and we will refine our methods for
this step in the chapter on the fundamental theorem of identity types.

In this section we consider a type family `B` over `A`.
Given two pairs

```text
  (x, y), (x', y') : Σ(x : A) B(x),
```

if we have a path `α : x = x'` then we can compare `y : B(x)` to `y' : B(x')`
by first transporting `y` along `α`, i.e., we consider the identity type

```text
  tr_B(α, y) = y'.
```

Thus it makes sense to think of `(x, y)` to be identical to `(x', y')` if there
is an identification `α : x = x'` and an identification
`β : tr_B(α, y) = y'`.
In the following definition we turn this idea into a binary relation on the
`Σ`-type.

## Definition 9.3.1

We will define a relation

```text
  Eq-Σ : (Σ(x : A) B(x)) → (Σ(x : A) B(x)) → 𝕌
```

by defining

```text
  Eq-Σ(s, t) :=
    Σ(α : pr1(s) = pr1(t)) tr_B(α, pr2(s)) = pr2(t).
```

## Lemma 9.3.2

The relation `Eq-Σ` is reflexive, i.e., we can construct

```text
  reflexive-Eq-Σ : Π(s : Σ(x : A) B(x)) Eq-Σ(s, s).
```

## Construction

The element `reflexive-Eq-Σ` is constructed by `Σ`-induction on
`s : Σ(x : A) B(x)`.
Thus, it suffices to construct a dependent function of type

```text
  Π(x : A) Π(y : B(x)) Σ(α : x = x) tr_B(α, y) = y.
```

Here we take `λ x. λ y. (refl(x), refl(y))`.

## Definition 9.3.3

Consider a type family `B` over `A`.
Then for any `s, t : Σ(x : A) B(x)` we define a map

```text
  pair-eq : (s = t) → Eq-Σ(s, t)
```

by path induction, taking
`pair-eq(refl(s)) := reflexive-Eq-Σ(s)`.

## Theorem 9.3.4

Let `B` be a type family over `A`.
Then the map

```text
  pair-eq : (s = t) → Eq-Σ(s, t)
```

is an equivalence for every `s, t : Σ(x : A) B(x)`.

## Proof

The maps in the converse direction

```text
  eq-pair : Eq-Σ(s, t) → (s = t)
```

are defined by repeated `Σ`-induction.
By `Σ`-induction on `s` and `t` we see that it suffices to define a map

```text
  eq-pair :
    (Σ(p : x = x') tr_B(p, y) = y') → ((x, y) = (x', y')).
```

A map of this type is again defined by `Σ`-induction.
Thus it suffices to define a dependent function of type

```text
  Π(p : x = x') (tr_B(p, y) = y') → ((x, y) = (x', y')).
```

Such a dependent function is defined by double path induction by sending
`(refl(x), refl(y))` to `refl(x, y)`.
This completes the definition of the function `eq-pair`.

Next, we must show that `eq-pair` is a section of `pair-eq`.
In other words, we must construct an identification

```text
  pair-eq(eq-pair(α, β)) = (α, β)
```

for each `(α, β) : Σ(α : x = x') tr_B(α, y) = y'`.
We proceed by path induction on `α`, followed by path induction on `β`.
Then our goal becomes to construct an identification of type

```text
  pair-eq(eq-pair(refl(x), refl(y))) = (refl(x), refl(y)).
```

By the definition of `eq-pair` we have
`eq-pair(refl(x), refl(y)) ≐ refl(x, y)`, and by the definition of `pair-eq` we
have `pair-eq(refl(x, y)) ≐ (refl(x), refl(y))`.
Thus we may take `refl(refl(x), refl(y))` to complete the construction of the
homotopy `pair-eq ∘ eq-pair ~ id`.

To complete the proof, we must show that `eq-pair` is a retraction of
`pair-eq`.
In other words, we must construct an identification

```text
  eq-pair(pair-eq(p)) = p
```

for each `p : s = t`.
We proceed by path induction on `p : s = t`, so it suffices to construct an
identification

```text
  eq-pair(refl(pr1(s)), refl(pr2(s))) = refl(s).
```

Now we proceed by `Σ`-induction on `s : Σ(x : A) B(x)`, so it suffices to
construct an identification

```text
  eq-pair(refl(x), refl(y)) = refl(x, y).
```

Since `eq-pair(refl(x), refl(y))` computes to `refl(x, y)`, we may simply take
`refl(refl(x, y))`.
