# Section 13.3 Universal properties

```agda
module section-13-3-universal-properties where
```

The function extensionality principle allows us to prove *universal
properties*.
Universal properties are characterizations of all maps out of or into a given
type, so they are very important.
Among other applications, universal properties characterize a type up to
equivalence.
We prove here the universal properties of dependent pair types and of identity
types.
In the exercises, you are asked to prove the universal properties of `unit`,
`empty`, and coproducts.

## The universal property of Sigma-types

The **universal property of `Σ`-types** characterizes maps *out of* a dependent
pair type `Σ(x : A) B(x)`.
It asserts that the map

```text
  ev-pair :
    ((Σ(x : A) B(x)) → X) →
    (Π(x : A) (B(x) → X)),
```

given by `f ↦ λ x → λ y → f(x, y)`, is an equivalence for any type `X`.
In fact, we will prove a slight generalization of this universal property.
We will prove the **dependent universal property** of `Σ`-types, which
characterizes *dependent* functions out of `Σ(x : A) B(x)`.

## Theorem 13.3.1

Let `B` be a type family over `A`, and let `C` be a type family over
`Σ(x : A) B(x)`.
Then the map

```text
  ev-pair :
    (Π(z : Σ(x : A) B(x)) C(z)) →
    (Π(x : A) Π(y : B(x)) C(x, y)),
```

given by `f ↦ λ x → λ y → f(x, y)`, is an equivalence.

## Proof

The map in the converse direction is obtained by the induction principle of
`Σ`-types.
It is simply the map

```text
  ind-Σ :
    (Π(x : A) Π(y : B(x)) C(x, y)) →
    (Π(z : Σ(x : A) B(x)) C(z)).
```

By the computation rule for `Σ`-types we have the homotopy

```text
  refl-htpy : ev-pair ∘ ind-Σ ~ id.
```

This shows that `ind-Σ` is a section of `ev-pair`.

To show that `ind-Σ ∘ ev-pair ~ id` we will apply the function extensionality
principle.
Therefore it suffices to show that `ind-Σ(λ x → λ y → f(x, y)) = f`.
We apply function extensionality again, so it suffices to show that

```text
  Π(t : Σ(x : A) B(x)) ind-Σ(λ x → λ y → f(x, y))(t) = f(t).
```

We obtain this homotopy by another application of `Σ`-induction.

## Corollary 13.3.2

Let `A`, `B`, and `X` be types.
Then the map

```text
  ev-pair : (A × B → X) → (A → (B → X))
```

given by `f ↦ λ a → λ b → f(a, b)` is an equivalence.

## The universal property of identity types

The universal property of identity types is the fact that families of maps out
of the identity type are uniquely determined by their action on the reflexivity
identification.
More precisely, the map

```text
  ev-refl : (Π(x : A) (a = x) → B(x)) → B(a)
```

given by `λ f → f(a, refl(a))` is an equivalence, for every type family `B`
over `A`.
Since this result is similar to the Yoneda lemma of category theory, the
universal property of identity types is sometimes referred to as the *type
theoretic Yoneda lemma*.
We will prove the *dependent* universal property of identity types, a slight
generalization of the universal property.

## Theorem 13.3.3

Consider a type `A` equipped with `a : A`, and consider a family of types
`B(x, p)` indexed by `x : A` and `p : a = x`.
Then the map

```text
  ev-refl :
    (Π(x : A) Π(p : a = x) B(x, p)) →
    B(a, refl(a)),
```

given by `λ f → f(a, refl(a))`, is an equivalence.

## Proof

The inverse is the function

```text
  path-ind_a : B(a, refl(a)) → Π(x : A) Π(p : a = x) B(x, p).
```

It is immediate from the computation rule of the path induction principle that
`ev-refl ∘ path-ind_a ~ id`.

To see that `path-ind_a ∘ ev-refl ~ id`, let
`f : Π(x : A) (a = x) → B(x, p)`.
To show that `path-ind_a(f(a, refl(a))) = f` we apply function extensionality
twice.
Therefore it suffices to show that

```text
  Π(x : A) Π(p : a = x)
    path-ind_a(f(a, refl(a)), x, p) = f(x, p).
```

This follows by path induction on `p`, since
`path-ind_a(f(a, refl(a)), a, refl(a)) ≐ f(a, refl(a))` by the computation rule
of path induction.
