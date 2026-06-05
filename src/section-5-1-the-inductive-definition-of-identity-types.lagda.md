# Section 5.1 The inductive definition of identity types

```agda
module section-5-1-the-inductive-definition-of-identity-types where
```

## Definition 5.1.1

Consider a type `A` and let `a : A`.
Then we define the **identity type** of `A` at `a` as an inductive family of
types `a = x` indexed by `x : A`, of which the constructor is

```text
  refl : a = a.
```

The induction principle of the identity type postulates that for any family of
types `P(x, p)` indexed by `x : A` and `p : a = x`, there is a function

```text
  path-ind_a : P(a, refl) → Π(x : A) Π(p : a = x) P(x, p)
```

which satisfies `path-ind_a(u, a, refl) ≐ u`, given `u : P(a, refl)`.

An element of type `a = x` is also called an **identification** of `a` with `x`,
and sometimes it is called a **path** from `a` to `x`.
The induction principle for identity types is sometimes called **identification
elimination** or **path induction**.
We also write `Id_A` for the identity type on `A`, and often we write `a = x`
for the type of identifications of `a` with `x`, omitting reference to the
ambient type `A`.

## Remark 5.1.2

We see that the identity type is not just an inductive type, like the
inductive types `ℕ`, `∅`, and `𝟙` for example, but it is an inductive
*family* of types.
Even though we have a type `a = x` for any `x : A`, the constructor only
provides an element ` refl : a = a`, identifying `a` with itself.
The induction principle then asserts that in order to prove something about all
identifications of `a` with some `x : A`, it suffices to prove this assertion
about `refl` only.
We will see in the next sections that this induction principle is strong enough
to derive many familiar facts about equality, namely that it is a symmetric and
transitive relation, and that all functions preserve equality.

## Remark 5.1.3

Since the identity types require getting used to, we provide the formal rules
for identity types.
The identity type is formed by the formation rule:

```text
         Γ ⊢ a : A
  -----------------------
   Γ, x : A ⊢ a = x type
```

The constructor of the identity type is then given by the introduction rule:

```text
      Γ ⊢ a : A
  ------------------
   Γ ⊢ refl : a = a
```

The induction principle is now given by the elimination rule:

```text
      Γ ⊢ a : A           Γ, x : A, p : a = x ⊢ P(x, p) type
  --------------------------------------------------------------
    Γ ⊢ path-ind_a : P(a, refl) → Π(x : A) Π(p : a = x) P(x, p)
```

And finally the computation rule is:

```text
     Γ ⊢ a : A           Γ, x : A, p : a = x ⊢ P(x, p) type
  -------------------------------------------------------------
   Γ, u : P(a, refl) ⊢ path-ind_a(u, a, refl) ≐ u : P(a, refl)
```

## Remark 5.1.4

One might wonder whether it is also possible to form the identity type at a
*variable* of type `A`, rather than at an element.
This is certainly possible:  since we can form the identity type in *any*
context, we can form the identity type at a variable `x : A` as follows:

```text
         Γ, x : A ⊢ x : A
  ------------------------------
   Γ, x : A, y : A ⊢ x = y type
```

In this way we obtain the "binary" identity type.
Its constructor is then also indexed by `x : A`.
We have the following introduction rule

```text
      Γ, x : A ⊢ x : A
  -------------------------
   Γ, x : A ⊢ refl : x = x
```

and similarly we have elimination and computation rules.
