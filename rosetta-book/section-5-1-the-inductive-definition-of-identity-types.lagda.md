# Section 5.1 The inductive definition of identity types

```agda
module section-5-1-the-inductive-definition-of-identity-types where

open import universe-levels
```

<!-- rosetta-item: section-5.1 -->

## Definition 5.1.1

<!-- rosetta-item: definition-5.1.1 -->

Consider a type `A` and let `a:A`.
Then we define the **identity type** of `A` at `a` as an inductive family of types `a =_A x` indexed by `x:A`, of which the constructor is
```text
refl:a=_Aa.
```
The induction principle of the identity type postulates that for any family of types `P(x,p)` indexed by `x:A` and `p:a=_A x`, there is a function
```text
path-ind_a:P(a,refl) → Π(x:A) Π(p:a=_A x) P(x,p)
```
that satisfies `path-ind_a(u,a,refl)≐ u`, give `u:P(a,refl)`.

An element of type `a=_A x` is also called an **identification** of `a` with `x`, and sometimes it is called a **path** from `a` to `x`.
The induction principle for identity types is sometimes called **identification elimination** or **path induction**.
We also write `Id_A` for the identity type on `A`, and often we write `a=x` for the type of identifications of `a` with `x`, omitting reference to the ambient type `A`.

<!-- rosetta-agda-block: section-5-1-the-inductive-definition-of-identity-types-block-20 -->

```agda
module _
  {l : Level} {A : Type l}
  where

  data Id (x : A) : A → Type l where
    instance refl : Id x x

  infix 6 _＝_
  _＝_ : A → A → Type l
  (a ＝ b) = Id a b

{-# BUILTIN EQUALITY Id #-}
```

<!-- rosetta-agda-block: section-5-1-the-inductive-definition-of-identity-types-block-44 -->

```agda
ind-Id :
  {l1 l2 : Level} {A : Type l1}
  (x : A) (B : (y : A) (p : x ＝ y) → Type l2) →
  B x refl → (y : A) (p : x ＝ y) → B y p
ind-Id x B b y refl = b
```
<!-- rosetta-item-end: definition-5.1.1 -->

## Remark 5.1.2

<!-- rosetta-item: remark-5.1.2 -->

We see that the identity type is not just an inductive type, like the inductive types `ℕ`, `empty`, and `unit` for example, but it is an inductive *family* of types.
Even though we have a type `a=_A x` for any `x:A`, the constructor only provides an element `refl:a=_A a`, identifying `a` with itself.
The induction principle then asserts that in order to prove something about all identifications of `a` with some `x:A`, it suffices to prove this assertion about `refl` only.
We will see in the next sections that this induction principle is strong enough to derive many familiar facts about equality, namely that it is a symmetric and transitive relation, and that all functions preserve equality.

<!-- rosetta-item-end: remark-5.1.2 -->

## Remark 5.1.3

<!-- rosetta-item: remark-5.1.3 -->

Since the identity types require getting used to, we provide the formal rules for identity types.
The identity type is formed by the formation rule:

<!-- rosetta-proof-tree: 0aab00f2bff7; review: pending -->

*Proof tree (automatic faithful draft).*

```text
       Γ⊢ a:A
───────────────────
Γ,x:A⊢ a=_A x \type
```

The constructor of the identity type is then given by the introduction rule:

<!-- rosetta-proof-tree: 32d00eeef0e3; review: pending -->

*Proof tree (automatic faithful draft).*

```text
    Γ⊢ a:A
──────────────
Γ⊢ refl:a=_A a
```

The induction principle is now given by the elimination rule:

<!-- rosetta-proof-tree: 3b38b35fccc7; review: pending -->

*Proof tree (automatic faithful draft).*

```text
      Γ⊢ a:A   Γ,x:A,p:a=_A x⊢ P(x,p) \type
─────────────────────────────────────────────────
Γ⊢ path-ind_a:P(a,refl)→Π(x:A) Π(p:a=_A x) P(x,p)
```

And finally the computation rule is:

<!-- rosetta-proof-tree: 29bf1f402f7f; review: pending -->

*Proof tree (automatic faithful draft).*

```text
       Γ⊢ a:A   Γ,x:A,p:a=_A x⊢ P(x,p) \type
───────────────────────────────────────────────────
Γ,u:P(a,refl) ⊢ path-ind_a(u,a,refl)≐ u : P(a,refl)
```

<!-- rosetta-item-end: remark-5.1.3 -->

## Remark 5.1.4

<!-- rosetta-item: remark-5.1.4 -->

One might wonder whether it is also possible to form the identity type at a *variable* of type `A`, rather than at an element.
This is certainly possible: since we can form the identity type in *any* context, we can form the identity type at a variable `x:A` as follows:

<!-- rosetta-proof-tree: 159e5f9d918a; review: pending -->

*Proof tree (automatic faithful draft).*

```text
       Γ,x:A⊢ x:A
───────────────────────
Γ,x:A,y:A⊢ x=_A y \type
```

In this way we obtain the ‘binary’ identity type.
Its constructor is then also indexed by `x:A`.
We have the following introduction rule

<!-- rosetta-proof-tree: 55d5fde68874; review: pending -->

*Proof tree (automatic faithful draft).*

```text
    Γ,x:A⊢ x:A
──────────────────
Γ,x:A⊢ refl:x=_A x
```

and similarly we have elimination and computation rules.

<!-- rosetta-item-end: remark-5.1.4 -->
