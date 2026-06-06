# Section 12.1 Propositions

```agda
module section-12-1-propositions where
```

## Definition 12.1.1

A type `A` is said to be a **proposition** if its identity types are
contractible, i.e., if it comes equipped with a term of type

```text
  is-prop(A) := Π(x y : A) is-contr(x = y).
```

Given a universe `𝒰`, we define `Prop_𝒰` to be the type of all small
propositions, i.e.,

```text
  Prop_𝒰 := Σ(X : 𝒰) is-prop(X).
```

## Example 12.1.2

Any contractible type is a proposition by Exercise `ex:prop_contr`.
In particular, the unit type is a proposition.
The empty type is also a proposition, since we have

```text
  Π(x y : empty) is-contr(x = y)
```

by the induction principle of the empty type.

There are many conditions on a type `A` that are equivalent to the condition
that `A` is a proposition.
In the following proposition we state four such conditions.

## Proposition 12.1.3

Let `A` be a type.
Then the following are equivalent:

1. The type `A` is a proposition.
2. Any two terms of type `A` can be identified, i.e., there is a dependent
   function of type

```text
  is-prop'(A) := Π(x y : A) x = y.
```

3. The type `A` is contractible as soon as it is inhabited, i.e., there is a
   function of type

```text
  A → is-contr(A).
```

4. The map `const_star : A → unit` is an embedding.

## Proof

If `A` is a proposition, then we can use the center of contraction of the
identity types of `A` to identify any two terms in `A`.
This shows that (i) implies (ii).

To show that (ii) implies (iii), suppose that `A` comes equipped with
`p : Π(x y : A) x = y`.
Then for any `x : A` the dependent function `p(x) : Π(y : A) x = y` is a
contraction of `A`.
Thus we obtain the function

```text
  λ x → (x, p(x)) : A → is-contr(A).
```

To show that (iii) implies (iv), suppose that `A → is-contr(A)`.
We first make the simple observation that

```text
  (X → is-emb(f)) → is-emb(f)
```

for any map `f : X → Y`, so it suffices to show that
`A → is-emb(const_star)`.
However, assuming we have `x : A`, it follows by assumption that `A` is
contractible.
Therefore, it follows by Exercise `ex:contr_equiv` that the map
`const_star : A → unit` is an equivalence, and any equivalence is an embedding
by Corollary `cor:emb_equiv`.

To show that (iv) implies (i), note that if `A → unit` is an embedding, then
the identity types of `A` are equivalent to contractible types and therefore
they must be contractible.

One useful feature of propositions is that, in order to construct an
equivalence `e : P ≃ Q` between propositions, it suffices to construct maps
back and forth between them.

## Proposition 12.1.4

A map `f : P → Q` between two propositions `P` and `Q` is an equivalence if and
only if there is a map `g : Q → P`.
Consequently, we have for any two propositions `P` and `Q` that

```text
  (P ≃ Q) ↔ (P ↔ Q).
```

## Proof

Of course, if we have an equivalence `e : P ≃ Q`, then we get maps back and
forth between `P` and `Q`.
Therefore it remains to show that

```text
  (P ↔ Q) → (P ≃ Q).
```

Suppose we have `f : P → Q` and `g : Q → P`.
Then we obtain the homotopies `f ∘ g ~ id` and `g ∘ f ~ id` by the fact that
any two elements in `P` and `Q` can be identified.
Therefore `f` is an equivalence with inverse `g`.
