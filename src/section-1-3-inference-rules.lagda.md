# Section 1.3 Inference rules

```agda
module section-1-3-inference-rules where
```

We are now ready to present the system of inference rules that underlies
dependent type theory.
These rules are known as the **structural rules** of type theory, since they
establish the basic mathematical framework for type dependency.
There are six sets of inference rules:

1. Rules about the formation of contexts, types, and their elements.
2. Rules postulating that judgmental equality is an equivalence relation.
3. Variable conversion rules.
4. Substitution rules.
5. Weakening rules.
6. The generic element.

## Rules about the formation of contexts, types, and their elements

In the definition of well-formed contexts, types, and elements we specified
that for a type `B(x)` to be well-formed in context `Γ, x : A`, it must be the
case that `A` is a well-formed type in context `Γ`.
The following rules follow from the presuppositions about contexts, types, and
their elements, and may be used freely in derivations:

```text
  Γ, x : A ⊢ B(x) type
  --------------------
      Γ ⊢ A type

  Γ ⊢ a : A
  ----------
  Γ ⊢ A type

  Γ ⊢ A ≐ B type
  --------------
  Γ ⊢ A type

  Γ ⊢ A ≐ B type
  --------------
  Γ ⊢ B type

  Γ ⊢ a ≐ b : A
  -------------
    Γ ⊢ a : A

  Γ ⊢ a ≐ b : A
  -------------
    Γ ⊢ b : A
```

## Judgmental equality is an equivalence relation

The rules postulating that judgmental equality on types and on elements is an
equivalence relation simply postulate that these relations are reflexive,
symmetric, and transitive:

```text
  Γ ⊢ A type
  ----------
  Γ ⊢ A ≐ A type

  Γ ⊢ A ≐ B type
  --------------
  Γ ⊢ B ≐ A type

  Γ ⊢ A ≐ B type    Γ ⊢ B ≐ C type
  --------------------------------
             Γ ⊢ A ≐ C type

  Γ ⊢ a : A
  ---------
  Γ ⊢ a ≐ a : A

  Γ ⊢ a ≐ b : A
  -------------
  Γ ⊢ b ≐ a : A

  Γ ⊢ a ≐ b : A    Γ ⊢ b ≐ c : A
  -------------------------------
            Γ ⊢ a ≐ c : A
```

## Variable conversion rules

The **variable conversion rules** are rules postulating that we can convert the
type of a variable to a judgmentally equal type.
The first variable conversion rule states that

```text
  Γ ⊢ A ≐ A' type    Γ, x : A, Δ ⊢ B(x) type
  ------------------------------------------------
            Γ, x : A', Δ ⊢ B(x) type.
```

In this conversion rule, the context `Γ, x : A, Δ` is just any extension of
the context `Γ, x : A`, i.e., it is a context of the form

```text
  x₁ : A₁, …, x_{n-1} : A_{n-1},
  x : A,
  x_{n+1} : A_{n+1}, …, x_{n+m} : A_{n+m}.
```

Similarly, there are variable conversion rules for judgmental equality of
types, for elements, and for judgmental equality of elements.
To avoid having to state essentially the same rule four times, we state all
four variable conversion rules at once using a *generic judgment thesis* `𝒥`,
which can be any of the four kinds described in Definition 1.1.1:

```text
  Γ ⊢ A ≐ A' type    Γ, x : A, Δ ⊢ 𝒥
  ----------------------------------
           Γ, x : A', Δ ⊢ 𝒥.
```

An analogous *element conversion rule*, converting the type of an element to a
judgmentally equal type, is derivable using the rules presented in this
section.

## Substitution

Consider an element `f(x) : B(x)` indexed by `x : A` in context `Γ`, and
suppose we also have an element `a : A`.
Then we can simultaneously substitute `a` for all occurrences of `x` in
`f(x)` to obtain a new element `f[a/x]`, which has type `B[a/x]`.
A precise definition of substitution requires us to get too deep into the
theory of the syntax of type theory, but a mathematician is of course no
stranger to substitution.
For example, substituting `0` for `x` in the polynomial

```text
  1 + x + x² + x³
```

results in the number `1 + 0 + 0² + 0³`, which can be computed to the value
`1`.

Type theoretic substitution is similar.
Type theoretic substitution is in fact a bit more general than what we have
described above.
Suppose we have a type

```text
  Γ, x : A, y₁ : B₁, …, y_n : B_n ⊢ C type
```

and an element `a : A` in context `Γ`.
Then we can simultaneously substitute `a` for all occurrences of `x` in the
types `B₁, …, B_n` and `C`, to obtain

```text
  Γ, y₁ : B₁[a/x], …, y_n : B_n[a/x] ⊢ C[a/x] type.
```

Note that the variables `y₁, …, y_n` are assigned new types after performing
the substitution of `a` for `x`.
Similarly, we can substitute `a` for `x` in an element `c : C` to obtain the
element `c[a/x] : C[a/x]`, and we can substitute `a` for `x` in a judgmental
equality thesis, either of types or elements, by simply substituting on both
sides of the equation.
The **substitution rule** is therefore stated using a generic judgment `𝒥`:

```text
  Γ ⊢ a : A    Γ, x : A, Δ ⊢ 𝒥
  -------------------------------- S
      Γ, Δ[a/x] ⊢ 𝒥[a/x]
```

Furthermore, we add two more congruence rules for substitution, postulating
that substitution by judgmentally equal elements results in judgmentally equal
types and elements:

```text
  Γ ⊢ a ≐ a' : A    Γ, x : A, Δ ⊢ B type
  --------------------------------------
       Γ, Δ[a/x] ⊢ B[a/x] ≐ B[a'/x] type

  Γ ⊢ a ≐ a' : A    Γ, x : A, Δ ⊢ b : B
  -------------------------------------
       Γ, Δ[a/x] ⊢ b[a/x] ≐ b[a'/x] : B[a/x].
```

To see that these rules make sense, we observe that both `B[a/x]` and
`B[a'/x]` are types in context `Δ[a/x]`, provided that `a ≐ a'`.
This is immediate by recursion on the length of `Δ`.

## Definition 1.3.1

When `B` is a family of types over `A` in context `Γ`, and if we have `a : A`,
then we also say that `B[a/x]` is the **fiber** of `B` at `a`.
We will usually write `B(a)` for the fiber of `B` at `a`.

When `b` is a section of the family `B` over `A` in context `Γ`, we call the
element `b[a/x]` the **value** of `b` at `a`.
Again, we will usually write `b(a)` for the value of `b` at `a`.

## Weakening

If we are given a type `A` in context `Γ`, then any judgment made in a longer
context `Γ, Δ` can also be made in the context `Γ, x : A, Δ`, for a fresh
variable `x`.
The **weakening rule** asserts that weakening by a type `A` in context
preserves well-formedness and judgmental equality of types and elements.

```text
  Γ ⊢ A type    Γ, Δ ⊢ 𝒥
  ---------------------- W
      Γ, x : A, Δ ⊢ 𝒥
```

This process of expanding the context by a fresh variable of type `A` is
called **weakening** by `A`.

In the simplest situation where weakening applies, we have two types `A` and
`B` in context `Γ`.
Then we can weaken `B` by `A` as follows

```text
  Γ ⊢ A type    Γ ⊢ B type
  ------------------------ W
      Γ, x : A ⊢ B type
```

in order to form the type `B` in context `Γ, x : A`.
The type `B` in context `Γ, x : A` is called the **constant family** `B`, or
the **trivial family** `B`.

## The generic elements

If we are given a type `A` in context `Γ`, then we can weaken `A` by itself to
obtain that `A` is a type in context `Γ, x : A`.
The rule for the **generic element** now asserts that any hypothetical element
`x : A` in the context `Γ, x : A` is also an element of type `A` in context
`Γ, x : A`.

```text
  Γ ⊢ A type
  -------------------- δ
  Γ, x : A ⊢ x : A
```

This rule is also known as the **variable rule**.
One of the reasons for including the generic element is to make sure that the
variables declared in a context, i.e., the hypothetical elements, are indeed
*elements*.
It also provides the **identity function** on the type `A` in context `Γ`.
