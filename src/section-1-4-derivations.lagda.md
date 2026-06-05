# Section 1.4 Derivations

```agda
module section-1-4-derivations where
```

A **derivation** in type theory is a finite tree in which each node is a valid
rule of inference.
At the root of the tree we find the conclusion, and in the leaves of the tree
we find the hypotheses.
We give two examples of derivations: a derivation showing that any variable
can be changed to a fresh one, and a derivation showing that any two variables
that do not mutually depend on one another can be swapped in order.

Given a derivation with hypotheses `ℋ₁, …, ℋ_n` and conclusion
`𝒞`, we can form a new inference rule

```text
  ℋ₁    ⋯    ℋ_n
  --------------
        𝒞.
```

Such a rule is called **derivable**, because we have a derivation for it.
In order to keep proof trees reasonably short and manageable, we use the
convention that any derived rules can be used in future derivations.

## Changing variables

Variables can always be changed to fresh variables.
We show that this is the case by showing that the inference rule

```text
  Γ, x : A, Δ ⊢ 𝒥
  ------------------------------------- x'/x
  Γ, x' : A, Δ[x'/x] ⊢ 𝒥[x'/x]
```

is derivable, where `x'` is a variable that does not occur in the context
`Γ, x : A, Δ`.

Indeed, we have the following derivation using substitution, weakening, and
the generic element:

```text
  Γ ⊢ A type
  -------------------- δ
  Γ, x' : A ⊢ x' : A

  Γ ⊢ A type    Γ, x : A, Δ ⊢ 𝒥
  -------------------------------- W
  Γ, x' : A, x : A, Δ ⊢ 𝒥

  Γ, x' : A ⊢ x' : A    Γ, x' : A, x : A, Δ ⊢ 𝒥
  ------------------------------------------------ S
      Γ, x' : A, Δ[x'/x] ⊢ 𝒥[x'/x]
```

In this derivation it is the application of the weakening rule where we have
to check that `x'` does not occur in the context `Γ, x : A, Δ`.

## Interchanging variables

The **interchange rule** states that if we have two types `A` and `B` in
context `Γ`, and we make a judgment in context `Γ, x : A, y : B, Δ`, then we
can make that same judgment in context `Γ, y : B, x : A, Δ` where the order of
`x : A` and `y : B` is swapped.
More formally, the interchange rule is the following inference rule

```text
  Γ ⊢ B type    Γ, x : A, y : B, Δ ⊢ 𝒥
  ------------------------------------
       Γ, y : B, x : A, Δ ⊢ 𝒥.
```

Just as the rule for changing variables, we claim that the interchange rule is
a derivable rule.

The idea of the derivation for the interchange rule is as follows.
If we have a judgment

```text
  Γ, x : A, y : B, Δ ⊢ 𝒥,
```

then we can change the variable `y` to a fresh variable `y'` and weaken the
judgment to obtain the judgment

```text
  Γ, y : B, x : A, y' : B, Δ[y'/y] ⊢ 𝒥[y'/y].
```

Now we can substitute `y` for `y'` to obtain the desired judgment
`Γ, y : B, x : A, Δ ⊢ 𝒥`.
The formal derivation is as follows:

```text
  Γ ⊢ B type
  ------------------ δ
  Γ, y : B ⊢ y : B
  -------------------------- W
  Γ, y : B, x : A ⊢ y : B

  Γ ⊢ B type    Γ, x : A, y : B, Δ ⊢ 𝒥
  ------------------------------------ y'/y
  Γ, x : A, y' : B, Δ[y'/y] ⊢ 𝒥[y'/y]
  ------------------------------------------------ W
  Γ, y : B, x : A, y' : B, Δ[y'/y] ⊢ 𝒥[y'/y]

  Γ, y : B, x : A ⊢ y : B
  Γ, y : B, x : A, y' : B, Δ[y'/y] ⊢ 𝒥[y'/y]
  ------------------------------------------------ S
  Γ, y : B, x : A, Δ ⊢ 𝒥
```
