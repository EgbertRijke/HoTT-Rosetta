# Section 1.1 Judgments and contexts in type theory

```agda
module section-1-1-judgments-and-contexts-in-type-theory where
```

A mathematical argument or construction consists of a sequence of deductive steps, each one using finitely many premises in order to get to the next stage in the proof or construction.
Such steps can be represented by **inference rules**, which are written in the form

```text
   ℋ₁    ℋ₂    ⋯    ℋ_n
  -----------------------
             𝒞.
```

Inference rules contain above the horizontal line a finite list `ℋ₁`, `ℋ₂`, ⋯, `ℋ_n` of *judgments* for the **premises**, and below the horizontal line a single judgment `𝒞` for the **conclusion**.
The system of dependent type theory is described by a set of such inference rules.

A straightforward example of an inference rule that we will encounter in Chapter 2 when we introduce function types, is the inference rule

```text
   Γ ⊢ a : A    Γ ⊢ f : A → B
  ----------------------------
         Γ ⊢ f(a) : B.
```

This rule asserts that in any context `Γ` we may use an element `a : A` and a function `f : A → B` to obtain an element `f(a) : B`.
Each of the expressions

```text
  Γ ⊢ a : A
  Γ ⊢ f : A → B
  Γ ⊢ f(a) : B
```

are examples of judgments.

## Definition 1.1.1

There are four kinds of **judgments** in Martin-Löf's dependent type theory:
- *`A` is a (well-formed) **type** in context `Γ `.*
  We express this judgment as

  ```text
    Γ ⊢ A Type.
  ```
  
- *`A` and `B` are **judgmentally equal types** in context `Γ `.*
  We express this judgment as

  ```text
    Γ ⊢ A ≐ B Type.
  ```

- *`a` is an **element** of type `A` in context `Γ `.*
  We express this judgment as

  ```text
    Γ  ⊢ a : A.
  ```

- *`a` and `b` are **judgmentally equal elements** of type `A` in context `Γ `.*
  We express this judgment as

  ```text
    Γ ⊢ a ≐ b : A.
  ```

We see that any judgment is of the form `Γ ⊢ 𝒥`, consisting of a *context* `Γ` and a *judgment thesis* `𝒥` asserting either that `A` is a type, that `A` and `B` are equal types, that `a` is an element of type `A`, or that `a` and `b` are equal elements of type `A`.
The role of a context is to declare what **hypothetical elements** are assumed, along with their types.
Hypothetical elements are commonly called **variables**.

## Definition 1.1.2

A **context** is a finite list of **variable declarations**

```text
  x₁ : A₁, x₂ : A₂(x₁), …, x_n : A_n(x₁,…,x_{n-1})          (✲)
```

satisfying the condition that for each `1 ≤ k ≤ n` we can derive the judgment

```text
  x₁ : A₁, …, x_{k-1} : A_{k-1}(x₁,…,x_{k-2})⊢ A_k(x₁,…,x_{k-1}) Type,
```text

using the inference rules of type theory.
We may use variable names other than `x₁,…,x_n`, as long as no variable is declared more than once.

The condition in Definition 1.1.2 that each of the hypothetical elements is assigned a type, is checked recursively.
In other words, to check that a list of variable declarations as in Equation (✲) is a context, one starts on the left and works their way to the right, verifying that each hypothetical elements `x_k` is assigned a type. 

Note that there is a context of length `0`, the **empty context**, which declares no variables.
This context satisfies the requirement in Definition 1.1.2 vacuously.
A list of variable declarations `x₁ : A₁` of length one is a context if and only if `A₁` is a type in the empty context.
We will soon encounter the type `ℕ` of natural numbers, which is an example of a type in the empty context.

The next case is that a list of variable declarations `x₁ : A₁, x₂ : A₂(x₁)` of length two is a context if and only if `A₁` is a type in the empty context, and `A₂(x₁)` is a type in context `x₁ : A₁`.
This process repeats itself for longer contexts.
