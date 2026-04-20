# Section 1.2 Type families

```agda
module section-1-2-type-families where
```

It is a feature of *dependent* type theory that all judgments are context dependent, and indeed that even the types of the variables in a context may depend on any previously declared variables. For example, if `n` is a natural number and we know from the context that `n` is prime, then we don't have enough information yet to decide whether or not `n` is odd. However, if we also know from the context that `n + 2` is prime, then we can derive that `n` must be odd. Context dependency is everywhere---not only in mathematics, but also in language and in everyday life---and it gives rise to the notion of *type families* and their *sections*.

## Definition 1.2.1
  Consider a type `A` in context `Γ`. A **family** of types over `A` in context `Γ` is a type `B(x)` in context `Γ, x : A`. In other words, in the situation where

```text
  Γ, x : A ⊢ B(x) type,
```

we say that `B` is a family of types over `A` in context `Γ`. Alternatively, we say that `B(x)` is a type *indexed* by `x : A`, in context `Γ`.

We think of a type family `B` over `A` in context `Γ` as a type `B(x)` varying along `x : A`. A basic example of a type family occurs when we introduce *identity types* in Chapter 5. They are introduced as follows:

```text
  \AxiomC{`Γ ⊢ a : A`}
  \UnaryInfC{`Γ, x : A ⊢ a = x type`.}
```

This rule asserts that given an element `a : A` in context `Γ`, we may form the type `a = x` in context `Γ, x : A`. The type `a = x` in context `Γ, x : A` is an example of a type family over `A` in context `Γ`.

## Definition 1.2.2

Consider a type family `B` over `A` in context `Γ`. A **section** of the family `B` over `A` in context `Γ` is an element of type `B(x)` in context `Γ, x : A`, i.e., in the judgment

```text
  Γ, x : A ⊢ b(x) : B(x)
```

we say that `b` is a section of the family `B` over `A` in context `Γ`. Alternatively, we say that `b(x)` is an element of type `B(x)` **indexed** by `x : A` in context `Γ`.

Note that in the above situations `A`, `B`, and `b` also depend on the variables declared in the context `Γ`, even though we have not explicitly mentioned them. It is indeed common practice to not mention every variable in the context `Γ` in such situations.
