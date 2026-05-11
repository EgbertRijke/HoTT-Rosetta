# The rules for dependent function types

Consider a section `b` of a family `B` over `A` in context `Γ`, i.e., consider

```text
  Γ, x : A ⊢ b(x) : B(x).
```

From one point of view, such a section `b` is an operation or assignment `x ↦ b(x)`, or a program, that takes as input `x : A` and produces a term `b(x) : B(x)`. From a more mathematical point of view we see `b` as a choice of an element of each `B(x)`. In other words, we may see `b` as a function that takes `x : A` to `b(x) : B(x)`. Note that the type `B(x)` of the output may depend on `x : A`. The assignment `x ↦ b(x)` is in this sense a *dependent* function. The type of all such dependent functions is called the **dependent function type**, and we will write

```text
  Π(x:A) B(x)
```

for the type of dependent functions. There are four principal rules for `Π`-types:

1. The *formation rule*, which tells us how we may form dependent function types.
2. The *introduction rule*, which tells us how to introduce new terms of dependent function types.
3. The *elimination rule*, which tells us how to use arbitrary terms of dependent function types.
4. The *computation rules*, which tell us how the introduction and elimination rules interact. These computation rules guarantee that every term of a dependent function type is indeed a dependent function taking the values by which it is defined.

In the cases of the formation rule, the introduction rule, and the elimination rule, we also need rules that assert that all the constructions respect judgmental equality. Those rules are called **congruence rules**, and they are part of the specification of dependent function types.

## The `Π`-formation rule

The **`Π`-formation rule** tells us how `Π`-types are constructed. The idea of `Π`-types is that `Π(x:A) B(x)` is a type of **dependent functions**, for any type family `B` of types over `A`, so the `Π`-formation rule is as follows:

```text
   Γ , x : A ⊢ B(x) type
  ----------------------- Π.
    Γ ⊢ Π(x:A) B(x) type
```

This rule simply states that in order to form the type `Π(x:A) B(x)` in context `Γ`, we must have a type family `B` over `A` in context `Γ`.

We also require that the operation of forming dependent function types respects judgmental equality. This is postulated in the **congruence rule** for `Π`-types:

```text
   Γ ⊢ A ≐ A' type    Γ, x : A ⊢ B(x) ≐ B'(x) type
  ------------------------------------------------- Π-eq.
        Γ ⊢ Π(x:A) B(x) ≐ Π(x:A') B'(x) type
```

## The `Π`-introduction rule

The introduction rule for dependent functions tells us how we may construct dependent functions of type `Π(x:A) B(x)`. The idea is that a dependent function `f : Π(x:A) B(x)` is an operation that takes an `x : A` to `f(x) : B(x)`. Hence the introduction rule of dependent functions postulates that, in order to construct a dependent function one has to construct a term `b(x) : B(x)` indexed by `x : A` in context `Γ`, i.e.:

```text
     Γ, x : A ⊢ b(x) : B(x)
  ----------------------------- λ.
   Γ ⊢ λ x. b(x) : Π(x:A) B(x)
```

This introduction rule for dependent functions is also called the **`λ`-abstraction rule**, and we also say that the `λ`-abstraction `λ x. b(x)` **binds** the variable `x` in `b`. Just like ordinary mathematicians, we will sometimes write `x ↦ b(x)` for a function `λ x. b(x)`. The map `n ↦ n²` is an example.

We will also require that `λ`-abstraction respects judgmental equality. Therefore we postulate the **congruence rule** for `λ`-abstraction,

which asserts that

```text
        Γ, x : A ⊢ b(x) ≐ b'(x) : B(x)
  ------------------------------------------ λ-eq.
   Γ ⊢ λ x. b(x) ≐ λ x. b'(x) : Π(x:A) B(x)
```

## The `Π`-elimination rule

The elimination rule for dependent function types provides us with a way to *use* dependent functions. The way to use a dependent function is to evaluate it at an argument of the domain type. The `Π`-elimination rule is therefore also called the **evaluation rule**:

```text
    Γ ⊢ f : Π(x:A) B(x)
  ------------------------ ev.
   Γ, x : A ⊢ f(x) : B(x)
```

This rule asserts that given a dependent function `f : Π(x:A) B(x)` in context `Γ` we obtain a term `f(x)` of type `B(x)` indexed by `x : A` in context `Γ`. Again we require that evaluation respects judgmental equality:

```text
     Γ ⊢ f ≐ f' : Π(x:A) B(x)
  ------------------------------ ev-eq.
   Γ, x:A ⊢ f(x) ≐ f'(x) : B(x)
```

## The `Π`-computation rules

We now postulate rules that specify the behavior of functions. First, we have a rule that asserts that a function of the form `λ x. b(x)` behaves as expected: when we evaluate it at `x : A`, then we obtain the value `b(x) : B(x)`. This rule is called the **`β`-rule**

```text
            Γ, x : A ⊢ b(x) : B(x)
  ----------------------------------------- β.
   Γ, x : A ⊢ (λ y. b(y))(x) ≐ b(x) : B(x)
```

Second, we postulate a rule that asserts that all elements of a `Π`-type are (dependent) functions. This rule is known as the **`η`-rule**

```text
         Γ ⊢ f : Π(x:A) B(x)
  --------------------------------- η.
   Γ ⊢ λ x. f(x) ≐ f : Π(x:A) B(x)
```

In other words, the computation rules (`β` and `η`) for dependent function types postulate that `λ`-abstraction rule and the evaluation rule are mutual inverses. This completes the specification of dependent function types.
