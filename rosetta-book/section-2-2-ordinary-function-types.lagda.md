# Ordinary function types

```agda
module section-2-2-ordinary-function-types where

open import universe-levels
```

An important special case of `Π`-types arises when both `A` and `B` are types in context `Γ`. In this case, we can first weaken `B` by `A` and then apply the `Π`-formation rule to obtain the type `A → B` of *ordinary* functions from `A` to `B`, as in the following derivation:

```text
   Γ ⊢ A type    Γ ⊢ B type
  -------------------------- W
      Γ , x : A ⊢ B type
     -------------------- Π
      Γ ⊢ Π(x:A) B type.
```

A term `f : Π(x:A) B` is a function that takes an argument `x : A` and returns `f(x) : B`. In other words, terms of type `Π(x:A) B` are indeed ordinary functions from `A` to `B`. Therefore, we define the type `A → B` of **(ordinary) functions** from `A` to `B` by

```text
  A → B := Π(x:A) B.
```

If `f : A → B` is a function, then the type `A` is also called the **domain** of `f`, and the type `B` is also called the **codomain** of `f`.

Sometimes we will also write `Bᴬ` for the type `A → B`.  Formally, we make such definitions by adding one more line to the above derivation:

```text
      Γ ⊢ A type    Γ ⊢ B type
     -------------------------- W
         Γ, x : A ⊢ B type
        ------------------- Π
         Γ ⊢ Π(x:A) B type
  ------------------------------
   Γ ⊢ A → B :=  Π(x:A) B type.
```

## Remark 2.2.1

More generally, we can make definitions at the end of a derivation if the conclusion is a certain type in context, or if the conclusion is a certain term of a type in context. Suppose, for instance, that we have a derivation

```text
       𝒟
  ------------   
   Γ ⊢ a : A,
```

in which the derivation `𝒟` makes use of the premises `ℋ₁`, …, `ℋ_n`. If we wish to make a definition `c := a`, then we can extend the derivation tree with

```text
          𝒟
     -----------
      Γ ⊢ a : A
  ----------------
   Γ ⊢ c :=  a : A.
```

  The effect of such a definition is that we have extended our type theory with a new constant `c `, for which the following inference rules are valid
  

```text
   ℋ₁    ℋ₂    ⋯    ℋ_n
  -----------------------
        Γ ⊢ c :A
```

```text
   ℋ₁    ℋ₂    ⋯    ℋ_n
  -----------------------
      Γ ⊢ c ≐ a : A
```

In our example of the definition of the ordinary function type `A → B`, we therefore have by definition the following valid inference rules

```text
   Γ ⊢ A type    Γ ⊢ B type
  --------------------------
        Γ ⊢ A → B type
```

```text
    Γ ⊢ A type    Γ ⊢ B type
  ----------------------------
   Γ ⊢ A → B ≐ Π(x:A) B type.
```

There are of course many such definitions throughout the development of dependent type theory, the univalent foundations of mathematics, and synthetic homotopy theory. They are all included in the index at the end of this book.

## Remark 2.2.2

By the term conversion rules of Exercise 1.1 we can now use the rules for `λ`-abstraction, evaluation, and so on, to obtain corresponding rules for the ordinary function type `A → B`. We give a brief summary of these rules, omitting the congruence rules.

```text
   Γ ⊢ A type    Γ ⊢ B type
  -------------------------- →
        Γ ⊢ A → B type
```

```text
   Γ ⊢ B type    Γ, x : A ⊢ b(x) : B
  ----------------------------------- λ
        Γ ⊢ λ x. b(x) : A → B
```

```text
      Γ ⊢ f : A → B
  --------------------- ev
   Γ, x : A ⊢ f(x) : B
```

```text
    Γ ⊢ B type    Γ, x : A ⊢ b(x) : B
  -------------------------------------- β
   Γ, x : A ⊢ (λ y. b(y))(x) ≐ b(x) : B
```

```text
         Γ ⊢ f : A → B
  --------------------------- η
   Γ ⊢ λ x. f(x) ≐ f : A → B
```

Now we can use these rules to construct some familiar functions, such as the identity function `id : A → A` on an arbitrary type `A`, and the composition `g ∘ f : A → C` of any two functions `f : A → B` and `g : B → C`.

## Definition 2.2.3

For any type `A` in context `Γ`, we define the **identity function** `id : A → A` using the generic term:

```text
   Γ ⊢ A type    Γ, x : A ⊢ x : A
  --------------------------------
        Γ ⊢ λ x. x : A → A
    ---------------------------
     Γ ⊢ id := λ x. x : A → A.
```

The identity function therefore satisfies the following inference rules:

```text
     Γ ⊢ A type
  ----------------
   Γ ⊢ id : A → A
```

```text
          Γ ⊢ A type
  --------------------------
   Γ ⊢ id ≐ λ x. x : A → A.
```

## Agda implementation

```agda
id : {l : Level} {A : Type l} → A → A
id a = a

id' : {l : Level} (A : Type l) → A → A
id' A = id

idω : {A : Typeω} → A → A
idω a = a
```

Next, we define the composition of functions. We will introduce the composition operation itself as a function `comp` that takes two arguments: the first argument is a function `g : B → C`, and the second argument is a function `f : A → B`. The output is a function `comp(g,f) : A → C`, for which we often write `g ∘ f`.

## Rermark 2.2.4

Since composition is a function that takes multiple arguments, we need to know how to represent such functions.
Types of functions with multiple arguments can be formed by iterating the `Π`-formation rule or the `→`-formation rule. For example, a function

```text
  f : A → (B → C)
```

takes two arguments: first it takes an argument `x : A`, and the output `f(x)` has type `B → C`. This is again a function type, so `f(x)` is a function that takes an argument `y : B`, and its output `f(x)(y)` has type `C`. We will usually write `f(x,y)` for `f(x)(y)`.

Similarly, when `C(x,y)` is a family of types indexed by `x : A` and `y : B(x)`, then we can form the dependent function type `Π(x:A) Π(y:B(x)) C(x,y)`. In the special case where `C(x,y)` is a family of types indexed by two elements `x, y : A` of the same type, then we often write

```text
  Π(x,y:A) C(x,y)
```

for the type `Π(x:A) Π(y:A) C(x,y)`.

With the idea of iterating function types, we see that type of the composition operation `comp` is

```text
  (B → C) → ((A → B) → (A → C)).
```

It is the type of functions, taking a function `g : B → C`, to the type of functions `(A → B) → (A → C)`. Thus, `comp(g)` is again a function, mapping a function `f : A → B` to a function of type `A → C`.

## Definition 2.2.5

For any three types `A`, `B`, and `C` in context `Γ`, there is a **composition** operation

```text
  comp : (B → C) → ((A → B) → (A → C)).
```

We will usually write `g ∘ f` for `comp(g,f)`.

## Construction

The idea of the definition is to define `comp(g,f)` to be the function `λ x. g(f(x))`. The function `comp` is therefore defined as

```text
  comp :=  λ g. λ f. λ x. g(f(x)).
```

The derivation we use to construct `comp` is as follows:

```text

                                                   Γ ⊢ B type     Γ ⊢ C type
                                                 ----------------------------- (b)
         Γ ⊢ A type    Γ ⊢ B type                 Γ, g : Cᴮ, y : B ⊢ g(y) : C
       ----------------------------- (a)     -------------------------------------
        Γ, f : Bᴬ, x : A ⊢ f(x) : B           Γ, g : Cᴮ, f : Bᴬ, y : B ⊢ g(y) : C
   -------------------------------------  --------------------------------------------
    Γ, g : Cᴮ, f : Bᴬ, x : A ⊢ f(x) : B    Γ, g : Cᴮ, f : Bᴬ, x : A, y : B ⊢ g(y) : C
   ----------------------------------------------------------------------------------
                      Γ, g : Cᴮ, f : Bᴬ, x : A ⊢ g(f(x)) : C
                     ----------------------------------------
                       Γ, g : Cᴮ, f : Bᴬ ⊢ λ x. g(f(x)) : Cᴬ
                   --------------------------------------------
                    Γ, g : B → C ⊢ λ f. λ x. g(f(x)) : Bᴬ → Cᴬ
                   ---------------------------------------------
                    Γ ⊢ λ g. λ f. λ x. g(f(x)) : Cᴮ → (Bᴬ → Cᴬ)
               ------------------------------------------------------  
                Γ ⊢ comp := λ g. λ f. λ x. g(f(x)) : Cᴮ → (Bᴬ → Cᴬ).
```

Note, however, that we haven't derived the rules (a) and (b) yet. These rules assert that the *generic functions* of `A → B` and `B → C` can also be evaluated. The formal derivation of this fact is as follows:

```text
       Γ ⊢ A type    Γ ⊢ B type
      --------------------------
             Γ ⊢ A → B type
      --------------------------
       Γ, f : A → B ⊢ f : A → B
   ---------------------------------
    Γ, f : A → B, x : A ⊢ f(x) : B.
```

This completes the construction of `comp`.

## Agda implementation

In the implementation we use a slightly more general definition of composition, which allows us to compose dependent functions.

```agda
infixr 15 _∘_

_∘_ :
  {l1 l2 l3 : Level}
  {A : Type l1} {B : A → Type l2} {C : (a : A) → B a → Type l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
```

In the remainder of this section we will see how to use the given rules for function types to derive the laws of a category for functions. These are the laws that assert that function composition is associative and that the identity function satisfies the unit laws.

## Lemma 2.2.6

Composition of functions is associative, i.e., we can derive

```text
   Γ ⊢ f : A → B    Γ ⊢ g : B → C    Γ ⊢ h : C → D
  -------------------------------------------------
       Γ ⊢ (h ∘ g) ∘ f ≐ h ∘ (g ∘ f) : A → D.
```

## Proof

The main idea of the proof is that both `((h ∘ g) ∘ f)(x)` and `(h ∘ (g ∘ f))(x)` evaluate to `h(g(f(x))`, and therefore `(h ∘ g) ∘ f` and `h ∘ (g ∘ f)` must be judgmentally equal. This idea is made formal in the following derivation:

```text

                                   Γ ⊢ g : B → C
                               ---------------------
        Γ ⊢ f : A → B           Γ, y : B ⊢ g(y) : C               Γ ⊢ h : C → D
    ---------------------  ----------------------------      ---------------------
     Γ, x : A ⊢ f(x) : B    Γ, x : A, y : B ⊢ g(y) : C        Γ, z : C ⊢ h(z) : D
    ---------------------------------------------------  ----------------------------
                 Γ, x : A ⊢ g(f(x)) : C                   Γ, x : A, z : C ⊢ h(z) : D
                ----------------------------------------------------------------------
                                   Γ, x : A ⊢ h(g(f(x))) : D
                           ----------------------------------------
                            Γ, x : A ⊢ h(g(f(x))) ≐ h(g(f(x))) : D
                         ---------------------------------------------
                          Γ, x : A ⊢ (h∘ g)(f(x)) ≐ h((g ∘ f)(x)) : D
                      ----------------------------------------------------
                       Γ, x : A ⊢ ((h ∘ g) ∘ f)(x) ≐ (h ∘ (g ∘ f))(x) : D
                      ----------------------------------------------------
                             Γ ⊢ (h ∘ g) ∘ f ≐ h ∘ (g ∘ f) : A → D.
```

## Lemma 2.2.7

Composition of functions satisfies the left and right unit laws, i.e., we can derive

```text
       Γ ⊢ f : A → B
  ------------------------
   Γ ⊢ id ∘ f ≐ f : A → B
```

and

```text
        Γ ⊢ f : A → B
  -------------------------
   Γ ⊢ f ∘ id ≐ f : A → B.
```


## Proof

Note that it suffices to derive that `id (f(x)) ≐ f(x)` in context `Γ, x : A`, because once we derived this equality we can finish the derivation with

```text
                      ⋮
      ---------------------------------
       Γ, x : A ⊢ id (f(x)) ≐ f(x) : B               Γ ⊢ f : A → B
   ----------------------------------------  ---------------------------
    Γ ⊢ λ x. id (f(x)) ≐ λ x. f(x) : A → B    Γ ⊢ λ x. f(x) ≐ f : A → B
   ---------------------------------------------------------------------
                       Γ ⊢ id ∘ f ≐ f : A → B.
```

The derivation of the equality `id (f(x))≐ f(x)` in context `Γ,x:A` is as follows:

```text
                                                   Γ ⊢ B type
                                          --------------------------
         Γ ⊢ f : A → B       Γ ⊢ A type    Γ, y : B ⊢ id(y) ≐ y : B
     ---------------------  ----------------------------------------
      Γ, x : A ⊢ f(x) : B        Γ, x : A, y : B ⊢ id(y) ≐ y : B
     ------------------------------------------------------------
                Γ, x : A ⊢ id (f(x)) ≐ f(x) : B.
```

We leave the right unit law as Exercise 2.2.
  
