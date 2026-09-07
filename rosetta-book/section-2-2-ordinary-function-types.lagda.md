# Section 2.2 Ordinary function types

```agda
module section-2-2-ordinary-function-types where

open import universe-levels
```

<!-- rosetta-item: section-2.2 -->

An important special case of `Π`-types arises when both `A` and `B` are types in context `Γ`.
In this case, we can first weaken `B` by `A` and then apply the `Π`-formation rule to obtain the type `A→ B` of *ordinary* functions from `A` to `B`, as in the following derivation:

<!-- rosetta-proof-tree: 36158e86a79a; review: pending -->

*Proof tree (automatic faithful draft).*

```text
  Γ⊢ A \textrm{type}   Γ⊢ B \textrm{type}
─────────────────────────────────────── W
                 Γ,x:A⊢ B \textrm{type}
───────────────────────────────────────── Π
       $Γ⊢ Π(x:A) B \textrm{type}$
```

A term `f:Π(x:A) B` is a function that takes an argument `x:A` and returns `f(x):B`.
In other words, terms of type `Π(x:A) B` are indeed ordinary functions from `A` to `B`.
Therefore, we define the type `A→ B` of **(ordinary) functions** from `A` to `B` by
```text
A→ B≔Π(x:A) B.
```
If `f:A→ B` is a function, then the type `A` is also called the **domain** of `f`, and the type `B` is also called the **codomain** of `f`.

Sometimes we will also write `B^A` for the type `A→ B`.
Formally, we make such definitions by adding one more line to the above derivation:

<!-- rosetta-proof-tree: 3c5d5474d557; review: pending -->

*Proof tree (automatic faithful draft).*

```text
    Γ⊢ A \textrm{type}   Γ⊢ B \textrm{type}
  ─────────────────────────────────────── W
                    Γ,x:A⊢ B \textrm{type}
───────────────────────────────────────── Π
                Γ⊢ Π(x:A) B \textrm{type}
───────────────────────────────────────────
     $Γ⊢ A→ B ≔ Π(x:A) B \textrm{type}$
```

## Remark 2.2.1

<!-- rosetta-item: remark-2.2.1 -->

More generally, we can make definitions at the end of a derivation if the conclusion is a certain type in context, or if the conclusion is a certain term of a type in context.
Suppose, for instance, that we have a derivation

<!-- rosetta-proof-tree: baee45fb1099; review: pending -->

*Proof tree (automatic faithful draft).*

```text
    D
─────────
$Γ⊢ a:A$,
```

in which the derivation `D` makes use of the premises `H_1`, …,`H_n`.
If we wish to make a definition `c≔ a`, then we can extend the derivation tree with

<!-- rosetta-proof-tree: 77d5b36d644b; review: pending -->

*Proof tree (automatic faithful draft).*

```text
      D
  ──────
  Γ⊢ a:A
──────────
$Γ⊢c≔ a:A$
```

The effect of such a definition is that we have extended our type theory with a new constant `c`, for which the following inference rules are valid

<!-- unsupported LaTeX environment: center -->

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: fb4e66883881; review: pending -->

*Proof tree (automatic faithful draft).*

```text
H_1$ $H_2$ \dots $H_n
─────────────────────
        Γ⊢c:A
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 0d3df12f6594; review: pending -->

*Proof tree (automatic faithful draft).*

```text
H_1$ $H_2$ \dots $H_n
─────────────────────
      $Γ⊢c≐ a:A$
```

In our example of the definition of the ordinary function type `A→ B`, we therefore have by definition the following valid inference rules

<!-- unsupported LaTeX environment: center -->

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 4932f369462d; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ A \textrm{type}   Γ⊢ B \textrm{type}
───────────────────────────────────────
         Γ⊢ A→ B \textrm{type}
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 8f76c41bb3d9; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ A \textrm{type}   Γ⊢ B \textrm{type}
───────────────────────────────────────
   $Γ⊢ A→ B≐ Π(x:A) B \textrm{type}$
```

There are of course many such definitions throughout the development of dependent type theory, the univalent foundations of mathematics, and synthetic homotopy theory.
They are all included in the index at the end of this book.

<!-- rosetta-item-end: remark-2.2.1 -->

## Remark 2.2.2

<!-- rosetta-item: remark-2.2.2 -->

By the term conversion rules of Exercise 1.1 we can now use the rules for `λ`-abstraction, evaluation, and so on, to obtain corresponding rules for the ordinary function type `A→ B`.
We give a brief summary of these rules, omitting the congruence rules.

<!-- rosetta-proof-tree: a76327c3dc3d; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ A \textrm{type}   Γ⊢ B \textrm{type}
─────────────────────────────────────── →
         Γ⊢ A→ B \textrm{type}
```

<!-- unsupported LaTeX environment: center -->

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 368109a25c5a; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ B \textrm{type}   Γ,x:A⊢ b(x):B
────────────────────────────────── λ
        Γ⊢ λ x. b(x):A→ B
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 44b9bf29410c; review: pending -->

*Proof tree (automatic faithful draft).*

```text
  Γ⊢ f:A→ B
───────────── ev
Γ,x:A⊢ f(x):B
```

<!-- unsupported LaTeX environment: center -->

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 35fde85ce8fa; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ B \textrm{type}   Γ,x:A⊢ b(x):B
────────────────────────────────── β
   Γ,x:A⊢(λ y. b(y))(x)≐ b(x):B
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 405b10090e15; review: pending -->

*Proof tree (automatic faithful draft).*

```text
     Γ⊢ f:A→ B
─────────────────── η
Γ⊢λ x. f(x)≐ f:A→ B
```

<!-- rosetta-agda-block: remark-2.2.2-evaluation-at-a-point -->

```agda
ev-point :
  {l1 l2 : Level} {A : Type l1} (a : A) {P : A → Type l2} → ((x : A) → P x) → P a
ev-point a f = f a
```
<!-- rosetta-item-end: remark-2.2.2 -->

Now we can use these rules to construct some familiar functions, such as the identity function `id:A→ A` on an arbitrary type `A`, and the composition `g∘ f:A→ C` of any two functions `f:A→ B` and `g:B→ C`.

## Definition 2.2.3

<!-- rosetta-item: definition-2.2.3 -->

For any type `A` in context `Γ`, we define the **identity function** `id[A]:A→ A` using the generic term:

<!-- rosetta-proof-tree: 226a8c99c4e3; review: pending -->

*Proof tree (automatic faithful draft).*

```text
  Γ⊢ A \textrm{type}
  ──────────────────
         Γ,x:A⊢ x:A
  ──────────────────
     Γ⊢ λ x. x:A→ A
──────────────────────
$Γ⊢ id[A]≔λ x. x:A→ A$
```

<!-- rosetta-agda-block: section-2-2-identity-function-adapted -->

```agda
id : {l : Level} {A : Type l} → A → A
id a = a
```
<!-- rosetta-item-end: definition-2.2.3 -->

The identity function therefore satisfies the following inference rules:

<!-- unsupported LaTeX environment: center -->

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 64b471c1cd14; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ A \textrm{type}
──────────────────
  Γ⊢ id[A]:A→ A
```

<!-- unsupported LaTeX environment: minipage -->

<!-- rosetta-proof-tree: 19ae9daec232; review: pending -->

*Proof tree (automatic faithful draft).*

```text
  Γ⊢ A \textrm{type}
──────────────────────
$Γ⊢ id[A]≐λ x. x:A→ A$
```

Next, we define the composition of functions.
We will introduce the composition operation itself as a function `comp` that takes two arguments: the first argument is a function `g:B→ C`, and the second argument is a function `f:A→ B`.
The output is a function `comp(g,f):A→ C`, for which we often write `g∘ f`.

## Remark 2.2.4

<!-- rosetta-item: remark-2.2.4 -->

Since composition is a function that takes multiple arguments, we need to know how to represent such functions.
Types of functions with multiple arguments can be formed by iterating the `Π`-formation rule or the `→`-formation rule.
For example, a function
```text
f:A→ (B→ C)
```
takes two arguments: first it takes an argument `x:A`, and the output `f(x)` has type `B→ C`.
This is again a function type, so `f(x)` is a function that takes an argument `y:B`, and its output `f(x)(y)` has type `C`.
We will usually write `f(x,y)` for `f(x)(y)`.

Similarly, when `C(x,y)` is a family of types indexed by `x:A` and `y:B(x)`, then we can form the dependent function type `Π(x:A) Π(y:B(x)) C(x,y)`.
In the special case where `C(x,y)` is a family of types indexed by two elements `x,y:A` of the same type, then we often write
```text
Π(x,y:A) C(x,y)
```
for the type `Π(x:A) Π(y:A) C(x,y)`.

With the idea of iterating function types, we see that type of the composition operation `comp` is
```text
(B→ C)→ ((A→ B)→ (A→ C)).
```
It is the type of functions, taking a function `g:B→ C`, to the type of functions `(A→ B)→ (A→ C)`.
Thus, `comp(g)` is again a function, mapping a function `f:A→ B` to a function of type `A→ C`.

<!-- rosetta-item-end: remark-2.2.4 -->

## Definition 2.2.5

<!-- rosetta-item: definition-2.2.5 -->

For any three types `A`, `B`, and `C` in context `Γ`, there is a **composition** operation
```text
comp:(B→ C)→ ((A→ B)→ (A→ C)).
```
We will usually write `g∘ f` for `comp(g,f)`.

### Construction

<!-- rosetta-item: subheading-2.2-construction -->

The idea of the definition is to define `comp(g,f)` to be the function `λ x. g(f(x))`.
The function `comp` is therefore defined as
```text
comp≔ λ g. λ f. λ x. g(f(x)).
```
The derivation we use to construct `comp` is as follows:

<!-- unsupported LaTeX environment: small -->

<!-- rosetta-proof-tree: 74a14b9dd104; review: pending -->

*Proof tree (automatic faithful draft).*

```text
                                    Γ⊢ B type   Γ⊢ C type
                                ───────────────────── (b)
     Γ⊢ A type   Γ⊢ B type            Γ,g:C^B,y:B⊢ g(y):C
 ───────────────────── (a)      ─────────────────────────
       Γ,f:B^A,x:A⊢ f(x):B      Γ,g:C^B,f:B^A,y:B⊢ g(y):C
─────────────────────────   ─────────────────────────────
Γ,g:C^B,f:B^A,x:A⊢ f(x):B   Γ,g:C^B,f:B^A,x:A,y:B⊢ g(y):C
─────────────────────────────────────────────────────────
                           Γ,g:C^B,f:B^A,x:A⊢ g(f(x)) : C
─────────────────────────────────────────────────────────
                          Γ,g:C^B,f:B^A⊢ λ x. g(f(x)):C^A
─────────────────────────────────────────────────────────
                     Γ,g:B→ C⊢ λ f. λ x. g(f(x)):B^A→ C^A
─────────────────────────────────────────────────────────
               Γ⊢λ g. λ f. λ x. g(f(x)):C^B→ (B^A→ C^A)
─────────────────────────────────────────────────────────
     $Γ⊢comp≔ λ g. λ f. λ x. g(f(x)):C^B→ (B^A→ C^A)$
```

Note, however, that we haven’t derived the rules (a) and (b) yet.
These rules assert that the *generic functions* of `A→ B` and `B→ C` can also be evaluated.
The formal derivation of this fact is as follows:

<!-- rosetta-proof-tree: f169ee27e9a6; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ A type   Γ⊢ B type
─────────────────────
        Γ⊢ A → B type
─────────────────────
     Γ,f:A→ B⊢ f:A→ B
──────────────────────
$Γ,f:A→ B,x:A⊢ f(x):B$
```

This completes the construction of `comp`.

<!-- rosetta-agda-block: section-2-2-dependent-composition-adapted -->

```agda
infixr 15 _∘_

_∘_ :
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : (a : A) → B a → Type l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
```
<!-- rosetta-item-end: definition-2.2.5 -->

In the remainder of this section we will see how to use the given rules for function types to derive the laws of a category for functions.
These are the laws that assert that function composition is associative and that the identity function satisfies the unit laws.

## Lemma 2.2.6

<!-- rosetta-item: lemma-2.2.6 -->

Composition of functions is associative, i.e., we can derive

<!-- rosetta-proof-tree: 11f58f4aeab6; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ⊢ f:A→ B   Γ⊢ g:B→ C   Γ⊢ h:C→ D
─────────────────────────────────
  $Γ ⊢ (h∘ g)∘ f≐ h∘(g∘ f):A→ D$
```

### Proof

<!-- rosetta-item: subheading-2.2-proof -->

*Proof.* The main idea of the proof is that both `((h∘ g)∘ f)(x)` and `(h∘ (g∘ f))(x)` evaluate to `h(g(f(x))`, and therefore `(h∘ g)∘ f` and `h∘(g∘ f)` must be judgmentally equal.
This idea is made formal in the following derivation:

<!-- rosetta-proof-tree: 665b72f849c6; review: pending -->

*Proof tree (automatic faithful draft).*

```text
                                            Γ⊢ g:B→ C
                                        ─────────────
     Γ⊢ f:A→ B       Γ,y:B⊢ g(y):C          Γ⊢ h:C→ D
 ─────────────   ─────────────────      ─────────────
 Γ,x:A⊢ f(x):B   Γ,x:A,y:B⊢ g(y):C      Γ,z:C⊢ h(z):D
─────────────────────────────────   ─────────────────
             Γ,x:A⊢ g(f(x)):C       Γ,x:A,z:C⊢ h(z):D
─────────────────────────────────────────────────────
                                  Γ,x:A⊢ h(g(f(x))):D
─────────────────────────────────────────────────────
                      Γ,x:A⊢ h(g(f(x)))≐ h(g(f(x))):D
─────────────────────────────────────────────────────
                  Γ,x:A⊢ (h∘ g)(f(x))≐ h((g∘ f)(x)):D
─────────────────────────────────────────────────────
            Γ,x:A⊢ ((h∘ g)∘ f)(x)≐ (h∘ (g ∘ f))(x):D
─────────────────────────────────────────────────────
            $Γ⊢ (h∘ g)∘ f≐ h∘(g∘ f):A→ D$
``` ◻

<!-- rosetta-item-end: lemma-2.2.6 -->

## Lemma 2.2.7

<!-- rosetta-item: lemma-2.2.7; latex-label: lem:fun_unit -->

Composition of functions satisfies the left and right unit laws, i.e., we can derive

<!-- rosetta-proof-tree: f7d21f060db6; review: pending -->

*Proof tree (automatic faithful draft).*

```text
     Γ⊢ f:A→ B
───────────────────
Γ⊢ id[B]∘ f≐ f:A→ B
```

and

<!-- rosetta-proof-tree: acd94c5b7a9f; review: pending -->

*Proof tree (automatic faithful draft).*

```text
     Γ⊢ f:A→ B
────────────────────
$Γ⊢ f∘id[A]≐ f:A→ B$
```

### Proof

<!-- rosetta-item: subheading-2.2-proof-2 -->

*Proof.* Note that it suffices to derive that `id(f(x))≐ f(x)` in context `Γ,x:A`, because once we derived this equality we can finish the derivation with

<!-- rosetta-proof-tree: fe2814149929; review: pending -->

*Proof tree (automatic faithful draft).*

```text
                                 \vdots
                  ──────────────────────
       Γ,x:A⊢id(f(x))≐ f(x):B             Γ⊢ f:A→ B
──────────────────────────────   ───────────────────
Γ⊢λ x. id(f(x))≐λ x. f(x):A→ B   Γ⊢λ x. f(x)≐ f:A→ B
────────────────────────────────────────────────────
                 $Γ⊢id∘ f≐ f:A→ B$
```

The derivation of the equality `id(f(x))≐ f(x)` in context `Γ,x:A` is as follows:

<!-- rosetta-proof-tree: dd2c022b64a9; review: pending -->

*Proof tree (automatic faithful draft).*

```text
                                  Γ⊢ B type
                            ────────────────
   Γ⊢ f:A→ B    Γ⊢ A type   Γ,y:B⊢id(y)≐ y:B
─────────────   ────────────────────────────
 Γ,x:A⊢ f(x):B         Γ,x:A,y:B⊢id(y)≐ y:B
────────────────────────────────────────────
          $Γ,x:A⊢id(f(x))≐ f(x):B$
```

We leave the right unit law as Exercise 2.2. ◻

<!-- rosetta-item-end: lemma-2.2.7 -->
