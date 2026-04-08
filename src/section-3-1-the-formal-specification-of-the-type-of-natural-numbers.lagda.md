# 3.1 The formal specification of the type of natural numbers 

```agda
module section-3-1-the-formal-specification-of-the-type-of-natural-numbers where

open import universe-levels
```

The type `ℕ` of **natural numbers** is the archetypal example of an inductive type. 
The rules we postulate for the type of natural numbers come in four sets, just as the rules for `Π`-types:

1. The formation rule, which asserts that the type ℕ can be formed.
2. The introduction rules, which provide the zero element `0` and the successor function `succ-ℕ`.
3. The elimination rule. This rule is the type theoretic version of the induction principle for `ℕ`.
4. The computation rules, which assert that any application of the elimination rule behaves as expected on the constructors `0` and `succ-ℕ` of `ℕ`.

## The formation rule of ℕ

The type `ℕ` is formed by the ℕ-**formation** rule

```text

  ---------- ℕ form 
   ⊢ ℕ type 
```

In other words, `ℕ` is postulated to be a type in the empty context.

## The introduction rules of `ℕ`

Unlike the set of positive integers in Bishop's remarks, Peano's first axiom postulates that `0` is a natural number. 
The introduction rules for `ℕ` equip it with the **zero element** and the **successor function**.

```text

  -----------
   ⊢ 0 : ℕ 
```

```text

  ------------------
   ⊢ succ-ℕ : ℕ → ℕ
```

```agda
data ℕ : Type lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

### Remark 3.1.1

Every element in type theory always comes equipped with its type.
Therefore it is possible in type theory that all elements have a *unique* type.
In general, it is therefore good practice to make sure that every element is given a unique name, and in formalized mathematics in computer proof assistants this is even required. 
For example, the element `0` has type `ℕ`, and it is not also a type of `ℤ`. 
This is why we annotate the terms `0` and `succ-ℕ` with their type in the subscript. 
The type `ℤ` of the integers will be introduced in the next section, which will come equipped with a zero element `0 : ℤ` and a successor function `succ-ℤ`.

## The induction principle of `ℕ`

The classical induction principle of the natural numbers tells us what we have to do in order to show that `∀(n ∈ ℕ) P(n)` holds, for a predicate `P` over `ℕ`.
Recall that a predicate `P` on a set `X` is just a proposition `P(x)` about an arbitrary `x ∈ X`.
For example, the assertion that "`n` is divisible by five" is a predicate on the natural numbers.

In dependent type theory we may think of a type family `P` over `ℕ` as a predicate over `ℕ`.
The type theoretical induction principle of `ℕ` is therefore formulated using a type family `P` over `ℕ`:

```text
   n : ℕ ⊢ P(n) type
   ⊢ p_0 : P(0)
   ⊢ p_S : Π(n : ℕ) P(n) → P(succ-ℕ(n))
  -----------------------------------------
       ⊢ ind-ℕ : Π(n : ℕ) P(n)
```

In other words, the type theoretical induction principle of `ℕ` tells us what we need to do in order to construct a dependent function `Π(n : ℕ) P(n)`.
Just as in the classical induction principle, there are two things to be constructed given a type family `P` over `ℕ`: in the **base case** we need to construct an element `p_0 : P(0)`, and for the **inductive step** we need to construct a function of type `P(n) → P(succ-ℕ(n))` for all `n : ℕ`.

### Remark 3.1.2

We might alternatively present the induction principle of `ℕ` as the following inference rule

```text
   Γ, n : ℕ ⊢ P(n) type
  ------------------------------------------------------------------ ℕ-ind
   ⊢ ind-ℕ : P(0) → (Π(n : ℕ) P(n) → P(succ-ℕ(n))) → Π(n : ℕ) P(n).
```

In other words, for any type family `P` over `ℕ` there is a *function* `ind-ℕ` that takes two arguments, one for the base case and one for the inductive step, and returns a section of `P`.
We claim that this rule is *interderivable* with the rule `ℕ-ind` above.
  
To see that indeed we get such a function from the rule `ℕ-ind`, we use generic elements.
First, we let `Γ'` be the context

```text
  Γ, p_0 : P(0), p_S : Π(n : ℕ) P(n)→ P(succ-ℕ(n)).
```

By weakening we obtain that

```text
  Γ', n : ℕ ⊢ P(n) type
       Γ' ⊢ p_0 : P(0)
       Γ' ⊢ p_S : Π(n : ℕ) P(n) → P(succ-ℕ(n)).
```

Therefore, the induction principle of `ℕ` provides us with a dependent function

```text
  Γ' ⊢ ind-ℕ(p_0,p_S) : Π(n : ℕ) P(n).
```

Now we proceed by `λ`-abstraction twice to obtain a function

```text
  ind-ℕ : P(0) → ((Π(n : ℕ) P(n) → P(succ-ℕ(n))) → Π(n : ℕ) P(n))
```

in the original context `Γ`.

This shows that we can define the function `ind-ℕ` from the rule `ℕ-ind`.
Conversely, we can derive the rule `ℕ-ind` from the rule that presents `ind-ℕ` as a function.
We conclude that the "official" rule `ℕ-ind` and the rule that presents `ind-ℕ` as a function are indeed interderivable.

```agda
ind-ℕ :
  {l : Level} {P : ℕ → Type l} →
  P 0 → ((n : ℕ) → P n → P (succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p-zero p-succ 0 = p-zero
ind-ℕ p-zero p-succ (succ-ℕ n) = p-succ n (ind-ℕ p-zero p-succ n)

rec-ℕ : {l : Level} {A : Type l} → A → (ℕ → A → A) → (ℕ → A)
rec-ℕ = ind-ℕ
```

## The computation rules of `ℕ`

The computation rules for `ℕ` postulate that the dependent function

```text
  ind-ℕ(p_0,p_S) : Π(n : ℕ) P(n)
```

behaves as expected when it is applied to `0` or a successor.
There is one computation rule for each step in the induction principle, covering the base case and the inductive step.

The computation rule for the base case is

```text
   Γ, n : ℕ ⊢ P(n) type
   Γ ⊢ p_0 : P(0)
   Γ ⊢ p_S : Π(n : ℕ) P(n) → P(succ-ℕ(n))
  ----------------------------------------
   Γ ⊢ ind-ℕ(p_0,p_S,0) ≐ p_0 : P(0).
```

The computation rule for the inductive step has the same premises as the computation rule for the base case:

```text
   Γ, n : ℕ ⊢ P(n) type
   Γ ⊢ p_0 : P(0)
   Γ ⊢ p_S : Π(n : ℕ) P(n) → P(succ-ℕ(n))
  ------------------------------------------------------------------------------
   Γ, n : ℕ ⊢  ind-ℕ(p_0,p_S,succ-ℕ(n)) ≐ p_S(n,ind-ℕ(p_0,p_S,n)) : P(succ-ℕ(n)).
```

This completes the formal specification of the type `ℕ` of natural numbers.
