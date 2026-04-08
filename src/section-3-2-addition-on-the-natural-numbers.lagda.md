# 3.2 Addition on the natural numbers

```agda
module section-3-2-addition-on-the-natural-numbers where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
```

The type theoretic induction principle of `ℕ` can be used to do all the usual constructions of operations on `ℕ`, and to derive all the familiar properties about natural numbers.
Many of those properties, however, require a few more ingredients of Martin-Löf's dependent type theory.
For example, the traditional inductive proof that the triangular numbers can be calculated by

```text
  1 + ⋯ + n = n(n + 1)/2
```

is analogous in type theory, but it requires the identity type to state this equation.
We will introduce the identity type in Chapter 5.
Until we have fully specified all the ways of forming types in Martin-Löf's dependent type theory, we are a bit limited in what we can do with the natural numbers, but at the present stage we can define some of the familiar operations on `ℕ`.
We give in this section the type theoretical construction the **addition operation** by induction on `ℕ`, along with the complete derivation tree.

### Definition 3.2.1

We define a function

```text
  add-ℕ : ℕ → (ℕ → ℕ)
```

satisfying the specification

```text
        add-ℕ(m,0) ≐ m,
  add-ℕ(m,succ-ℕ(n)) ≐ succ-ℕ(add-ℕ(m,n)).
```

Usually we will write `m + n` for `add-ℕ(m,n)`.

### Construction

We will construct the binary operation `add-ℕ : ℕ → (ℕ → ℕ)` by induction on the second variable.
In other words, we will construct an element

```text
  m : ℕ ⊢ add-ℕ(m) : ℕ → ℕ.
```

The context `Γ` we work in is therefore `m : ℕ`.
The induction principle of `ℕ` is used with the family of types `P(n) ≔ ℕ` indexed by `n : ℕ` in context `m : ℕ`.
Therefore, we need to construct

```text
  m : ℕ ⊢ add-0 (m) : ℕ,
  m : ℕ ⊢ add-S (m) : ℕ → (ℕ → ℕ),
```

in order to obtain

```text
  m : ℕ ⊢ add-ℕ(m) ≔ ind-ℕ(add-0(m),add-S(m)) : ℕ → ℕ.
```

The element `add-0(m) : ℕ` in context `m : ℕ` is of course defined to be `m : ℕ`, i.e., by the generic element, because adding zero should just be the identity function.
To see how the function `add-S(m) : ℕ → (ℕ → ℕ)` should be defined, we look at the specification of `add-ℕ(m)` when it is applied to a successor:

```text
  add-ℕ(m,succ-ℕ(n)) ≐ succ-ℕ(add-ℕ(m,n)).
```

This shows us that we should define

```text
  add-S(m,n,x) ≐ succ-ℕ(x),
```

because with this definition we will have

```text
  add-ℕ(m,succ-ℕ(n)) ≐ ind-ℕ(add-0(m),add-S(m),succ-ℕ(n))
                     ≐ add-S(m,n,add-ℕ(m,n))
                     ≐ succ-ℕ(add-ℕ(m,n)).
```

The formal derivation for the construction of `add-S` is as follows:

```text
                   ------------------
                    ⊢ succ-ℕ : ℕ → ℕ
    ----------  ------------------------
     ⊢ ℕ type    n : ℕ ⊢ succ-ℕ : ℕ → ℕ
    ------------------------------------
       m : ℕ, n : ℕ ⊢ succ-ℕ : ℕ → ℕ
      -------------------------------
         λ n. succ-ℕ : ℕ → (ℕ → ℕ)
  ---------------------------------------
   add-S(m) ≔ λ n. succ-ℕ : ℕ → (ℕ → ℕ).
```

We combine this derivation with the induction principle of `ℕ` to complete the construction of addition:

```text
               ⋮                               ⋮
  --------------------------  --------------------------------
   m : ℕ ⊢ add-0(m) ≔ m : ℕ    m : ℕ ⊢ add-S(m) : ℕ → (ℕ → ℕ)
  ------------------------------------------------------------
      m : ℕ ⊢ ind-ℕ(add-0(m),add-S(m)) : ℕ → ℕ
    -----------------------------------------------------
     m : ℕ ⊢ add-ℕ(m) ≔ ind-ℕ(add-0(m),add-S(m)) : ℕ → ℕ
```

The asserted judgmental equalities then hold by the computation rules for `ℕ`.  □

```agda
add-ℕ : ℕ → ℕ → ℕ
add-ℕ x 0 = x
add-ℕ x (succ-ℕ y) = succ-ℕ (add-ℕ x y)

infixl 35 _+ℕ_
_+ℕ_ = add-ℕ

{-# BUILTIN NATPLUS _+ℕ_ #-}

add-ℕ' : ℕ → ℕ → ℕ
add-ℕ' m n = add-ℕ n m
```

### Remark 3.2.2

By the computation rules for `ℕ` it follows that

```text
  m + 0 ≐ m,    and     m + succ-ℕ(n) ≐ succ-ℕ(m + n).
```

A simple consequence of this definition is that `succ-ℕ(n) ≐ n + 1`, as one would expect.
However, the rules that we provided so far are not sufficient to also conclude that `0 + n ≐ n` and `succ-ℕ(m) + n ≐ succ-ℕ(m + n)`.
In fact, dependent type theory with its inductive types does not provide any means to prove such judgmental equalities.

Nevertheless, once we have introduced the *identity type* in Chapter 5 we will be able to *identify* `0 + n` with `n`, and `succ-ℕ(m) + n` with `succ-ℕ(m + n)`.
See Propositions 5.6.1 and 5.6.2.
