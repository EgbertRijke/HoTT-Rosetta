# Section 4.5 The type of integers

```agda
module section-4-5-the-type-of-integers where

open import universe-levels

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
```

The set of integers is usually defined as a quotient of the set `ℕ × ℕ`, by the equivalence relation

```text
  ((n , m) ~ (n' , m')) := (n + m' = n' + m).
```

We haven't introduced the identity type yet, in order to consider the type of identifications `n + m' = n' + m`, but more importantly there are no quotient types in Martin-Löf's dependent type theory.
We will only discuss quotient types in the section on set quotients after we have assumed the univalence axiom and propositional truncations, because we will use the univalence axiom and propositional truncations to define them and derive their basic properties.
Nevertheless, the type of integers is also definable in dependent type theory without set quotients, but we have to settle for a more pedestrian version of the integers that is defined using coproducts.

## Definition 4.5.1

We define the **integers** to be the type `ℤ := ℕ + (𝟙 + ℕ)`.
The type of integers comes equipped with inclusion functions of the positive and negative integers

```text
  in-pos-ℤ := inr ∘ inr : ℕ → ℤ
  in-neg-ℤ := inl       : ℕ → ℤ
```

and with the constants

```text
  -1_ℤ := in-neg-ℤ(0)
   0_ℤ := inr(inl(⋆))
   1_ℤ := in-pos-ℤ(0).
```

```agda
ℤ : Type lzero
ℤ = ℕ + (unit + ℕ)

{-# BUILTIN INTEGER ℤ #-}

in-neg-ℤ : ℕ → ℤ
in-neg-ℤ n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg-ℤ zero-ℕ

zero-ℤ : ℤ
zero-ℤ = inr (inl star)

in-pos-ℤ : ℕ → ℤ
in-pos-ℤ n = inr (inr n)

one-ℤ : ℤ
one-ℤ = in-pos-ℤ zero-ℕ
```

The definition of the integers as the coproduct `ℕ + (𝟙 + ℕ)` can be pictured as follows:

```text
        𝟙           ℕ
         \         /
          \       /
  ℕ        𝟙 + ℕ
   \       /
    \     /
      ℤ
```

### Remark 4.5.2

The type of integers is built entirely out of inductive types.
Therefore it is possible to derive an induction principle especially tailored for the type `ℤ`, which can be used to define the basic operations on `ℤ`, such as the successor map, addition and multiplication.
This induction principle asserts that for any type family `P` over `ℤ`, we can define a dependent function `f : Π(k : ℤ) P(k)` recursively by

```text
  f(-1_ℤ)                := p_-1
  f(in-neg-ℤ(succ-ℕ(n))) := p_-S(n , f(in-neg-ℤ(n)))
  f(0_ℤ)                 := p_0
  f(1_ℤ)                 := p_1
  f(in-pos-ℤ(succ-ℕ(n))) := p_S(n , f(in-pos-ℤ(n))),
```

where the types of `p_-1`, `p_-S`, `p_0`, `p_1`, and `p_S` are

```text
  p_-1 : P(-1_ℤ)
  p_-S : Π(n : ℕ) P(in-neg-ℤ(n)) → P(in-neg-ℤ(succ-ℕ(n)))
  p_0  : P(0_ℤ)
  p_1  : P(1_ℤ)
  p_S  : Π(n : ℕ) P(in-pos-ℤ(n)) → P(in-pos-ℤ(succ-ℕ(n))).
```

```agda
ind-ℤ :
  {l : Level} (P : ℤ → Type l) →
  P neg-one-ℤ →
  ((n : ℕ) → P (in-neg-ℤ n) → P (in-neg-ℤ (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ →
  ((n : ℕ) → P (in-pos-ℤ n) → P (in-pos-ℤ (succ-ℕ n))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr x)))
```

## Definition 4.5.3

We define the **successor function** on the integers `succ-ℤ : ℤ → ℤ` using the induction principle of Remark 4.5.2, taking

```text
  succ-ℤ(-1_ℤ)                := 0_ℤ
  succ-ℤ(in-neg-ℤ(succ-ℕ(n))) := in-neg-ℤ(n)
  succ-ℤ(0_ℤ)                 := 1_ℤ
  succ-ℤ(1_ℤ)                 := in-pos-ℤ(1_ℕ)
  succ-ℤ(in-pos-ℤ(succ-ℕ(n))) := in-pos-ℤ(succ-ℕ(succ-ℕ(n))).
```

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))
```
