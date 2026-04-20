# Section 4.2 The unit type

```agda
module section-4-2-the-unit-type where

open import universe-levels
```

A straightforward example of an inductive type is the *unit type*, which has just one constructor. 
Its induction principle is analogous to just the base case of induction on the natural numbers.

## Definition 4.2.1

We define the **unit type** to be a type `𝟙` equipped with a term

```text
  ⋆ : 𝟙,
```

satisfying the induction principle that for any family of types `P(x)` indexed by `x : 𝟙`, there is a function

```text
  ind_𝟙 : P(⋆) → Π(x : 𝟙) P(x)
```

for which the computation rule

```text
  ind_𝟙(p,⋆) ≐ p
```

holds.

```agda
record unit : Type lzero where
  instance constructor star

{-# BUILTIN UNIT unit #-}

ind-unit : {l : Level} {P : unit → Type l} → P star → (x : unit) → P x
ind-unit p star = p
```

Alternatively, a definition of a dependent function `f : Π{x : 𝟙} P(x)` by induction using `p : P(⋆)` can be presented by pattern matching as

```text
  f(⋆) ≔ p.
```

A special case of the induction principle arises when `P` does not actually depend on `𝟙`.
If we are given a type `A`, then we can first weaken it to obtain the constant family over `𝟙`, with value `A`.
Then the induction principle of the unit type provides a function

```text
  ind_𝟙 : A → (𝟙 → A).
```

In other words, by the induction principle for the unit type we obtain for every `x : A` a function `pt_x ≔ ind_𝟙(x) : 𝟙 → A`.

```agda
module _
  {l : Level} {A : UU l}
  where

  point : A → (unit → A)
  point = diagonal-exponential A unit
```
