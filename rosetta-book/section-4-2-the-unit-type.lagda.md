# Section 4.2 The unit type

```agda
module section-4-2-the-unit-type where

open import universe-levels
```

<!-- rosetta-item: section-4.2 -->

A straightforward example of an inductive type is the *unit type*, which has just one constructor.
Its induction principle is analogous to just the base case of induction on the natural numbers.

## Definition 4.2.1

<!-- rosetta-item: definition-4.2.1 -->

We define the **unit type** to be a type `unit` equipped with a term
```text
⋆:unit,
```
satisfying the induction principle that for any family of types `P(x)` indexed by `x:unit`, there is a function
```text
ind-unit : P(⋆)→Π(x:unit) P(x)
```
for which the computation rule
```text
ind-unit(p,⋆) ≐ p
```
holds.
Alternatively, a definition of a dependent function `f:Π(x:unit) P(x)` by induction using `p:P(⋆)` can be presented by pattern matching as
```text
f(⋆)≔ p.
```

<!-- rosetta-agda-block: section-4-2-the-unit-type-block-35 -->

```agda
record unit : Type lzero where
  instance constructor star

{-# BUILTIN UNIT unit #-}

ind-unit : {l : Level} {P : unit → Type l} → P star → (x : unit) → P x
ind-unit p star = p
```

<!-- rosetta-agda-block: section-4-2-the-unit-type-block-61 -->

```agda
module _
  {l : Level} {A : Type l}
  where

  point : A → (unit → A)
  point a x = a
```
<!-- rosetta-item-end: definition-4.2.1 -->

A special case of the induction principle arises when `P` does not actually depend on `unit`.
If we are given a type `A`, then we can first weaken it to obtain the constant family over `unit`, with value `A`.
Then the induction principle of the unit type provides a function
```text
ind-unit : A → (unit→ A).
```
In other words, by the induction principle for the unit type we obtain for every `x:A` a function `pt_x≔ind-unit(x):unit→ A`.
