# Exercise 4.2 Boolean operations

```agda
module exercise-4-2-boolean-operations where

open import universe-levels renaming (UU to Type)
```

## Problem statement

The type of **booleans** is an inductive type `bool` that comes equipped with

```text
    false : bool
```

and

```text
    true : bool
```

The induction principle of the booleans asserts that for any family of types `P(x)` indexed by `x : bool`, there is a term

```text
    ind-bool : P(false) → (P(true) → Π(x : bool) P(x))
```

for which the computation rules

```text
    ind-bool(p₀, p₁, false) ≐ p₀
     ind-bool(p₀, p₁, true) ≐ p₁
```

hold.

```agda
data bool : Type lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

ind-bool : {l : Level} (P : bool → Type l) → P true → P false → (b : bool) → P b
ind-bool P pt pf true = pt
ind-bool P pt pf false = pf

rec-bool : {l : Level} {P : Type l} → P → P → bool → P
rec-bool {l} {P} p1 p0 = ind-bool (λ _ → P) p1 p0
```

### Exercise 4.2(a)

Construct the **boolean negation function** `neg-bool : bool → bool`.

### Exercise 4.2(b)

Construct the **boolean conjunction** operation `and-bool : bool → (bool → bool)`.

### Exercise 4.2(c)

Construct the **boolean disjunction** operation `or-bool : bool → (bool → bool)`.

## Solutions

### Exercise 4.2(a)

We can now define the boolean negation function.

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true
```

## Exercise 4.2(b)

```agda
and-bool : bool → bool → bool
and-bool true q = q
and-bool false q = false
```

## Exercise 4.2(c)

```agda
or-bool : bool → bool → bool
or-bool true q = true
or-bool false q = q
```

## Agda-unimath sources

- The definitions of the type of booleans is implemented in `foundation-core.booleans`.
- The definitions of boolean negation, conjunction, and disjunction are implemented in `foundation.boolean-operations`.
