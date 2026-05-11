# Exercise 3.2 Boolean operations

```agda
module exercise-4-2-boolean-operations where

open import universe-levels
```

## Problem statement

The type of **booleans** is defined to be an inductive type `bool` that comes equipped with

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

Construct the **boolean negation function** `neg-bool : bool → bool`.

## Solution

Before we can solve the exercise, we must implement the definition of the type `bool` with its induction principle.

```agda
data bool : Type lzero where
  true false : bool

ind-bool : {l : Level} {P : bool → Type l} → P true → P false → (b : bool) → P b
ind-bool pt pf true = pt
ind-bool pt pf false = pf
```

We can now define the boolean negation function.

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true
```

## Problem Statement

Construct the **boolean conjunction** operation `- ∧ -: bool → (bool → bool)`.

## Solution

```agda
_∧_ : bool → bool → bool
true ∧ q = q
false ∧ q = false
```

## Problem Statement

Construct the **boolean disjunction** operation `- ∨ - : bool → (bool → bool)`.

## Solution

```agda
_∨_ : bool → bool → bool
true ∨ q = true
false ∨ q = q
```

## Agda-unimath sources

- The definitions of the type of booleans, boolean negation, conjunction, and disjunction are implemented in `foundation-core.booleans`.
