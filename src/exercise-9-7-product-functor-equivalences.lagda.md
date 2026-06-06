# Exercise 9.7 Product functor equivalences

```agda
module exercise-9-7-product-functor-equivalences where
```

## Problem statement

Construct for any two maps `f : A → A'` and `g : B → B'`, a map

```text
  f × g : A × B → A' × B'.
```

## Solution

## Problem statement

Show that `id_A × id_B ~ id_(A × B)`.

## Solution

## Problem statement

Show that for any two pairs of composable functions

```text
  A → A' → A''
  B → B' → B''
```

there is a homotopy

```text
  (f' ∘ f) × (g' ∘ g) ~ (f' × g') ∘ (f × g).
```

## Solution

## Problem statement

Show that if `H : f ~ f'` and `K : g ~ g'`, then there is a homotopy

```text
  H × K : (f × g) ~ (f' × g').
```

## Solution

## Problem statement

Show that for any two maps `f : A → A'` and `g : B → B'`, the following are
equivalent:

1. The map `f × g` is an equivalence.
2. There are functions

```text
  α : B → is-equiv(f)
  β : A → is-equiv(g).
```

## Solution
