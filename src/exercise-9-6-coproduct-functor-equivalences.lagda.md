# Exercise 9.6 Coproduct functor equivalences

```agda
module exercise-9-6-coproduct-functor-equivalences where
```

## Problem statement

Recall that coproducts have a **functorial action**, i.e., that for every
`f : A → A'` and every `g : B → B'` we have a map

```text
  f + g : (A + B) → (A' + B').
```

Show that `id_A + id_B ~ id_(A + B)`.

## Solution

## Problem statement

Show that for any two pairs of composable functions

```text
  A → A' → A''
  B → B' → B''
```

there is a homotopy

```text
  (f' ∘ f) + (g' ∘ g) ~ (f' + g') ∘ (f + g).
```

## Solution

## Problem statement

Show that if `H : f ~ f'` and `K : g ~ g'`, then there is a homotopy

```text
  H + K : (f + g) ~ (f' + g').
```

## Solution

## Problem statement

Show that if both `f` and `g` are equivalences, then so is `f + g`.

## Solution
