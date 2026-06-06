# Exercise 13.12 Dependent products of truncated maps

```agda
module exercise-13-12-dependent-products-of-truncated-maps where
```

## Problem statement

Consider a family of `k`-truncated maps `f_i : A_i → B_i` indexed by `i : I`.
Show that the map

```text
  λ h → λ i → f_i(h(i)) :
    (Π(i : I) A_i) → (Π(i : I) B_i)
```

is also `k`-truncated.

## Solution

## Problem statement

Consider an equivalence `e : I ≃ J`, and a family of equivalences
`f_i : A_i ≃ B_{e(i)}` indexed by `i : I`, where `A` is a family of types
indexed by `I` and `B` is a family of types indexed by `J`.
Show that the map

```text
  λ h → λ j → f_{e^{-1}(j)}(h(e^{-1}(j))) :
    (Π(i : I) A_i) → (Π(j : J) B_j)
```

is an equivalence.

## Solution

## Problem statement

Consider a family of maps `f_i : A_i → B_i` indexed by `i : I`.
Show that the following are equivalent:

1. Each `f_i` is `k`-truncated.
2. For every map `α : X → I`, the map

```text
  λ h → λ x → f_{α(x)}(h(x)) :
    (Π(x : X) A_{α(x)}) → (Π(x : X) B_{α(x)})
```

is `k`-truncated.

## Solution

## Problem statement

Show that for any map `f : A → B` the following are equivalent:

1. The map `f` is `k`-truncated.
2. For every type `X`, the postcomposition function

```text
  f ∘ _ : (X → A) → (X → B)
```

is `k`-truncated.

In particular, `f` is an equivalence if and only if `f ∘ _` is an equivalence,
and `f` is an embedding if and only if `f ∘ _` is an embedding.

## Solution
