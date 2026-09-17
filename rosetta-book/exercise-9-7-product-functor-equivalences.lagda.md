# Exercise 9.7

```agda
module exercise-9-7-product-functor-equivalences where

```

## Problem statement

<div class="subexenum">

Construct for any two maps `f:A → A'` and `g:B→ B'`, a map
```text
f× g : A× B → A'× B'
```

Show that `id[A]×id[B]~id[A× B]`.

Show that for any two pairs of composable functions

```text
 [A] --f--> [A']--{f'}-->[A'']
```

there is a homotopy `(f'∘ f)×(g'∘ g) ~ (f'× g')∘ (f× g)`.

Show that if `H:f~ f'` and `K:g~ g'`, then there is a homotopy
```text
H× K:(f× g)~ (f'× g').
```

Show that for any two maps `f:A→ A'` and `g:B→ B'`, the following are equivalent:

1. The map `f× g` is an equivalence.

2. There are functions
```text
α : B → is-equiv(f)
β : A → is-equiv(g).
```

</div>

## Solution

No formalization has been curated yet.
