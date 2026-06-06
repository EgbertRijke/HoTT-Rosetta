# Exercise 17.5 Surjective precomposition

```agda
module exercise-17-5-surjective-precomposition where
```

## Problem statement

Consider a map `f : A → B`.
Show that the following are equivalent:

1. The map `f` is surjective.
2. For every set `C`, the precomposition function

```text
  _ ∘ f : (B → C) → (A → C)
```

is an embedding.

Hint: To show that (ii) implies (i), use the assumption with the set
`C := Prop_𝒰`, where `𝒰` is a univalent universe containing both `A` and `B`.

## Solution
