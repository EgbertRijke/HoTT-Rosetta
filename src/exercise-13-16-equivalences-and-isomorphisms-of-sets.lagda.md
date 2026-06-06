# Exercise 13.16 Equivalences and isomorphisms of sets

```agda
module exercise-13-16-equivalences-and-isomorphisms-of-sets where
```

## Problem statement

Let `A` and `B` be sets.
Show that the type `A ≃ B` of equivalences from `A` to `B` is equivalent to the
type `A ≅ B` of **isomorphisms** from `A` to `B`, i.e., the type of quadruples
`(f, g, H, K)` consisting of

```text
  f : A → B
  g : B → A
  H : f ∘ g = id_B
  K : g ∘ f = id_A.
```

## Solution
