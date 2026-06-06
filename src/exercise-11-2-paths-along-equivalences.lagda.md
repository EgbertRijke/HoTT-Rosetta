# Exercise 11.2 Paths along equivalences

```agda
module exercise-11-2-paths-along-equivalences where
```

## Problem statement

Consider an equivalence `e : A ≃ B`.
Construct an equivalence

```text
  p ↦ p~ : (e(x) = y) ≃ (x = e⁻¹(y))
```

for every `x : A` and `y : B`, such that the triangle

```text
  e(x) --ap e p~--> e(e⁻¹(y))
    \                   |
     \ p                | G(y)
      \                 v
                  y
```

commutes for every `p : e(x) = y`.
In this diagram, the homotopy `G : e ∘ e⁻¹ ~ id` is the homotopy witnessing that
`e⁻¹` is a section of `e`.

## Solution
