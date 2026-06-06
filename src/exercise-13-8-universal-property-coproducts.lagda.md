# Exercise 13.8 Universal property coproducts

```agda
module exercise-13-8-universal-property-coproducts where
```

## Problem statement

Consider two types `A` and `B`.
Show that the map

```text
  (Π(z : A + B) P(z)) →
  (Π(x : A) P(inl(x))) × (Π(y : B) P(inr(y)))
```

given by `f ↦ (f ∘ inl, f ∘ inr)` is an equivalence for any type family `P`
over `A + B`.
This property is the **dependent universal property of the coproduct of `A` and
`B`**.
Conclude that the map

```text
  (A + B → X) → (A → X) × (B → X)
```

given by `f ↦ (f ∘ inl, f ∘ inr)` is an equivalence for any type `X`.
This latter property is the **universal property of the coproduct of `A` and
`B`**.

## Solution
