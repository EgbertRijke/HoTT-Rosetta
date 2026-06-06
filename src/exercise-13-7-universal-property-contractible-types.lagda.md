# Exercise 13.7 Universal property contractible types

```agda
module exercise-13-7-universal-property-contractible-types where
```

## Problem statement

Consider a type `A`.
Show that the following are equivalent:

1. The type `A` is contractible.
2. The type `A` comes equipped with a point `a : A`, and the map

```text
  (Π(x : A) P(x)) → P(a)
```

given by `f ↦ f(a)` is an equivalence for any type family `P` over `A`.
This property is the **dependent universal property of a contractible type**.

3. The type `A` comes equipped with a point `a : A`, and the map

```text
  (A → X) → X
```

given by `f ↦ f(a)` is an equivalence for any type `X`.
This property is the **universal property of a contractible type**.

4. The type `A` comes equipped with a point `a : A`, and the map

```text
  (A → A) → A
```

given by `f ↦ f(a)` is an equivalence.

5. The map

```text
  X → (A → X)
```

given by `x ↦ λ y → x` is an equivalence for any type `X`.

6. The map

```text
  A → (A → A)
```

given by `x ↦ λ y → x` is an equivalence.

## Solution
