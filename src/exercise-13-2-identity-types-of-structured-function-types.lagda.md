# Exercise 13.2 Identity types of structured function types

```agda
module exercise-13-2-identity-types-of-structured-function-types where
```

## Problem statement

Characterize the identity type of the type

```text
  Σ(h : A → B) h(a) = b
```

of **pointed maps**, where `a : A` and `b : B` are given.

## Solution

## Problem statement

Characterize the identity type of the type

```text
  Σ(h : A → B) f ~ g ∘ h
```

of commuting triangles

```text
      h
  A ----> B
   \    /
  f \  / g
     X,
```

where `f : A → X` and `g : B → X` are given.

## Solution

## Problem statement

Characterize the identity type of the type

```text
  Σ(h : X → Y) h ∘ f ~ g
```

of commuting triangles

```text
    A
   / \
 f/   \g
 X --> Y,
   h
```

where `f : A → X` and `g : A → Y` are given.

## Solution

## Problem statement

Characterize the identity type of the type

```text
  Σ(i : A → X) Σ(j : B → Y) j ∘ f ~ g ∘ i
```

of commuting squares

```text
  A --i--> X
  |       |
  f       g
  |       |
  v       v
  B --j--> Y,
```

where `f : A → B` and `g : X → Y` are given.

## Solution
