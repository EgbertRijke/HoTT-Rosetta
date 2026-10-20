# Exercise 13.2

```agda
module exercise-13-2-identity-types-of-structured-function-types where

```

## Problem statement

Characterize the identity types of the following types:

### Exercise 13.2(a)

The type `Σ(h : A → B) h(a) = b` of **pointed maps**, where `a : A` and `b : B` are given.

### Exercise 13.2(b)

The type `Σ(h : A → B) f ~ g ∘ h` of commuting triangles

```text
       h
  A ------> B
   \       /
  f \     / g
     \   /
      ∨ ∨
       X
```
where `f : A → X` and `g : B → X` are given.

### Exercise 13.2(c)

The type `Σ(h : X → Y) h ∘ f ~ g` of commuting triangles

```text
       A
      / \
   f /   \ g
    /     \
   ∨       ∨
  X ------> Y
       h
```
where `f : A → X` and `g : A → Y` are given.

### Exercise 13.2(d)

The type `Σ(i : A → X) Σ(j : B → Y) j ∘ f ~ g ∘ i` of commuting squares

```text
       i
  A ------> X
  |         |
f |         | g
  ∨         ∨
  B ------> Y
       j
```
where `f : A → B` and `g : X → Y` are given.

## Solution

BENCHMARK PROBLEM
