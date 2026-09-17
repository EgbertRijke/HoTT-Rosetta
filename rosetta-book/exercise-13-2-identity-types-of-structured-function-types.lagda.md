# Exercise 13.2

```agda
module exercise-13-2-identity-types-of-structured-function-types where

```

## Problem statement

Characterize the identity types of the following types:

The type `Σ(h:A→ B) h(a)=b` of **pointed maps**, where `a:A` and `b:B` are given.

The type `Σ(h:A→ B) f~ g∘ h` of commuting triangles

```text
 [A]                 [B]

           [X]

Arrows:
- A --h--> B
- A --f--> X
- B --g--> X
```
where `f:A→ X` and `g:B→ X` are given.

The type `Σ(h:X→ Y) h∘ f~ g` of commuting triangles

```text
           [A]

 [X]                 [Y]

Arrows:
- A --f--> X
- A --g--> Y
- X --h--> Y
```
where `f:A→ X` and `g:A→ Y` are given.

The type `Σ(i:A→ X) Σ(j:B→ Y) j∘ f~ g∘ i` of commuting squares

```text
 [A] ----> [X]
  |         |
 [B] ----> [Y]

Arrows:
- A --f--> B
- A --i--> X
- X --g--> Y
- B --j--> Y
```
where `f:A→ B` and `g:X→ Y` are given.

## Solution

No formalization has been curated yet.
