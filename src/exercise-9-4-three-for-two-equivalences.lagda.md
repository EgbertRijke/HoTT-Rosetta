# Exercise 9.4 Three-for-two property for equivalences

```agda
module exercise-9-4-three-for-two-equivalences where
```

## Problem statement

Consider a commuting triangle

```text
      h
  A ----> B
   \    /
  f \  / g
     X
```

with `H : f ~ g ∘ h`.
Suppose that the map `h` has a section `s : B → A`.
Show that the triangle

```text
      s
  B ----> A
   \    /
  g \  / f
     X
```

commutes, and that `f` has a section if and only if `g` has a section.

## Solution

## Problem statement

Suppose that the map `g` has a retraction `r : X → B`.
Show that the triangle

```text
      f
  A ----> X
   \    /
  h \  / r
     B
```

commutes, and that `f` has a retraction if and only if `h` has a retraction.

## Solution

## Problem statement

Show the **3-for-2 property** for equivalences: if any two of the functions

```text
  f, g, h
```

are equivalences, then so is the third.
Conclude that any section and any retraction of an equivalence is again an
equivalence.

## Solution
