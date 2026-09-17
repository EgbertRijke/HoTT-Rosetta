# Exercise 18.7

```agda
module exercise-18-7-exercise where

```

## Problem statement

Consider a map `f:A→ B`.

<div class="subexenum">

Show that the type of maps `‖f‖_0:‖A‖_0→‖B‖_0` equipped with a homotopy witnessing that the square
<!-- rosetta-diagram: 4430fe3fab53; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
  [A]  ---->  [B]
   |           |
[‖A‖_0]---->[‖B‖_0]

Arrows:
- A --f--> B
- A --η--> ‖A‖_0
- B --η--> ‖B‖_0
- ‖A‖_0 --‖f‖_0--> ‖B‖_0
```
commutes is contractible.

Show that if `f` is injective, then `‖f‖_0:‖A‖_0→‖B‖_0` is injective.

Show that the following are equivalent

1. The map `f` is surjective.

2. the map `‖f‖_0:‖A‖_0→‖B‖_0` is surjective.

Construct a map `h:im(f)→im‖f‖_0` such that the squares
<!-- rosetta-diagram: 48b2b46a6132; review: pending -->

*Diagram of two squares pasted horizontally (automatic draft).*

```text
  [A]  ----> [im(f)] ---->  [B]
   |            |            |
[‖A‖_0]---->[im‖f‖_0]---->[‖B‖_0]

Arrows:
- A --q_f--> im(f)
- A --η--> ‖A‖_0
- im(f) --h--> im‖f‖_0
- im(f) --i_f--> B
- B --η--> ‖B‖_0
- ‖A‖_0 --q_{‖f‖_0}--> im‖f‖_0
- im‖f‖_0 --i_{‖f‖_0}--> ‖B‖_0
```
commute, and show that `h` is a set truncation of `im(f)`.

</div>

## Solution

<!-- rosetta-item: exercise-18-7 -->

No formalization has been curated yet.
