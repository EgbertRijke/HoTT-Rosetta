# Exercise 11.11

```agda
module exercise-11-11-fiber-triangles where

```

## Problem statement

Consider a triangle

```text
 [A]                 [B]

           [X]

Arrows:
- A --h--> B
- A --f--> X
- B --g--> X
```
with a homotopy `H:f~ g∘ h` witnessing that the triangle commutes.

<div class="subexenum">

Construct a family of maps
```text
fib-triangle(h,H):Π(x:X) fib(f, x)→fib(g, x),
```
for which the square

```text
[Σ(x:X) fib(f, x)]---->[Σ(x:X) fib(g, x)]
        |                      |
       [A]        ---->       [B]

Arrows:
- Σ(x:X) fib(f, x) --tot(fib-triangle(h,H))--> Σ(x:X) fib(g, x)
- Σ(x:X) fib(f, x) --unlabeled--> A
- Σ(x:X) fib(g, x) --unlabeled--> B
- A --h--> B
```
commutes, where the vertical maps are as constructed in Exercise 10.8.

Show that `h` is an equivalence if and only if `fib-triangle(h,H)` is a family of equivalences.

</div>

## Solution

No formalization has been curated yet.
