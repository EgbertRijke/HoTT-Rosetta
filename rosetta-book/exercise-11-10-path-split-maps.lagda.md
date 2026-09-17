# Exercise 11.10

```agda
module exercise-11-10-path-split-maps where

```

## Problem statement

(Shulman) We say that a map `f:A→ B` is **path-split** if `f` has a section, and for each `x,y:A` the map
```text
ap{f}(x,y):(x=y)→ (f(x)=f(y))
```
also has a section.
We write `is-path-split(f)` for the type
```text
sec(f)×Π(x,y:A) sec(ap{f}(x,y)).
```
Show that for any map `f:A→ B` the following are equivalent:

1. The map `f` is an equivalence.

2. The map `f` is path-split.

## Solution

No formalization has been curated yet.
