# Exercise 19.16

```agda
module exercise-19-16-exercise where

```

## Problem statement

Consider a group `G` and a pointed connected `1`-type `B` equipped with a group isomorphism
```text
φ:G≅ Ω(B).
```

Show that the map
```text
ev_⋆:(B→Set_𝒰)→ Σ(X:Set_𝒰) hom(G,Aut(X))
```
sending concrete `G`-sets to abstract `G`-sets defined by
```text
ev_⋆(X)≔ (X(⋆),g↦ tr_X(φ(g)))
```
is an equivalence.
In the remainder of this exercise we will write `gx` for `tr_X(φ(g),x)`.

Show that the type `X_G≔Π(u:BG) X(u)` of concrete fixed points of `X` is equivalent to the type
```text
Σ(x:X(⋆)) gx=x
```
of **fixed points** of the abstract `G`-set `ev_⋆(X)`.

Show that the type `X/G` of orbits of `X` is connected if and only if the abstract `G`-set `ev_⋆(X)` is transitive in the sense that
```text
∀_{(x:X(⋆))}is-surj(g↦ gx)
```

Show that the type `X/G` of orbits of `X` is a set if and only if the abstract `G`-set `ev_⋆(X)` is free in the sense that
```text
∀_{(x:X(⋆))}is-inj(g↦ gx).
```

Show that the type of abstract `G`-torsors is equivalent to the type of families `X:B→Set_𝒰` with contractible total space.

## Solution

No formalization has been curated yet.
