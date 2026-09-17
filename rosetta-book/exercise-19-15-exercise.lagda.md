# Exercise 19.15

```agda
module exercise-19-15-exercise where

```

## Problem statement

Consider a group `G` in a universe `𝒰` and a pointed connected `1`-type `B`.
In analogy with Theorem 18.2.3, show that the following are equivalent:

1. The pointed connected `1`-type `B` comes equipped with a group homomorphism
```text
φ:G → Ω(B)
```
    and for every pointed connected `1`-type `C` that comes equipped with a group homomorphism `ψ:G→ Ω(C)` there is a unique pointed map `f:B→_⋆ C` equipped with a homotopy witnessing that the triangle

*Triangle-shaped diagram (automatic draft).*

```text
            [G]

[Ω(B)]               [Ω(C)]

Arrows:
- G --φ--> Ω(B)
- G --ψ--> Ω(C)
- Ω(B) --Ω(f)--> Ω(C)
```
    commutes.

2. The pointed connected `1`-type `B` comes equipped with a group isomorphism
```text
φ:G≅ Ω(B).
```

3. There is an embedding `i:B↪ G-Set_𝒰` such that the triangle

*Triangle-shaped diagram (automatic draft).*

```text
[unit]                    [B]

           [G-Set_𝒰]

Arrows:
- unit --unlabeled--> B
- unit --Pr_G--> G-Set_𝒰
- B --i--> G-Set_𝒰
```
    commutes, where `Pr_G` is the **principal `G`-set**, i.e., `G` acting on itself from the left.

## Solution

No formalization has been curated yet.
