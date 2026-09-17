# Exercise 19.17

```agda
module exercise-19-17-exercise where

```

## Problem statement

(Buchholtz) Consider a group `G` with classifying type `BG` equipped with a group isomorphism
```text
φ:G≅ Ω(BG).
```
Define the `G`-type `Concrete-Subgroup_𝒰(G) : BG→𝒰` of **concrete subgroups** of `G` by
```text
Concrete-Subgroup_𝒰(G,u)≔ \sum_{(X:BG→Set_𝒰)}\sum_{(x:X(u))}is-conn(X/G).
```

Construct an equivalence
```text
Concrete-Subgroup_𝒰(G,⋆)≃Subgroup_𝒰(G).
```

Show that `G` acts on `Concrete-Subgroup_𝒰(G,⋆)` by conjugation, i.e., show that for any `g:G` we have a commuting square

*Square-shaped diagram (automatic draft).*

```text
[Concrete-Subgroup_𝒰(G,⋆)]---->[Concrete-Subgroup_𝒰(G,⋆)]
            |                              |
     [Subgroup_𝒰(G)]      ---->     [Subgroup_𝒰(G)]

Arrows:
- Concrete-Subgroup_𝒰(G,⋆) --g--> Concrete-Subgroup_𝒰(G,⋆)
- Concrete-Subgroup_𝒰(G,⋆) --≃--> Subgroup_𝒰(G)
- Concrete-Subgroup_𝒰(G,⋆) --≃--> Subgroup_𝒰(G)
- Subgroup_𝒰(G) --H↦{ghg^{-1}| h∈ H}--> Subgroup_𝒰(G)
```

Conclude that the type of normal subgroups of a group `G` is equivalent to the type of **concrete normal subgroups**
```text
Π(u:BG) Concrete-Subgroup_𝒰(G,u).
```

Show that the type of normal subgroups of a group `G` is also equivalent to the type
```text
Σ(BH:Concrete-Group_𝒰) Σ(f:BG→_⋆ BH) is-conn(f)
```

## Solution

No formalization has been curated yet.
