# Exercise 19.17

```agda
module exercise-19-17-exercise where

```

## Problem statement

(Buchholtz) Consider a group `G` with classifying type `BG` equipped with a group isomorphism

```text
φ : G ≅ Ω(BG).
```

Define the `G`-type `Concrete-Subgroup_𝒰(G) : BG → Set_𝒰` of **concrete subgroups** of `G` by

```text
Concrete-Subgroup_𝒰(G,u) ≔ Σ(X : BG → Set_𝒰) Σ(x : X(u)) is-conn(X/G).
```

### Exercise 19.17(a)

Construct an equivalence

```text
Concrete-Subgroup_𝒰(G,⋆) ≃ Subgroup_𝒰(G).
```

### Exercise 19.17(b)

Show that `G` acts on `Concrete-Subgroup_𝒰(G,⋆)` by conjugation, i.e., show that for any `g : G` we have a commuting square

```text
    [Concrete-Subgroup_𝒰(G,⋆)] ---- g ----> [Concrete-Subgroup_𝒰(G,⋆)]
                 |                                  |
              ≃  |                                  | ≃
                 V                                  V
         [Subgroup_𝒰(G)] --H↦{ghg⁻¹ | h ∈ H}--> [Subgroup_𝒰(G)]
```

### Exercise 19.17(c)

Conclude that the type of normal subgroups of a group `G` is equivalent to the type of **concrete normal subgroups**

```text
Π(u : BG) Concrete-Subgroup_𝒰(G,u).
```

### Exercise 19.17(d)

Show that the type of normal subgroups of a group `G` is also equivalent to the type

```text
Σ(BH : Concrete-Group_𝒰) Σ(f : BG →_⋆ BH) is-conn(f)
```

## Solution

BENCHMARK PROBLEM
