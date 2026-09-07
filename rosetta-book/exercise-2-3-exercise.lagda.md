# Exercise 2.3

```agda
module exercise-2-3-exercise where

```

## Problem statement

<div class="subexenum">

Construct the **constant map**

<!-- rosetta-proof-tree: 6295d3bacb13; review: pending -->

*Proof tree (automatic faithful draft).*

```text
 Γ⊢ A \textrm{type}
───────────────────
Γ,y:B⊢ const_y:A→ B
```

Show that

<!-- rosetta-proof-tree: b070ceed5cb4; review: pending -->

*Proof tree (automatic faithful draft).*

```text
           Γ⊢ f:A→ B
────────────────────────────────
Γ,z:C⊢ const_z∘ f≐const_z : A→ C
```

Show that

<!-- rosetta-proof-tree: 981ff7e743d1; review: pending -->

*Proof tree (automatic faithful draft).*

```text
   Γ⊢ A \textrm{type}   Γ⊢ g:B→ C
───────────────────────────────────
Γ,y:B⊢ g∘const_y≐ const_{g(y)}:A→ C
```

</div>

## Solution

<!-- rosetta-item: exercise-2-3 -->

No formalization has been curated yet.
