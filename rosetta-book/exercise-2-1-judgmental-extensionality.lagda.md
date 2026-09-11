# Exercise 2.1

```agda
module exercise-2-1-judgmental-extensionality where

```

## Problem statement

The `η`-rule is often seen as a judgmental extensionality principle.
Use the `η`-rule to show that if `f` and `g` take equal values, then they must be equal, i.e., give a derivation for the rule

<!-- rosetta-proof-tree: c74e5a088f5b; review: pending -->

```text
     Γ⊢ f:Π(x:A) B(x)

     Γ⊢ g:Π(x:A) B(x)

Γ,x:A⊢ f(x)≐ g(x):B(x)
──────────────────────
 Γ⊢ f≐ g:Π(x:A) B(x)
```

## Solution

<!-- rosetta-item: exercise-2-1 -->

This is intended as a pen-and-paper exercise. 
No formalization is expected.
