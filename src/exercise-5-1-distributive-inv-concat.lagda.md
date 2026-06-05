# Exercise 5.1 Distributivity of inverse over concatenation

```agda
module exercise-5-1-distributive-inv-concat where
```

## Problem statement

Show that the operation inverting identifications distributes over the
concatenation operation, i.e., construct an identification

```text
  distributive-inv-concat(p,q) : (p ∙ q)⁻¹ = q⁻¹ ∙ p⁻¹.
```

for any `p : x = y` and `q : y = z`.


## Solution
