# Exercise 5.2 Inverse concatenation maps

```agda
module exercise-5-2-inverse-concatenation-maps where
```

## Problem statement

For any `p : x = y`, `q : y = z`, and `r : x = z`, construct maps

```text
  inv-con(p,q,r)  :  (p ∙ q = r) → (q = p⁻¹ ∙ r) \\
  con-inv(p,q,r)  :  (p ∙ q = r) → (p = r ∙ q⁻¹).
```


## Solution
