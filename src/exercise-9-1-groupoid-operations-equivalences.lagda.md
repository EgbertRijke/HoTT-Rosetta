# Exercise 9.1 Groupoid operations are equivalences

```agda
module exercise-9-1-groupoid-operations-equivalences where
```

## Problem statement

Show that the functions

```text
  inv        : (x = y) → (y = x)
  concat(p) : (y = z) → (x = z)
  concat'(q): (x = y) → (x = z)
  tr_B(p)   : B(x) → B(y)
```

are equivalences, where `concat'(q, p) := p ∙ q`.
Give their inverses explicitly.

## Solution
