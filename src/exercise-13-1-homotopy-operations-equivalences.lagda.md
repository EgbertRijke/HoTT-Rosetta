# Exercise 13.1 Homotopy operations equivalences

```agda
module exercise-13-1-homotopy-operations-equivalences where
```

## Problem statement

Show that the functions

```text
  inv-htpy       : (f ~ g) → (g ~ f)
  concat-htpy(H) : (g ~ h) → (f ~ h)
  concat-htpy'(K): (f ~ g) → (f ~ h)
```

are equivalences for every `f g h : Π(x : A) B(x)`.
Here, `concat-htpy'(K)` is the function defined by `H ↦ concat(H, K)`.

## Solution
