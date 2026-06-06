# Exercise 11.9 Embeddings from path sections

```agda
module exercise-11-9-embedding-from-path-sections where
```

## Problem statement

Use Exercise 11.8 to show that for any map `f : A → B`, if

```text
  ap_f : (x = y) → (f(x) = f(y))
```

has a section for each `x, y : A`, then `f` is an embedding.

## Solution
