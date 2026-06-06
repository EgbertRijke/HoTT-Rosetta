# Exercise 11.6 Embeddings from coproducts

```agda
module exercise-11-6-embeddings-from-coproducts where
```

## Problem statement

Consider two maps `f : A → C` and `g : B → C`.
Use Exercise 11.1 to show that the following are equivalent:

1. The map `[f, g] : A + B → C` is an embedding.
2. Both `f` and `g` are embeddings, and

```text
  f(a) ≠ g(b)
```

for all `a : A` and `b : B`.

## Solution
