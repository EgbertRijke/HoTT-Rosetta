# Exercise 18.4

```agda
module exercise-18-4-exercise where

```

## Problem statement

A **`Σ`-decomposition** of a type `A` consists of a type `X` (the **indexing type** of the `Σ`-decomposition) equipped with a family `Y` of inhabited types indexed by `X` and an equivalence
```text
e:A≃ Σ(x:X) Y(x).
```
In other words, the type of all `Σ`-decompositions of `A` is defined by
```text
\Sigmadecomposition_𝒰(A) ≔ Σ(X:𝒰) Σ(Y:X→Σ(Z:𝒰) ‖Z‖) A≃Σ(x:X) Y(x).
```

Construct an equivalence
```text
\Sigmadecomposition_𝒰(A)≃ Σ(X:𝒰) A↠ X.
```

A `Σ`-decomposition is said to be **set-indexed** if its indexing type is a set.
We will write `\Sigmadecomposition_{Set_𝒰}(A)` for the type of all set-indexed `Σ`-decompositions of `A` in `𝒰`.
Construct an equivalence
```text
Eq-Rel_𝒰(A)≃ \Sigmadecomposition_{Set_𝒰}(A).
```

## Solution

No formalization has been curated yet.
