# Exercise 16.11

```agda
module exercise-16-11-surjections-between-finite-types where

```

## Problem statement

Consider an arbitrary type `A` and a type `B` with decidable equality.
Construct an equivalence
```text
((A+unit)↠(B+unit))≃ (B+unit)×(A↠ B)+(A↠ B+unit).
```

Construct an equivalence `Fin{\numberofsurjectivemaps{m}{n}}≃(Fin{m}↠Fin{n})`, where `\numberofsurjectivemaps{m}{n}` is defined recursively by
```text
\numberofsurjectivemaps{0}{0} ≔ 1
\numberofsurjectivemaps{0}{n+1} ≔ 0
\numberofsurjectivemaps{m+1}{0} ≔ 0
\numberofsurjectivemaps{m+1}{n+1} ≔ (n+1)\numberofsurjectivemaps{m}{n}+\numberofsurjectivemaps{m}{n+1}.
```
Conclude that if `A` and `B` are finite with cardinality `m` and `n`, then the type `A↠ B` is finite with cardinality `\numberofsurjectivemaps{m}{n}`.
Note: the number `\numberofsurjectivemaps{m}{n}` is `n!Stirling(m, n)`, where `Stirling(m, n)` is the **Stirling number of the second kind** at `(m,n)`.

## Solution

No formalization has been curated yet.
