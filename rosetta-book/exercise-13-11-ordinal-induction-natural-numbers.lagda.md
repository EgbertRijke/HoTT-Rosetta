# Exercise 13.11

```agda
module exercise-13-11-ordinal-induction-natural-numbers where

```

## Problem statement

Show that `ℕ` satisfies **ordinal induction**, i.e., construct for any type family `P` over `ℕ` a function `ord-ind` of type
```text
(Π(k:ℕ) (Π(m:ℕ) (m< k) → P(m))→ P(k)) → Π(n:ℕ) P(n).
```
Moreover, prove that
```text
ord-ind(h,n)=h(n,λ m. λ p. ord-ind(h,m))
```
for any `n:ℕ` and any `h:Π(k:ℕ) (Π(m:ℕ) (m<k)→ P(m))→ P(k)`.

## Solution

No formalization has been curated yet.
