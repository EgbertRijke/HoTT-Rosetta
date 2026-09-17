# Exercise 13.13

```agda
module exercise-13-13-pi-types-distribute-over-coproducts where

```

## Problem statement

Show that *`Π`-types distribute over coproducts*, i.e., construct for any type `X` and any two families `A` and `B` over `X` an equivalence from the type `Π(x:X) A(x)+B(x)` to the type
```text
Σ(f:X→Fin{2}) (Π(x:X) A(x)^{f(x)=0})×(Π(x:X) B(x)^{f(x)=1}).
```

## Solution

No formalization has been curated yet.
