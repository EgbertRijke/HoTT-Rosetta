# Formal Statements Exercise 13.17

```agda
module formal-statements-exercise-13-17 where

open import universe-levels
open import section-8-1-decidability-and-decidable-equality
open import section-10-1-contractible-types
```

## Problem statement

Suppose that `A : I → 𝒰` is a type family over a set `I` with decidable equality.
Show that

```text
  (Π(i : I) is-contr(Aᵢ)) ↔ is-contr(Π(i : I) Aᵢ).
```

## Formal Statements

```agda
module _
  {l1 l2 : Level} {I : UU l1} (H : has-decidable-equality I) {A : I → UU l2}
  where

  is-contr-Π-is-contr-family-has-decidable-equality :
    ((i : I) → is-contr (A i)) → is-contr ((i : I) → A i)
  is-contr-Π-is-contr-family-has-decidable-equality = {!!}

  is-contr-family-is-contr-Π-has-decidable-equality :
    is-contr ((i : I) → A i) → ((i : I) → is-contr (A i))
  is-contr-family-is-contr-Π-has-decidable-equality = {!!}
```
