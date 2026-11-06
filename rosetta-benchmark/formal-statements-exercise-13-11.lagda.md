# Exercise 13.11

```agda
module formal-statements-exercise-13-11 where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-5-1-the-inductive-definition-of-identity-types
open import exercise-6-4-strict-order-natural-numbers
```

## Problem statement

Show that `ℕ` satisfies **ordinal induction**, i.e., construct for any type family `P` over `ℕ` a function `ord-ind` of type

```text
  (Π(k : ℕ) (Π(m : ℕ) (m < k) → P(m)) → P(k)) → Π(n : ℕ) P(n).
```

Moreover, prove that

```text
  ord-ind(h,n) = h(n,λ m. λ p. ord-ind(h,m))
```

for any `n : ℕ` and any `h : Π(k : ℕ) (Π(m : ℕ) (m < k) → P(m)) → P(k)`.

## Formal Statements

```agda
□-<-ℕ : 
  {l : Level} → (ℕ → UU l) → (ℕ → UU l)
□-<-ℕ P k = (m : ℕ) → m <-ℕ k → P m

module _
  {l : Level} (P : ℕ → UU l)
  where

  ordinal-ind-ℕ :
    ((k : ℕ) → □-<-ℕ P k → P k) → (n : ℕ) → P n
  ordinal-ind-ℕ = {!!}

  compute-ordinal-ind-ℕ :
    (H : (k : ℕ) → □-<-ℕ P k → P k) (n : ℕ) →
    ordinal-ind-ℕ H n ＝ H n (λ m p → ordinal-ind-ℕ H m)
  compute-ordinal-ind-ℕ = {!!}
```
