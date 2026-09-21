# Exercise 13.3

```agda
module exercise-13-3-truncatedness-is-a-proposition where

open import universe-levels

open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-10-1-contractible-types
open import exercise-10-1-identity-types-contractible
open import exercise-10-6-dependent-pair-contractible-base
open import section-12-1-propositions
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
```

## Problem statement

### Exercise 13.3(a)

Show that for any type `A` the type `is-contr(A)` is a proposition.

### Exercise 13.3(b)

Show that for any type `A` and any `k ≥ -2`, the type `is-trunc_{k}(A)` is a proposition.

## Solutions

### Exercise 13.3(a)

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr (pair a α) =
      is-contr-Σ
        ( pair a α)
        ( a)
        ( is-contr-Π (is-prop-is-contr (pair a α) a))

  abstract
    is-property-is-contr : (H K : is-contr A) → is-contr (H ＝ K)
    is-property-is-contr H = is-prop-is-contr (is-contr-is-contr H) H

is-contr-Prop : {l : Level} → UU l → Prop l
pr1 (is-contr-Prop A) = is-contr A
pr2 (is-contr-Prop A) = is-property-is-contr
```

### Exercise 13.3(b)

```agda
abstract
  is-property-is-trunc :
    {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-trunc k A)
  is-property-is-trunc neg-two-𝕋 A = is-property-is-contr
  is-property-is-trunc (succ-𝕋 k) A =
    is-trunc-Π neg-one-𝕋
      ( λ x → is-trunc-Π neg-one-𝕋 (λ y → is-property-is-trunc k (x ＝ y)))

is-trunc-Prop : {l : Level} (k : 𝕋) (A : UU l) → Σ (UU l) (is-trunc neg-one-𝕋)
pr1 (is-trunc-Prop k A) = is-trunc k A
pr2 (is-trunc-Prop k A) = is-property-is-trunc k A
```

## Supplement

### Being a proposition is a property

```agda
abstract
  is-property-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-property-is-prop A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-contr))

is-prop-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-property-is-prop A
```
