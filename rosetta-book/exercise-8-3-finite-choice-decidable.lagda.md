# Exercise 8.3

```agda
module exercise-8-3-finite-choice-decidable where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-7-3-the-standard-finite-types
open import section-8-1-decidability-and-decidable-equality
```

## Problem statement

For any family `P` of decidable types indexed by `Fin{k}`, construct a function
```text
¬(Π(x:Fin{k}) P(x))→Σ(x:Fin{k}) ¬ P(x).
```

## Solution

```agda
is-decidable-family : {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-family {A = A} P = (x : A) → is-decidable (P x)
```

```agda
exists-not-not-for-all-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} → (is-decidable-family P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-for-all-Fin {l} zero-ℕ d H = ex-falso (H ind-empty)
exists-not-not-for-all-Fin {l} (succ-ℕ k) {P} d H with d (inr star)
... | inl p =
  T ( exists-not-not-for-all-Fin k
      ( λ x → d (inl x))
      ( λ f → H (ind-coproduct P f (ind-unit p))))
  where
  T : Σ (Fin k) (λ x → ¬ (P (inl x))) → Σ (Fin (succ-ℕ k)) (λ x → ¬ (P x))
  T z = pair (inl (pr1 z)) (pr2 z)
... | inr f = pair (inr star) f
```
