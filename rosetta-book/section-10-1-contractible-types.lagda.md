# Section 10.1 Contractible types

```agda
module section-10-1-contractible-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
```

<!-- rosetta-item: section-10.1 -->

## Definition 10.1.1

<!-- rosetta-item: definition-10.1.1 -->

We say that a type `A` is **contractible** if it comes equipped with an element of type
```text
is-contr(A) ≔ Σ(c:A) Π(x:A) c=x.
```
Given a pair `(c,C):is-contr(A)`, we call `c:A` the **center of contraction** of `A`, and we call `C:Π(x:A) c=x` the **contraction** of `A`.

<!-- rosetta-agda-block: definition-10.1.1-contractible-types -->

```agda
is-contr :
  {l : Level} → Type l → Type l
is-contr A = Σ A (λ a → (x : A) → a ＝ x)

abstract
  center :
    {l : Level} {A : Type l} → is-contr A → A
  center (pair c is-contr-A) = c

eq-is-contr' :
  {l : Level} {A : Type l} → is-contr A → (x y : A) → x ＝ y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : Type l} → is-contr A → {x y : A} → x ＝ y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction :
    {l : Level} {A : Type l} (is-contr-A : is-contr A) →
    (x : A) → (center is-contr-A) ＝ x
  contraction C x = eq-is-contr C

  coh-contraction :
    {l : Level} {A : Type l} (is-contr-A : is-contr A) →
    (contraction is-contr-A (center is-contr-A)) ＝ refl
  coh-contraction (pair c C) = left-inv (C c)
```
<!-- rosetta-item-end: definition-10.1.1 -->

## Remark 10.1.2

<!-- rosetta-item: remark-10.1.2 -->

Suppose `A` is a contractible type with center of contraction `c` and contraction `C`.
Then the type of `C` is (judgmentally) equal to the type
```text
const_c~id[A].
```
In other words, the contraction `C` is a *homotopy* from the constant function to the identity function.

<!-- rosetta-item-end: remark-10.1.2 -->

## Example 10.1.3

<!-- rosetta-item: example-10.1.3 -->

The unit type is easily seen to be contractible.
For the center of contraction we take `⋆:unit`.
Then we define a contraction `Π(x:unit) ⋆=x` by the induction principle of `unit`.
Applying the induction principle, it suffices to construct an identification of type `⋆ = ⋆`, for which we just take `refl`.

<!-- rosetta-agda-block: example-10.1.3-unit-contractible -->

```agda
abstract
  is-contr-unit : is-contr unit
  pr1 is-contr-unit = star
  pr2 is-contr-unit _ = refl
```
<!-- rosetta-item-end: example-10.1.3 -->

## Theorem 10.1.4

<!-- rosetta-item: theorem-10.1.4; latex-label: thm:total_path -->

For any `a:A`, the type
```text
Σ(x:A) a=x
```
is contractible.

### Proof

<!-- rosetta-item: subheading-10.1-proof -->

*Proof.* For the center of contraction we take
```text
(a,refl):Σ(x:A) a=x.
```
The contraction is constructed in Proposition 5.5.1. ◻

<!-- rosetta-agda-block: theorem-10.1.4-total-path -->

```agda
module _
  {l : Level} {A : Type l}
  where

  abstract
    is-contr-Id : (a : A) → is-contr (Σ A (λ x → a ＝ x))
    pr1 (pr1 (is-contr-Id a)) = a
    pr2 (pr1 (is-contr-Id a)) = refl
    pr2 (is-contr-Id a) (.a , refl) = refl
```
<!-- rosetta-item-end: theorem-10.1.4 -->
