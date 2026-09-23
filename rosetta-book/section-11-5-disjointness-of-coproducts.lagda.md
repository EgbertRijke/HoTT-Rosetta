# Section 11.5 Disjointness of coproducts

```agda
module section-11-5-disjointness-of-coproducts where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-7-3-the-standard-finite-types
open import exercise-7-5-observational-equality-finite-types
open import exercise-8-7-decidable-equality-coproducts
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
```

In our third application of the fundamental theorem of identity types, we characterize the identity types of coproducts.
Our goal in this section is to prove the following theorem.

## Theorem 11.5.1

Let `A` and `B` be types.
Then there are equivalences

```text
  (inl(x) = inl(x')) ≃ (x = x')
  (inl(x) = inr(y')) ≃ ∅
  (inr(y) = inl(x')) ≃ ∅
  (inr(y) = inr(y')) ≃ (y=y')
```

for any `x, x' : A` and `y, y' : B`.

In order to prove Theorem 11.5.1, we first define a binary relation `Eq-coproduct_{A,B}` on the coproduct `A + B`.

## Definition 11.5.2

Let `A` and `B` be types.
We define

```text
  Eq-coproduct_{A,B} : (A + B) → (A + B) → 𝒰
```

by double induction on the coproduct, postulating

```text
  Eq-coproduct_{A,B}(inl(x),inl(x')) ≔ (x = x')
  Eq-coproduct_{A,B}(inl(x),inr(y')) ≔ ∅
  Eq-coproduct_{A,B}(inr(y),inl(x')) ≔ ∅
  Eq-coproduct_{A,B}(inr(y),inr(y')) ≔ (y = y').
```

The relation `Eq-coproduct_{A,B}` is also called the **observational equality of coproducts**.

## Lemma 11.5.3

The observational equality relation `Eq-coproduct_{A,B}` on `A+B` is reflexive, and therefore there is a map

```text
  Eq-coproduct-eq : Π(s, t : A + B) (s = t) → Eq-coproduct_{A,B}(s,t).
```

### Construction

The reflexivity term `ρ` is constructed by induction on `t : A + B`, using

```text
  ρ(inl(x)) ≔ refl : Eq-coproduct_{A,B}(inl(x),inl(x))
  ρ(inr(y)) ≔ refl : Eq-coproduct_{A,B}(inr(y),inr(y)).
```

To show that `Eq-coproduct-eq` is a family of equivalences, we will use the fundamental theorem of identity types, Theorem 11.2.2.
Therefore, we need to prove the following proposition.

## Proposition 11.5.4

For any `s : A + B` the total space

```text
  Σ(t : A + B) Eq-coproduct_{A,B}(s,t)
```

is contractible.

### Proof

For convenience, let us write `E ≔ Eq-coproduct_{A,B}`.
By induction on `s`, it suffices to show that the total spaces

```text
  Σ(t : A + B) E(inl(x),t) and Σ(t : A + B) E(inr(y),t)
```

are contractible.
The two proofs are similar, so we only prove that the type on the left is contractible.
By the laws of coproducts and `Σ`-types given in Examples 9.2.9 and 9.2.10, we simply compute

```text
  Σ(t : A + B) E(inl(x),t)
  ≃ (Σ(x' : A) E(inl(x),inl(x'))) + (Σ(y' : B) E(inl(x),inr(y')))
  ≃ (Σ(x' : A) x = x') + (Σ(y' : B) ∅)
  ≃ Σ(x' : A) x = x'.
```

The last type in this computation is contractible by Theorem 10.1.4, so we conclude that the total space of `E(inl(x))` is contractible. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-torsorial-Eq-coproduct :
    (x : A + B) → is-torsorial (Eq-coproduct x)
  pr1 (pr1 (is-torsorial-Eq-coproduct (inl x))) = inl x
  pr2 (pr1 (is-torsorial-Eq-coproduct (inl x))) = Eq-eq-coproduct-inl refl
  pr2
    ( is-torsorial-Eq-coproduct (inl x)) (.(inl x) , Eq-eq-coproduct-inl refl) =
    refl
  pr1 (pr1 (is-torsorial-Eq-coproduct (inr x))) = inr x
  pr2 (pr1 (is-torsorial-Eq-coproduct (inr x))) = Eq-eq-coproduct-inr refl
  pr2
    ( is-torsorial-Eq-coproduct (inr x)) (.(inr x) , Eq-eq-coproduct-inr refl) =
    refl
```

### Proof

The proof is now concluded with an application of Theorem 11.2.2, using Proposition 11.5.4. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv-Eq-eq-coproduct : (x y : A + B) → is-equiv (Eq-eq-coproduct x y)
  is-equiv-Eq-eq-coproduct x =
    fundamental-theorem-id (is-torsorial-Eq-coproduct x) (Eq-eq-coproduct x)

  extensionality-coproduct : (x y : A + B) → (x ＝ y) ≃ Eq-coproduct x y
  pr1 (extensionality-coproduct x y) = Eq-eq-coproduct x y
  pr2 (extensionality-coproduct x y) = is-equiv-Eq-eq-coproduct x y
```

## Supplement

### The left and right inclusions are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  module _
    (x y : A)
    where

    map-compute-Eq-coproduct-inl-inl :
      Eq-coproduct {B = B} (inl x) (inl y) → (x ＝ y)
    map-compute-Eq-coproduct-inl-inl (Eq-eq-coproduct-inl p) = p

    is-section-Eq-eq-coproduct-inl :
      (map-compute-Eq-coproduct-inl-inl ∘ Eq-eq-coproduct-inl) ~ id
    is-section-Eq-eq-coproduct-inl p = refl

    is-retraction-Eq-eq-coproduct-inl :
      (Eq-eq-coproduct-inl ∘ map-compute-Eq-coproduct-inl-inl) ~ id
    is-retraction-Eq-eq-coproduct-inl (Eq-eq-coproduct-inl p) = refl

    is-equiv-map-compute-Eq-coproduct-inl-inl :
      is-equiv map-compute-Eq-coproduct-inl-inl
    is-equiv-map-compute-Eq-coproduct-inl-inl =
      is-equiv-is-invertible
        ( Eq-eq-coproduct-inl)
        ( is-section-Eq-eq-coproduct-inl)
        ( is-retraction-Eq-eq-coproduct-inl)

    compute-Eq-coproduct-inl-inl : Eq-coproduct (inl x) (inl y) ≃ (x ＝ y)
    pr1 compute-Eq-coproduct-inl-inl = map-compute-Eq-coproduct-inl-inl
    pr2 compute-Eq-coproduct-inl-inl = is-equiv-map-compute-Eq-coproduct-inl-inl

    compute-eq-coproduct-inl-inl : (inl x ＝ inl y) ≃ (x ＝ y)
    compute-eq-coproduct-inl-inl =
      compute-Eq-coproduct-inl-inl ∘e extensionality-coproduct (inl x) (inl y)

    map-compute-eq-coproduct-inl-inl : (inl x ＝ inl y) → x ＝ y
    map-compute-eq-coproduct-inl-inl = map-equiv compute-eq-coproduct-inl-inl

    is-equiv-map-compute-eq-coproduct-inl-inl :
      is-equiv map-compute-eq-coproduct-inl-inl
    is-equiv-map-compute-eq-coproduct-inl-inl =
      is-equiv-map-equiv compute-eq-coproduct-inl-inl

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coproduct-inl-inr : Eq-coproduct (inl x) (inr y) → empty
    map-compute-Eq-coproduct-inl-inr ()

    is-equiv-map-compute-Eq-coproduct-inl-inr :
      is-equiv map-compute-Eq-coproduct-inl-inr
    is-equiv-map-compute-Eq-coproduct-inl-inr =
      is-equiv-is-empty' map-compute-Eq-coproduct-inl-inr

    compute-Eq-coproduct-inl-inr : Eq-coproduct (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coproduct-inl-inr = map-compute-Eq-coproduct-inl-inr
    pr2 compute-Eq-coproduct-inl-inr = is-equiv-map-compute-Eq-coproduct-inl-inr

    compute-eq-coproduct-inl-inr : (inl x ＝ inr y) ≃ empty
    compute-eq-coproduct-inl-inr =
      compute-Eq-coproduct-inl-inr ∘e extensionality-coproduct (inl x) (inr y)

    is-empty-eq-coproduct-inl-inr : is-empty (inl x ＝ inr y)
    is-empty-eq-coproduct-inl-inr = map-equiv compute-eq-coproduct-inl-inr

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coproduct-inr-inl : Eq-coproduct (inr x) (inl y) → empty
    map-compute-Eq-coproduct-inr-inl ()

    is-equiv-map-compute-Eq-coproduct-inr-inl :
      is-equiv map-compute-Eq-coproduct-inr-inl
    is-equiv-map-compute-Eq-coproduct-inr-inl =
      is-equiv-is-empty' map-compute-Eq-coproduct-inr-inl

    compute-Eq-coproduct-inr-inl : Eq-coproduct (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coproduct-inr-inl = map-compute-Eq-coproduct-inr-inl
    pr2 compute-Eq-coproduct-inr-inl = is-equiv-map-compute-Eq-coproduct-inr-inl

    compute-eq-coproduct-inr-inl : (inr x ＝ inl y) ≃ empty
    compute-eq-coproduct-inr-inl =
      compute-Eq-coproduct-inr-inl ∘e extensionality-coproduct (inr x) (inl y)

    is-empty-eq-coproduct-inr-inl : is-empty (inr x ＝ inl y)
    is-empty-eq-coproduct-inr-inl = map-equiv compute-eq-coproduct-inr-inl

  module _
    (x y : B)
    where

    map-compute-Eq-coproduct-inr-inr :
      Eq-coproduct {A = A} (inr x) (inr y) → x ＝ y
    map-compute-Eq-coproduct-inr-inr (Eq-eq-coproduct-inr p) = p

    is-section-Eq-eq-coproduct-inr :
      (map-compute-Eq-coproduct-inr-inr ∘ Eq-eq-coproduct-inr) ~ id
    is-section-Eq-eq-coproduct-inr p = refl

    is-retraction-Eq-eq-coproduct-inr :
      (Eq-eq-coproduct-inr ∘ map-compute-Eq-coproduct-inr-inr) ~ id
    is-retraction-Eq-eq-coproduct-inr (Eq-eq-coproduct-inr p) = refl

    is-equiv-map-compute-Eq-coproduct-inr-inr :
      is-equiv map-compute-Eq-coproduct-inr-inr
    is-equiv-map-compute-Eq-coproduct-inr-inr =
      is-equiv-is-invertible
        ( Eq-eq-coproduct-inr)
        ( is-section-Eq-eq-coproduct-inr)
        ( is-retraction-Eq-eq-coproduct-inr)

    compute-Eq-coproduct-inr-inr : Eq-coproduct (inr x) (inr y) ≃ (x ＝ y)
    pr1 compute-Eq-coproduct-inr-inr = map-compute-Eq-coproduct-inr-inr
    pr2 compute-Eq-coproduct-inr-inr = is-equiv-map-compute-Eq-coproduct-inr-inr

    compute-eq-coproduct-inr-inr : (inr x ＝ inr y) ≃ (x ＝ y)
    compute-eq-coproduct-inr-inr =
      compute-Eq-coproduct-inr-inr ∘e extensionality-coproduct (inr x) (inr y)

    map-compute-eq-coproduct-inr-inr : (inr x ＝ inr y) → x ＝ y
    map-compute-eq-coproduct-inr-inr = map-equiv compute-eq-coproduct-inr-inr

    is-equiv-map-compute-eq-coproduct-inr-inr :
      is-equiv map-compute-eq-coproduct-inr-inr
    is-equiv-map-compute-eq-coproduct-inr-inr =
      is-equiv-map-equiv compute-eq-coproduct-inr-inr
```
