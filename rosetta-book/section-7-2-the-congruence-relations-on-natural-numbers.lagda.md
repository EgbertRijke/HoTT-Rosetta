# Section 7.2 The congruence relations on ℕ

```agda
module section-7-2-the-congruence-relations-on-natural-numbers where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import exercise-7-1-divisibility-three-for-two
```

<!-- rosetta-item: section-7.2 -->

Relations in the Curry-Howard interpretation of logic into type theory are also type valued.
More specifically, a binary relation on a type `A` is a family of types `R(x,y)` indexed by `x,y:A`.
Such relations are sometimes called *typal*.

## Definition 7.2.1

<!-- rosetta-item: definition-7.2.1 -->

Consider a type `A`.
A **(typal) binary relation** on `A` is defined to be a family of types `R(x,y)` indexed by `x,y:A`.
Given a binary relation `R` on `A`, we say that `R` is **reflexive** if it comes equipped with
```text
ρ : Π(x:A) R(x,x),
```

we say that `R` is **symmetric** if it comes equipped with

```text
σ : Π(x,y:A) R(x,y)→ R(y,x),
```

and we say that `R` is **transitive** if it comes equipped with

```text
τ : Π(x,y,z:A) R(x,y)→ (R(y,z)→ R(x,z)).
```
A **(typal) equivalence relation** on `A` is a reflexive, symmetric, and transitive binary typal relation on `A`.

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-31 -->

```agda
Relation : {l1 : Level} (l : Level) (A : Type l1) → Type (l1 ⊔ lsuc l)
Relation l A = A → A → Type l
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-43 -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (R : Relation l2 A)
  where

  is-reflexive : Type (l1 ⊔ l2)
  is-reflexive = (x : A) → R x x
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-58 -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (R : Relation l2 A)
  where

  is-symmetric : Type (l1 ⊔ l2)
  is-symmetric = (x y : A) → R x y → R y x
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-73 -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (R : Relation l2 A)
  where

  is-transitive : Type (l1 ⊔ l2)
  is-transitive = (x y z : A) → R y z → R x y → R x z
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-86 -->

```agda
is-equivalence-relation :
  {l1 l2 : Level} {A : Type l1} (R : Relation l2 A) → Type (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive R ×
  is-symmetric R ×
  is-transitive R

equivalence-relation :
  (l : Level) {l1 : Level} (A : Type l1) → Type (lsuc l ⊔ l1)
equivalence-relation l A = Σ (Relation l A) is-equivalence-relation
```
<!-- rosetta-item-end: definition-7.2.1 -->

To define the congruence relation modulo `k` in type theory using the Curry-Howard interpretation, we will define for any three natural numbers `x`, `y`, and `k`, a *type*
```text
x≡ ymod k
```
consisting of the proofs that `x` is congruent to `y` modulo `k`.
We will define this type by directly interpreting Gauss’ definition of the congruence relations in his *Disquisitiones Arithmeticae* : two numbers `x` and `y` are congruent modulo `k` if `k` divides the symmetric difference `dist-ℕ(x,y)` between `x` and `y`.
Recall that `dist-ℕ(x,y)` was defined in Exercise 6.5 recursively by
```text
dist-ℕ(0,0) ≔ 0 dist-ℕ(0,y+1) ≔ y+1
dist-ℕ(x+1,0) ≔ x+1 dist-ℕ(x+1,y+1) ≔ dist-ℕ(x,y).
```

## Definition 7.2.2

<!-- rosetta-item: definition-7.2.2 -->

Consider three natural numbers `k,x,y:ℕ`.
We say that `x` is **congruent to `y` modulo `k`** if it comes equipped with an element of type
```text
x≡ y mod k ≔ k|dist-ℕ(x,y).
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-129 -->

```agda
cong-ℕ :
  ℕ → ℕ → ℕ → Type lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)
```
<!-- rosetta-item-end: definition-7.2.2 -->

## Example 7.2.3

<!-- rosetta-item: example-7.2.3 -->

For example, `k≡ 0mod k`.
To see this, we have to show that `k|dist-ℕ(k,0)`.
Since `dist-ℕ(k,0)=k` it suffices to show that `k| k`.
That is, we have to construct a natural number `l` equipped with an identification `p:kl=k`.
Of course, we choose `l≔ 1`, and the equation `k1=k` holds by the right unit law for multiplication on `ℕ`, which was shown in Exercise 5.5.

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-145 -->

```agda
cong-zero-ℕ :
  (k : ℕ) → cong-ℕ k k zero-ℕ
pr1 (cong-zero-ℕ k) = 1
pr2 (cong-zero-ℕ k) =
  (left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k))
```
<!-- rosetta-item-end: example-7.2.3 -->

## Proposition 7.2.4

<!-- rosetta-item: proposition-7.2.4; latex-label: prp:congruence-eqrel -->

For each `k:ℕ`, the congruence relation modulo `k` is an equivalence relation.

### Proof

<!-- rosetta-item: subheading-7.2-proof -->

*Proof.* Reflexivity follows from the fact that `dist-ℕ(x,x)=0`, and any number divides `0`.
Symmetry follows from the fact that `dist-ℕ(x,y)=dist-ℕ(y,x)` for any two natural numbers `x` and `y`.

The non-trivial part of the claim is therefore transitivity.
Here we use the fact that for any three natural numbers `x`, `y`, and `z`, at least one of the equalities
```text
dist-ℕ(x,y)+dist-ℕ(y,z) =dist-ℕ(x,z)
dist-ℕ(y,z)+dist-ℕ(x,z) =dist-ℕ(x,y)
dist-ℕ(x,z)+dist-ℕ(x,y) =dist-ℕ(y,z)
```
holds.
A formal proof of this fact is given by case analysis on the six possible ways in which `x`, `y`, and `z` can be ordered:
```text
x≤ y and y≤ z, x≤ z and z≤ y,
y≤ z and z≤ x, y≤ x and x≤ z,
z≤ x and x≤ y, z≤ y and y≤ x.
```
Therefore it follows by Exercise 6.5 and Proposition 7.1.5 that `{k|dist-ℕ(x,z)}` if `{k|dist-ℕ(x,y)}` and `{k|dist-ℕ(y,z)}`. ◻

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-163 -->

```agda
refl-cong-ℕ : (k : ℕ) → is-reflexive (cong-ℕ k)
pr1 (refl-cong-ℕ k x) = zero-ℕ
pr2 (refl-cong-ℕ k x) =
  (left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl))
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-173 -->

```agda
symmetric-cong-ℕ : (k : ℕ) → is-symmetric (cong-ℕ k)
pr1 (symmetric-cong-ℕ k x y (pair d p)) = d
pr2 (symmetric-cong-ℕ k x y (pair d p)) = p ∙ (commutative-dist-ℕ x y)
```

<!-- rosetta-agda-block: section-7-2-the-congruence-relations-on-natural-numbers-block-203 -->

```agda
transitive-cong-ℕ : (k : ℕ) → is-transitive (cong-ℕ k)
transitive-cong-ℕ k x y z e d with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z e d | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
transitive-cong-ℕ k x y z e d | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
transitive-cong-ℕ k x y z e d | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))
```
<!-- rosetta-item-end: proposition-7.2.4 -->
