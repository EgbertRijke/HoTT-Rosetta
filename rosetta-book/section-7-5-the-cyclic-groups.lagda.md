# Section 7.5 The cyclic groups

```agda
module section-7-5-the-cyclic-groups where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-5-6-the-laws-of-addition-on-natural-numbers
open import exercise-5-5-semiring-laws-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
```

<!-- rosetta-item: section-7.5 -->

We can now define the cyclic groups `ℤ/k` for each `k:ℕ`.
Note that `ℤ/k` must come equipped with the structure of a quotient `ℤ/{≡}` of `ℤ` by the congruence relation modulo `k`.
In the case where `k≐ 0`, we have that `x≡ ymod{0}` if and only if `x=y`.
This motivates the following definition:

## Definition 7.5.1

<!-- rosetta-item: definition-7.5.1; latex-label: defn:Zk -->

We define the type `ℤ/k` for each `k:ℕ` by
```text
ℤ/0≔ ℤ and ℤ/{(k+1)}≔Fin{k+1}.
```

<!-- rosetta-agda-block: definition-7.5.1-integers-modulo-adapted -->

```agda
ℤ-Mod : ℕ → Type lzero
ℤ-Mod zero-ℕ = ℤ
ℤ-Mod (succ-ℕ k) = Fin (succ-ℕ k)
```
<!-- rosetta-item-end: definition-7.5.1 -->

Recall from Exercise 5.7 that `ℤ/0` already comes equipped with the structure of a group, but the group structure on `ℤ/{(k+1)}` remains to be defined.

## Definition 7.5.2

<!-- rosetta-item: definition-7.5.2 -->

We define the **addition** operation on `ℤ/{(k+1)}` by
```text
x+y≔[nat-Fin(x)+nat-Fin(y)]_{k+1},
```
and we define the **additive inverse** operation on `ℤ/{(k+1)}` by
```text
-x≔[dist-ℕ(nat-Fin(x),k+1)]_{k+1}.
```

<!-- rosetta-agda-block: definition-7.5.2-addition-and-negation-finite -->

```agda
add-Fin : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin (succ-ℕ k) x y =
  mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))

add-Fin' : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin' k x y = add-Fin k y x
```

<!-- rosetta-agda-block: definition-7.5.2-negation-finite -->

```agda
neg-Fin :
  (k : ℕ) → Fin k → Fin k
neg-Fin (succ-ℕ k) x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))
```
<!-- rosetta-item-end: definition-7.5.2 -->

## Remark 7.5.3

<!-- rosetta-item: remark-7.5.3 -->

The following congruences modulo `k+1` follow immediately from Proposition 7.4.5:
```text
nat-Fin(0) ≡ 0
nat-Fin(x+y) ≡ nat-Fin(x)+nat-Fin(y)
nat-Fin(-x) ≡ dist-ℕ(nat-Fin(x),k+1).
```

<!-- rosetta-agda-block: remark-7.5.3-natural-value-congruences -->

```agda
cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  cong-ℕ k (nat-Fin k (add-Fin k x y)) ((nat-Fin k x) +ℕ (nat-Fin k y))
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  cong-ℕ k (nat-Fin k (neg-Fin k x)) (dist-ℕ (nat-Fin k x) k)
cong-neg-Fin {succ-ℕ k} x =
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))
```
<!-- rosetta-item-end: remark-7.5.3 -->

Before we show that addition on `ℤ/{k}` satisfies the group laws, we have to show that addition on `ℕ` preserves the congruence relation.

## Proposition 7.5.4

<!-- rosetta-item: proposition-7.5.4 -->

Consider `x,y,x',y':ℕ`.
If any two of the following three properties hold, then so does the third:

1.  `x≡ x'mod k`,

2.  `y≡ y'mod k`,

3.  `x+y≡ x'+y'mod k`.

### Proof

<!-- rosetta-item: subheading-7.5-proof -->

*Proof.* Recall that the distance function `dist-ℕ` is translation invariant by Exercise 6.5.
Therefore it follows that
```text
a≡ bmod k ↔ a+c≡ b+cmod k.(*)
```
We will use this observation to prove the claim.

First, suppose that `x≡ x'` and `y≡ y'` modulo `k`.
Then it follows by (\*) that
```text
x+y≡ x'+y≡ x'+y'.
```
This shows that (i) and (ii) together imply (iii).

Next, suppose that `x≡ x'` and `x+y≡ x'+y'` modulo `k`.
Then it follows that
```text
x+y≡ x'+y'≡ x+y'.
```
Applying (\*) once more in the reverse direction, we obtain that `y≡ y'` modulo `k`.
This shows that (i) and (iii) together imply (ii).

The remaining claim, that (ii) and (iii) together imply (i), follows by commutativity of addition from the fact that (i) and (iii) together imply (ii). ◻

<!-- rosetta-agda-block: proposition-7.5.4-congruence-support-excerpts -->

```agda
concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  x1 ＝ x2 → cong-ℕ k x2 x3 → x3 ＝ x4 → cong-ℕ k x1 x4
concatenate-eq-cong-eq-ℕ k refl H refl = H

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  x1 ＝ x2 → cong-ℕ k x2 x3 → cong-ℕ k x1 x3
concatenate-eq-cong-ℕ k refl H = H

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  cong-ℕ k x1 x2 → x2 ＝ x3 → cong-ℕ k x1 x3
concatenate-cong-eq-ℕ k H refl = H

translation-invariant-cong-ℕ :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (z +ℕ x) (z +ℕ y)
pr1 (translation-invariant-cong-ℕ k x y z (pair d p)) = d
pr2 (translation-invariant-cong-ℕ k x y z (pair d p)) =
  p ∙ inv (translation-invariant-dist-ℕ z x y)

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → cong-ℕ k x y → cong-ℕ k (x +ℕ z) (y +ℕ z)
translation-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

reflects-cong-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (x +ℕ y) (x +ℕ z) → cong-ℕ k y z
pr1 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) = d
pr2 (reflects-cong-add-ℕ {k} x {y} {z} (pair d p)) =
  p ∙ translation-invariant-dist-ℕ x y z
```

<!-- rosetta-agda-block: proposition-7.5.4-three-for-two-addition-congruence -->

```agda
congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k y y' → cong-ℕ k (x +ℕ y) (x' +ℕ y')
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (x +ℕ y) (x +ℕ y') (x' +ℕ y')
    ( translation-invariant-cong-ℕ' k x x' y' H)
    ( translation-invariant-cong-ℕ k y y' x K)

cong-right-summand-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k (x +ℕ y) (x' +ℕ y') → cong-ℕ k y y'
cong-right-summand-ℕ k {x} {y} {x'} {y'} H K =
  reflects-cong-add-ℕ x {y}
    ( transitive-cong-ℕ k
      ( x +ℕ y)
      ( x' +ℕ y')
      ( x +ℕ y')
      ( translation-invariant-cong-ℕ' k x' x y'
        ( symmetric-cong-ℕ k x x' H))
      ( K))

cong-left-summand-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k y y' → cong-ℕ k (x +ℕ y) (x' +ℕ y') → cong-ℕ k x x'
cong-left-summand-ℕ k {x} {y} {x'} {y'} H K =
  cong-right-summand-ℕ k {y} {x} {y'} {x'} H
    ( concatenate-eq-cong-ℕ k
      ( commutative-add-ℕ y x)
      ( concatenate-cong-eq-ℕ k {x1 = x +ℕ y}
        ( K)
        ( commutative-add-ℕ x' y')))
```
<!-- rosetta-item-end: proposition-7.5.4 -->

## Theorem 7.5.5

<!-- rosetta-item: theorem-7.5.5 -->

The addition operation on `ℤ/{k}` satisfies the laws of an abelian group:
```text
0+x = x x+0 = x
(-x)+x = 0 x+(-x) = 0
(x+y)+z = x+(y+z) x+y = y+x.
```

### Proof

<!-- rosetta-item: subheading-7.5-proof-2 -->

*Proof.* The fact that the addition operation on `ℤ/0` satisfies the laws of an abelian group was stated as Exercise 5.7.
Therefore we will only show that addition on `ℤ/{(k+1)}` satisfies the laws of an abelian group.

We first note that by commutativity of addition on `ℕ`, it follows immediately that addition on `ℤ/{(k+1)}` is commutative.

To prove associativity, note that by Theorem 7.4.7 it suffices to show that
```text
nat-Fin(x+y)+nat-Fin(z)≡nat-Fin(x)+nat-Fin(y+z)mod k+1.
```
Since addition on `ℤ/{(k+1)}` maps preserves the congruence relation, and since we have the congruences
```text
nat-Fin(x+y) ≡ nat-Fin(x)+nat-Fin(y) mod k+1
nat-Fin(y+z) ≡ nat-Fin(y)+nat-Fin(z) mod k+1,
```
it suffices to show that
```text
(nat-Fin(x)+nat-Fin(y))+nat-Fin(z) ≡ nat-Fin(x)+(nat-Fin(y)+nat-Fin(z)) mod k+1.
```
This follows immediately by associativity of addition on `ℕ`.

To show that addition on `ℤ/{(k+1)}` satisfies the right unit law, we first observe that it suffices to show that
```text
[nat-Fin(x)+nat-Fin(0)]_{k+1}=[nat-Fin(x)]_{k+1}
```
because there is an identification `[nat-Fin(x)]_{k+1}=x` by Theorem 7.4.8.
By Theorem 7.4.7 it now suffices tho show that
```text
nat-Fin(x)+nat-Fin(0)≡nat-Fin(x)mod k+1.
```
This follows immediately from the fact that `nat-Fin(0)=0`.
The left unit law now follows from the right unit law by commutativity.
We leave the inverse laws as an exercise. ◻

<!-- rosetta-agda-block: theorem-7.5.5-abelian-group-laws-finite-adapted -->

```agda
commutative-add-Fin : (k : ℕ) (x y : Fin k) → add-Fin k x y ＝ add-Fin k y x
commutative-add-Fin (succ-ℕ k) x y =
  ap
    ( mod-succ-ℕ k)
    ( commutative-add-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y))

associative-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  add-Fin k (add-Fin k x y) z ＝ add-Fin k x (add-Fin k y z)
associative-add-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y))
      ( nat-Fin (succ-ℕ k) z))
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) x)
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) z)}
      { x2 =
        add-ℕ
          ( (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))
          ( nat-Fin (succ-ℕ k) z)}
      { x3 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) x)
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k)
          ( add-Fin (succ-ℕ k) y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y)}
        { y = nat-Fin (succ-ℕ k) z}
        { x' = (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y)}
        { y' = nat-Fin (succ-ℕ k) z}
        ( cong-add-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) z)))
      ( associative-add-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) x}
        { y = (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z)}
        { x' = nat-Fin (succ-ℕ k) x}
        { y' = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z))
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))
          ( cong-add-Fin y z))))

right-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) x (zero-Fin k) ＝ x
right-unit-law-add-Fin k x =
  ( eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) (zero-Fin k)))
    ( (nat-Fin (succ-ℕ k) x) +ℕ zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin (succ-ℕ k) x}
      { y = nat-Fin (succ-ℕ k) (zero-Fin k)}
      { x' = nat-Fin (succ-ℕ k) x}
      { y' = zero-ℕ}
      ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
      ( cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})))) ∙
  ( is-section-nat-Fin k x)

left-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) (zero-Fin k) x ＝ x
left-unit-law-add-Fin k x =
  ( commutative-add-Fin (succ-ℕ k) (zero-Fin k) x) ∙
  ( right-unit-law-add-Fin k x)

left-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x) x ＝ zero-Fin k
left-inverse-law-add-Fin k x =
  eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x)) +ℕ (nat-Fin (succ-ℕ k) x))
    ( zero-ℕ)
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x))
          ( nat-Fin (succ-ℕ k) x)}
      { x2 =
        (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k)) +ℕ (nat-Fin (succ-ℕ k) x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( translation-invariant-cong-ℕ' (succ-ℕ k)
        ( nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x))
        ( dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))
        ( nat-Fin (succ-ℕ k) x)
        ( cong-neg-Fin x))
      ( is-difference-dist-ℕ' (nat-Fin (succ-ℕ k) x) (succ-ℕ k)
        ( leq-le-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k)
          ( strict-upper-bound-nat-Fin (succ-ℕ k) x)))
      ( symmetric-cong-ℕ (succ-ℕ k) (succ-ℕ k) zero-ℕ
        ( cong-zero-ℕ (succ-ℕ k))))

right-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x) ＝ zero-Fin k
right-inverse-law-add-Fin k x =
  ( commutative-add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x)) ∙
  ( left-inverse-law-add-Fin k x)
```
<!-- rosetta-item-end: theorem-7.5.5 -->
