# Section 7.4 The natural numbers modulo k+1

```agda
module section-7-4-the-natural-numbers-modulo-k-plus-one where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-4-2-the-unit-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-3-order-natural-numbers
open import exercise-6-4-strict-order-natural-numbers
open import exercise-6-5-distance-natural-numbers
open import section-7-1-the-curry-howard-interpretation
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-7-3-the-standard-finite-types
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-3-the-empty-type
open import section-5-4-transport
open import exercise-6-1-injectivity-addition-multiplication
```

<!-- rosetta-item: section-7.4 -->

Given an equivalence relation `~` on a set `A` in classical mathematics, the quotient `A/{~}` comes equipped with a quotient map `q:A→ A/{~}` that satisfies two important properties: (1) The map `q` satisfies the condition
```text
q(x)=q(y)↔ x~ y,
```
and (2) the map `q` is surjective.
The first condition is called the **effectiveness** of the quotient map.

In classical mathematics, a map `f:A→ B` is said to be surjective if for every `b∈ B` there exists an element `a∈ A` such that `f(a)=b`.
Following the Curry-Howard interpretation, a map `f:A→ B` is therefore surjective if it comes equipped with a dependent function
```text
Π(b:B) Σ(a:A) f(a)=b.
```
However, there is a subtle issue with this interpretation of surjectivity.
It is somewhat stronger than the classical notion of surjectivity, because a dependent function `Π(b:B) Σ(a:A) f(a)=b` provides for every element `b:B` an *explicit* element `a:A` equipped with an explicit identification `p:f(a)=b`, whereas in the classical notion of surjectivity such an element `a∈ A` is merely asserted to exist.
To emphasize that the Curry-Howard interpretation of surjectivity is stronger than intended we make the following definition, and we will properly introduce surjective maps in Section 15.2.

## Definition 7.4.1

<!-- rosetta-item: definition-7.4.1 -->

Consider a function `f:A→ B`.
We say that `f` is **split surjective** if it comes equipped with an element of type
```text
is-split-surjective(f):=Π(b:B) Σ(a:A) f(a)=b.
```

<!-- rosetta-agda-block: definition-7.4.1-split-surjective-adapted -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-split-surjective : (A → B) → Type (l1 ⊔ l2)
  is-split-surjective f = (b : B) → Σ A (λ x → f x ＝ b)
```
<!-- rosetta-item-end: definition-7.4.1 -->

Martin-Löf’s dependent type theory doesn’t have a general way of forming quotients of types.
However, in the specific case of the congruence relations on `ℕ` we can define the type of natural numbers modulo `k+1` as the standard finite type `Fin{k+1}`.
We will show that `Fin{k+1}` comes equipped with a map
```text
[_]_{k+1}:ℕ→ Fin{k+1}
```
for each `k:ℕ`, and we will show in Theorems 7.4.7 and 7.4.8 that this map satisfies conditions (1) and (2) in the split surjective sense.

To prepare for the definition of the quotient map `[_]_{k+1}`, we will first define a zero element of `Fin{k+1}` and successor function on each `Fin{k}`.
We will also define an auxiliary function `skip-zero-Fin_k:Fin{k}→Fin{k+1}`, which is used in the definition of the successor function.
The map `[_]_{k+1}` is then defined by iterating the successor function.

## Definition 7.4.2

<!-- rosetta-item: definition-7.4.2 -->

 

1.  We define the **zero element** `zero-Fin_k:Fin{k+1}` recursively by
```text
zero-Fin_0 ≔⋆
zero-Fin_{k+1} ≔ i(zero-Fin_k).
```

Since there is a mismatch between the index of `zero-Fin_k` and the index of its type, we will often simply write `zero-Fin` or `0` for the zero element of `Fin{k+1}`.

2.  We define the function `skip-zero-Fin_k:Fin{k}→Fin{k+1}` recursively by

```text
skip-zero-Fin_{k+1}(i(x)) ≔ i(skip-zero-Fin_k(x))
skip-zero-Fin_{k+1}(⋆) ≔ ⋆.
```

3.  We define the **successor function** `succ-Fin_k:Fin{k}→Fin{k}` recursively by

```text
succ-Fin_{k+1}(i(x)) ≔ skip-zero-Fin_k(x)
succ-Fin_{k+1}(⋆) ≔ zero-Fin_k.
```

<!-- rosetta-agda-block: definition-7.4.2-finite-zero-and-successor-adapted -->

```agda
zero-Fin : (k : ℕ) → Fin (succ-ℕ k)
zero-Fin zero-ℕ = inr star
zero-Fin (succ-ℕ k) = inl (zero-Fin k)

skip-zero-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-zero-Fin (succ-ℕ k) (inl x) = inl (skip-zero-Fin k x)
skip-zero-Fin (succ-ℕ k) (inr star) = inr star

succ-Fin : (k : ℕ) → Fin k → Fin k
succ-Fin (succ-ℕ k) (inl x) = skip-zero-Fin k x
succ-Fin (succ-ℕ k) (inr star) = zero-Fin k
```
<!-- rosetta-item-end: definition-7.4.2 -->

## Definition 7.4.3

<!-- rosetta-item: definition-7.4.3 -->

For any `k:ℕ`, we define the map `[_]_{k+1}:ℕ→Fin{k+1}` recursively on `x` by
```text
[0]_{k+1} ≔ 0
[x+1]_{k+1} ≔ succ-Fin_{k+1}[x]_{k+1}.
```

<!-- rosetta-agda-block: definition-7.4.3-mod-succ-natural-numbers -->

```agda
mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin k
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (succ-ℕ k) (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin 2
mod-two-ℕ = mod-succ-ℕ 1

mod-three-ℕ : ℕ → Fin 3
mod-three-ℕ = mod-succ-ℕ 2
```
<!-- rosetta-item-end: definition-7.4.3 -->

Our next intermediate goal is to show that `x≡ nat-Fin[x]_{k+1}mod k+1` for any natural number `x`.
This fact is a consequence of the following simple lemma, that will help us compute with the maps `nat-Fin : Fin{k}→ℕ`.

## Lemma 7.4.4

<!-- rosetta-item: lemma-7.4.4; latex-label: lem:nat-Fin -->

We make three claims:

1.  For any `k:ℕ` there is an identification
```text
nat-Fin(zero-Fin_k) = 0
```

2.  For any `k:ℕ` and any `x:Fin{k}`, we have

```text
nat-Fin(skip-zero-Fin_k(x)) = nat-Fin(x)+1.
```

3.  For any `k:ℕ` and any `x:Fin{k}`, we have

```text
nat-Fin(succ-Fin_k(x)) ≡ nat-Fin(x)+1 mod k.
```

### Proof

<!-- rosetta-item: subheading-7.4-proof -->

*Proof.* For the first claim, we define an identification `α_k:nat-Fin(zero-Fin_k)=0` recursively by
```text
α_0 ≔ refl
α_{k+1} ≔ α_k.
```

For the second claim, we define an identification `β_k(x):nat-Fin(skip-zero-Fin_k(x))=nat-Fin(x)+1` recursively by

```text
β_{k+1}(i(x)) ≔ β_k(x)
β_{k+1}(⋆) ≔ refl.
```
For the third claim, we again define an element `γ_k(x):nat-Fin(succ-Fin_k(x)) ≡ nat-Fin(x)+1mod{k}` recursively.
To obtain
```text
γ_{k+1}(i(x)) : nat-Fin(succ-Fin_{k+1}(i(x))) ≡nat-Fin(i(x))+1mod{k+1},
```
we calculate
```text
nat-Fin(succ-Fin_{k+1}(i(x))) ≐ nat-Fin(skip-zero-Fin(x))  by definition of succ-Fin
= nat-Fin(x)+1  by claim (ii).
```
Since the congruence relation modulo `k+1` is reflexive, we obtain `γ_{k+1}(i(x))` from the identification of the above calculation.
To obtain
```text
γ_{k+1}(⋆) : nat-Fin(succ-Fin_{k+1}(⋆)) ≡ nat-Fin(⋆)+1mod{k+1},
```
we calculate
```text
nat-Fin(succ-Fin_{k+1}(⋆)) ≐ nat-Fin(0)  by definition of succ-Fin
= 0  by claim (i)
≡ k+1  \text{by \cref{rmk:elementary-facts-div}}
≐ nat-Fin(⋆)+1  by definition of nat-Fin.
```
 ◻

<!-- rosetta-agda-block: lemma-7.4.4-natural-values-finite-successor-adapted -->

```agda
is-zero-nat-zero-Fin : {k : ℕ} → nat-Fin (succ-ℕ k) (zero-Fin k) ＝ zero-ℕ
is-zero-nat-zero-Fin {zero-ℕ} = refl
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

nat-skip-zero-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (skip-zero-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-skip-zero-Fin (succ-ℕ k) (inl x) = nat-skip-zero-Fin k x
nat-skip-zero-Fin (succ-ℕ k) (inr star) = refl

nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x)) ＝ succ-ℕ (nat-Fin k x)
nat-succ-Fin k x = nat-skip-zero-Fin k x
```
<!-- rosetta-item-end: lemma-7.4.4 -->

## Proposition 7.4.5

<!-- rosetta-item: proposition-7.4.5; latex-label: prp:cong-nat-mod-succ -->

For any `x:ℕ` we have
```text
nat-Fin[x]_{k+1}≡ x mod k+1.
```

### Proof

<!-- rosetta-item: subheading-7.4-proof-2 -->

*Proof.* The proof by induction on `x`.
The fact that
```text
nat-Fin[0]_{k+1}≡ 0 mod {k+1}
```
is immediate from the fact that `nat-Fin[0]_{k+1}≐nat-Fin(0)=0`, which was shown in Lemma 7.4.4.
In the inductive step, we have to show that
```text
nat-Fin[x+1]_{k+1}≡ x+1mod k+1.
```
This follows from the following computation
```text
nat-Fin[x+1]_{k+1} ≐ nat-Fin(succ-Fin_{k+1}[x]_{k+1})  by definition of [_]_{k+1}
≡ nat-Fin[x]_{k+1}+1  \text{by \cref{lem:nat-Fin}}
≡ x+1  by the inductive hypothesis.
```
 ◻

<!-- rosetta-agda-block: proposition-7.4.5-congruence-mod-successor-adapted -->

```agda
cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → x ＝ y → cong-ℕ k x y
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x

cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  cong-ℕ k (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    (succ-ℕ k)
    (nat-succ-Fin k x)
cong-nat-succ-Fin (succ-ℕ k) (inr star) =
  tr (λ z → cong-ℕ (succ-ℕ k) z (succ-ℕ k)) (inv (is-zero-nat-zero-Fin {k}))
    (symmetric-cong-ℕ (succ-ℕ k) (succ-ℕ k) zero-ℕ (cong-zero-ℕ (succ-ℕ k)))

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
cong-nat-mod-succ-ℕ k zero-ℕ =
  tr (λ z → cong-ℕ (succ-ℕ k) z zero-ℕ)
    (inv (is-zero-nat-zero-Fin {k})) (refl-cong-ℕ (succ-ℕ k) zero-ℕ)
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-cong-ℕ
    (succ-ℕ k)
    (nat-Fin (succ-ℕ k) (mod-succ-ℕ k (succ-ℕ x)))
    (succ-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)))
    (succ-ℕ x)
    (cong-nat-mod-succ-ℕ k x)
    (cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
```
<!-- rosetta-item-end: proposition-7.4.5 -->

We need one more fact before we can prove Theorems 7.4.7 and 7.4.8.

## Proposition 7.4.6

<!-- rosetta-item: proposition-7.4.6; latex-label: cor:eq-congN -->

For any natural number `x<d` we have
```text
d| x↔ x=0.
```
Consequently, for any two natural numbers `x` and `y` such that `dist-ℕ(x,y)<k`, we have
```text
x≡ ymod k↔ x=y.
```

### Proof

<!-- rosetta-item: subheading-7.4-proof-3 -->

*Proof.* Note that the implication `x=0→ d| x` is trivial, so it suffices to prove the forward implication
```text
d| x → x=0.
```
This implication clearly holds if `x≐ 0`.
Therefore we only have to show that `d| x+1` implies `x+1=0`, if we assume that `x+1<d`.
In other words, we will derive a contradiction from the hypotheses that `x+1<d` and `d| x+1`.
To reach a contradiction we use Exercise 6.4, by which it suffices to show that `d≤ x+1`.

We proceed by `Σ`-induction on the (unnamed) variable of type `d| x+1`, so we get to assume a natural number `k` equipped with an identification `p:dk=x+1`.
In the case where `k≐ 0` we reach an immediate contradiction via Theorem 6.4.2, because we obtain that `0=d· 0=x+1`.
In the case where `k≐succ-ℕ(k')` it follows that
```text
d≤ dk'+ d≐ dk = x+1.
```
 ◻

<!-- rosetta-agda-block: proposition-7.4.6-small-divisor-and-bounded-congruence-adapted -->

```agda
abstract
  is-zero-div-ℕ :
    (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
  is-zero-div-ℕ d zero-ℕ H D = refl
  is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
    ex-falso
      ( contradiction-le-ℕ
        ( succ-ℕ x) d H
        ( concatenate-leq-eq-ℕ d
          ( leq-add-ℕ' d (k *ℕ d)) p))
```

<!-- rosetta-agda-block: proposition-7.4.6-bounded-distance-congruence-adapted -->

```agda
abstract
  strict-upper-bound-dist-ℕ :
    (b x y : ℕ) → le-ℕ x b → le-ℕ y b → le-ℕ (dist-ℕ x y) b
  strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
  strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
  strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
    preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)

eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → cong-ℕ k x y → x ＝ y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)

eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → cong-ℕ k x y → x ＝ y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → cong-ℕ k (nat-Fin k x) (nat-Fin k y) → x ＝ y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin (succ-ℕ k)
    (eq-cong-le-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y)
      (strict-upper-bound-nat-Fin (succ-ℕ k) x)
      (strict-upper-bound-nat-Fin (succ-ℕ k) y) H)
```
<!-- rosetta-item-end: proposition-7.4.6 -->

## Theorem 7.4.7

<!-- rosetta-item: theorem-7.4.7; latex-label: thm:effective-mod-k -->

Consider a natural number `k`.
Then we have
```text
[x]_{k+1}=[y]_{k+1} ↔ x≡ ymod k+1,
```
for any `x,y:ℕ`.

### Proof

<!-- rosetta-item: subheading-7.4-proof-4 -->

*Proof.* First note that, since `nat-Fin` is injective by Proposition 7.3.6, we have
```text
[x]_{k+1}=[y]_{k+1} ↔ nat-Fin[x]_{k+1}=nat-Fin[y]_{k+1}.
```
Since the inequalities `nat-Fin[x]_{k+1}<k+1` and `nat-Fin[y]_{k+1}<k+1` hold by Lemma 7.3.5, it follows by Proposition 7.4.6 that
```text
nat-Fin[x]_{k+1}=nat-Fin[y]_{k+1}↔ nat-Fin[x]_{k+1}≡nat-Fin[y]_{k+1}mod k+1.
```
The latter condition is by Proposition 7.4.5 equivalent to the condition that `x≡ ymod k+1`. ◻

<!-- rosetta-agda-block: theorem-7.4.7-effectiveness-mod-successor-adapted -->

```agda
concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  cong-ℕ k x1 x2 → x2 ＝ x3 → cong-ℕ k x3 x4 → cong-ℕ k x1 x4
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ k x y z K H

cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → mod-succ-ℕ k x ＝ mod-succ-ℕ k y → cong-ℕ (succ-ℕ k) x y
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    (symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
      (cong-nat-mod-succ-ℕ k x))
    (ap (nat-Fin (succ-ℕ k)) p)
    (cong-nat-mod-succ-ℕ k y)

eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → cong-ℕ (succ-ℕ k) x y → mod-succ-ℕ k x ＝ mod-succ-ℕ k y
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x) (mod-succ-ℕ k y)
    (transitive-cong-ℕ (succ-ℕ k)
      (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
      (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
      (transitive-cong-ℕ (succ-ℕ k) x y
        (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
        (symmetric-cong-ℕ (succ-ℕ k)
          (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)) y
          (cong-nat-mod-succ-ℕ k y)) H)
      (cong-nat-mod-succ-ℕ k x))
```
<!-- rosetta-item-end: theorem-7.4.7 -->

## Theorem 7.4.8

<!-- rosetta-item: theorem-7.4.8; latex-label: thm:issec-nat-Fin -->

For any `x:Fin{k+1}` there is an identification
```text
[nat-Fin(x)]_{k+1}=x.
```
In other words, the map `[_]_{k+1}:ℕ→ Fin{k+1}` is split surjective.

### Proof

<!-- rosetta-item: subheading-7.4-proof-5 -->

*Proof.* Since `nat-Fin:Fin{k+1}→ℕ` is injective by Proposition 7.3.6, it suffices to show that
```text
nat-Fin[nat-Fin(x)]_{k+1}=nat-Fin(x).
```
Now observe that `nat-Fin[nat-Fin(x)]_{k+1}<k+1` and `nat-Fin(x)<k+1`.
By Proposition 7.4.6 it therefore suffices to show that
```text
nat-Fin[nat-Fin(x)]_{k+1}≡nat-Fin(x)mod{k+1}.
```
This fact is an instance of Proposition 7.4.5. ◻

<!-- rosetta-agda-block: theorem-7.4.8-split-surjectivity-mod-successor -->

```agda
is-section-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mod-succ-ℕ k (nat-Fin (succ-ℕ k) x) ＝ x
is-section-nat-Fin k x =
  is-injective-nat-Fin (succ-ℕ k)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))
      ( nat-Fin (succ-ℕ k) x)
      ( strict-upper-bound-nat-Fin
        ( succ-ℕ k)
        ( mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))
      ( strict-upper-bound-nat-Fin (succ-ℕ k) x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))

is-split-surjective-mod-succ-ℕ :
  (k : ℕ) → is-split-surjective (mod-succ-ℕ k)
pr1 (is-split-surjective-mod-succ-ℕ k x) = nat-Fin (succ-ℕ k) x
pr2 (is-split-surjective-mod-succ-ℕ k x) = is-section-nat-Fin k x
```
<!-- rosetta-item-end: theorem-7.4.8 -->
