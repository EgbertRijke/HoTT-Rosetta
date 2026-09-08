# Section 6.4 Peano's seventh and eighth axioms

```agda
module section-6-4-peanos-seventh-and-eighth-axioms where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-3-observational-equality-of-the-natural-numbers
```

<!-- rosetta-item: section-6.4 -->

Using the observational equality of `ℕ`, we can prove Peano’s seventh and eighth axioms.
In his *Arithmetices Principia* , the natural numbers are based at `1`, but today it is customary to have the natural numbers based at `0`.
Adapting for this, the seventh and eighth axioms assert that

1.  For any two natural numbers `m` and `n`, we have
```text
(m=n)↔ (succ-ℕ(m)=succ-ℕ(n)).
```

2.  For any natural number `n`, we have `0≠succ-ℕ(n)`.

## Theorem 6.4.1

<!-- rosetta-item: theorem-6.4.1; latex-label: thm:is-injective-succ-N -->

For any two natural numbers `m` and `n`, we have
```text
(m=n)↔ (succ-ℕ(m)=succ-ℕ(n)).
```

### Proof

<!-- rosetta-item: subheading-6.4-proof -->

*Proof.* The forward implication is given by the action on paths of the successor function
```text
ap{succ-ℕ}:(m=n)→(succ-ℕ(m)=succ-ℕ(n)).
```
The direction of interest is the converse, which asserts that the successor function is injective.

Here we use Proposition 6.3.3, which asserts that `(m=n)↔ Eq-ℕ(m,n)` for all `m,n:ℕ`.
Furthermore, we have `Eq-ℕ(succ-ℕ(m),succ-ℕ(n))≐ Eq-ℕ(m,n)`.
Therefore, we obtain
<!-- rosetta-diagram: d1c529ba013b; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
  [(succ-ℕ(m)=succ-ℕ(n))]  ---->  [(m=n)]
             |                       |
[Eq-ℕ(succ-ℕ(m),succ-ℕ(n))]---->[Eq-ℕ(m,n)]

Arrows:
- (succ-ℕ(m)=succ-ℕ(n)) --unlabeled--> (m=n)
- (succ-ℕ(m)=succ-ℕ(n)) --unlabeled--> Eq-ℕ(succ-ℕ(m),succ-ℕ(n))
- Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) --id--> Eq-ℕ(m,n)
- Eq-ℕ(m,n) --unlabeled--> (m=n)
```
and we define the function `(succ-ℕ(m)=succ-ℕ(n))→(m=n)` as the composite of the maps going down, then right, and then up. ◻

<!-- rosetta-agda-block: section-6-4-peanos-seventh-and-eighth-axioms-block-46 -->

```agda
ap-succ-ℕ : {m n : ℕ} → m ＝ n → succ-ℕ m ＝ succ-ℕ n
ap-succ-ℕ = ap succ-ℕ
```

<!-- rosetta-agda-block: section-6-4-peanos-seventh-and-eighth-axioms-block-63 -->

```agda
is-injective-succ-ℕ :
  {m n : ℕ} → succ-ℕ m ＝ succ-ℕ n → m ＝ n
is-injective-succ-ℕ {m} {n} p = eq-Eq-ℕ m n (Eq-eq-ℕ p)

peano-7-ℕ :
  (m n : ℕ) →
  ((m ＝ n) → succ-ℕ m ＝ succ-ℕ n) ×
  ((succ-ℕ m ＝ succ-ℕ n) → m ＝ n)
peano-7-ℕ m n = ap-succ-ℕ , is-injective-succ-ℕ
```
<!-- rosetta-item-end: theorem-6.4.1 -->

## Theorem 6.4.2

<!-- rosetta-item: theorem-6.4.2; latex-label: prp:zero-one -->

For any natural number `n`, we have `0≠succ-ℕ(n)`.

### Proof

<!-- rosetta-item: subheading-6.4-proof-2 -->

*Proof.* By Proposition 6.3.3 it follows that there is a family of maps
```text
(0=n)→ Eq-ℕ(0,n).
```
indexed by `n:ℕ`.
Since `Eq-ℕ(0,succ-ℕ(n))≐empty` it follows that
```text
(0=succ-ℕ(n))→ empty,
```
which is precisely the claim. ◻

<!-- rosetta-agda-block: section-6-4-peanos-seventh-and-eighth-axioms-block-97 -->

```agda
is-nonzero-succ-ℕ : (n : ℕ) → succ-ℕ n ＝ zero-ℕ → empty
is-nonzero-succ-ℕ n ()

neq-zero-succ-ℕ : (n : ℕ) → zero-ℕ ＝ succ-ℕ n → empty
neq-zero-succ-ℕ n p = Eq-eq-ℕ p

peano-8-ℕ : (n : ℕ) → zero-ℕ ＝ succ-ℕ n → empty
peano-8-ℕ = neq-zero-succ-ℕ
```
<!-- rosetta-item-end: theorem-6.4.2 -->
