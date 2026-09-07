# Section 11.3 Equality on the natural numbers

```agda
module section-11-3-equality-on-the-natural-numbers where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-3-observational-equality-of-the-natural-numbers
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-11-2-the-fundamental-theorem
```

<!-- rosetta-item: section-11.3 -->

As a first application of the fundamental theorem of identity types, we characterize the identity type of the natural numbers.
We will use the observational equality `Eq-ℕ` on `ℕ`.
Recall from Definition 6.3.1 that `Eq-ℕ` is defined by
```text
Eq-ℕ(0,0) ≔ unit Eq-ℕ(0,n+1) ≔ empty
Eq-ℕ(m+1,0) ≔ empty Eq-ℕ(m+1,n+1) ≔ Eq-ℕ(m,n).
```
This relation is an equivalence relation.
In particular, the reflexivity term `refl-Eq-ℕ(m):Eq-ℕ(m,m)` is defined inductively by
```text
refl-Eq-ℕ(0) ≔ ⋆
refl-Eq-ℕ(m+1) ≔ refl-Eq-ℕ(m).
```
Using the reflexivity term, we obtain a canonical map
```text
(m=n)→ Eq-ℕ(m,n)
```
for every `m,n:ℕ`.

## Theorem 11.3.1

<!-- rosetta-item: theorem-11.3.1; latex-label: thm:eq_nat -->

For each `m,n:ℕ`, the canonical map
```text
(m=n)→ Eq-ℕ(m,n)
```
is an equivalence.

### Proof

<!-- rosetta-item: subheading-11.3-proof -->

*Proof.* By Theorem 11.2.2 it suffices to show that the type
```text
Σ(n:ℕ) Eq-ℕ(m,n)
```
is contractible, for each `m:ℕ`.
The center of contraction is defined to be `(m,refl-Eq-ℕ(m))`.

The contraction
```text
γ(m):Π(n:ℕ) Π(e:Eq-ℕ(m,n)) (m,refl-Eq-ℕ(m))=(n,e)
```
is defined for each `m` by induction on `m,n:ℕ`.
In the base case we define
```text
γ(0,0,⋆)≔ refl.
```
If one of `m` and `n` is zero and the other is a successor, then the type `Eq-ℕ(m,n)` is empty, so the desired path can be obtained via the induction principle of the empty type.

The inductive step remains, in which we have to define the identification
```text
γ(m+1,n+1,e):(m+1,refl-Eq-ℕ(m+1))=(n+1,e)
```
for each `m,n:ℕ` equipped with `e:Eq-ℕ(m,n)`.
We first observe that there is a map
<!-- rosetta-diagram: 0eed2b2bdb83; review: pending -->

*Linear diagram (automatic draft).*

```text
[(Σ(n:ℕ) Eq-ℕ(m,n))]---->[(Σ(n:ℕ) Eq-ℕ(m+1,n))]

Arrows:
- (Σ(n:ℕ) Eq-ℕ(m,n)) --f--> (Σ(n:ℕ) Eq-ℕ(m+1,n))
```
given by `(n,e)↦ (n+1,e)`.
With this definition of `f` we have
```text
f(m,refl-Eq-ℕ(m))≐ (m+1,refl-Eq-ℕ(m+1)).
```
Therefore we can define
```text
γ(m+1,n+1,e)≔ ap_{f}(γ(m,n,e)).
```
 ◻

<!-- rosetta-agda-block: theorem-11.3.1-equality-natural-numbers -->

```agda
map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (n , e)) = succ-ℕ n
pr2 (map-total-Eq-ℕ m (n , e)) = e

is-torsorial-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
pr1 (pr1 (is-torsorial-Eq-ℕ m)) = m
pr2 (pr1 (is-torsorial-Eq-ℕ m)) = refl-Eq-ℕ m
pr2 (is-torsorial-Eq-ℕ zero-ℕ) (zero-ℕ , _) = refl
pr2 (is-torsorial-Eq-ℕ (succ-ℕ m)) (succ-ℕ n , e) =
  ap (map-total-Eq-ℕ m) (pr2 (is-torsorial-Eq-ℕ m) (pair n e))

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id
    ( is-torsorial-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)
```
<!-- rosetta-item-end: theorem-11.3.1 -->
