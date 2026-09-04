# Section 11.3 Equality on the natural numbers

```agda
module section-11-3-equality-on-the-natural-numbers where
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

<!-- rosetta-item-end: theorem-11.3.1 -->
