# Section 13.5 The strong induction principle of ℕ

```agda
module section-13-5-the-strong-induction-principle-of-the-natural-numbers where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-6-3-order-natural-numbers
open import exercise-7-3-divisibility-factorials
open import section-9-2-bi-invertible-maps
open import section-12-1-propositions
open import section-12-3-sets
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-12-4-coproduct-truncation
open import exercise-9-1-groupoid-operations-equivalences
```

<!-- rosetta-item: section-13.5 -->

In the final application of the function extensionality principle we prove the strong induction principle for the type of natural numbers.
Function extensionality is used to derive the computation rules of the strong induction principle.

## Theorem 13.5.1

<!-- rosetta-item: theorem-13.5.1; latex-label: thm:strong-ind-N -->

Consider a type family `P` over `ℕ` equipped with
```text
p_0 : P(0)
p_S : Π(n:ℕ) (Π(m:ℕ) (m≤ n)→ P(m))→ P(n+1).
```
Then there is a dependent function
```text
strong-ind-ℕ(p_0,p_S) : Π(n:ℕ) P(n)
```
that satisfies the following computation rules
```text
strong-ind-ℕ(p_0,p_S,0) = p_0
strong-ind-ℕ(p_0,p_S,n+1) = p_S(n,(λ m. λ p. strong-ind-ℕ(p_0,p_S,m))).
```

<!-- rosetta-item-end: theorem-13.5.1 -->

In order to construct `strong-ind-ℕ(p_0,p_S)`, we first define the type family `P̃` over `ℕ` by
```text
P̃(n)≔ Π(m:ℕ) (m≤ n)→ P(m).
```

<!-- rosetta-agda-block: section-13.5-bounded-family -->

```agda
□-≤-ℕ : {l : Level} → (ℕ → Type l) → ℕ → Type l
□-≤-ℕ P n = (m : ℕ) → (m ≤-ℕ n) → P m
```

The idea is then to first use `p_0` and `p_S` to construct
```text
p̃_0 : P̃(0)
p̃_S :Π(n:ℕ) P̃(n)→P̃(n+1).
```
The ordinary induction principle of `ℕ` then gives a function
```text
ind-ℕ(p̃_0,p̃_S):Π(n:ℕ) P̃(n),
```
which can be used to define a function `Π(n:ℕ) P(n)`.

Before we start by the proof of Theorem 13.5.1 we state two lemmas in which we construct `p̃_0` and `p̃_S` with computation rules of their own.
We will assume a type family `P` over `ℕ` equipped with
```text
p_0 : P(0)
p_S : Π(n:ℕ) P̃(n) → P(n+1),
```
as in the hypotheses of Theorem 13.5.1.

## Lemma 13.5.2

<!-- rosetta-item: lemma-13.5.2 -->

There is an element `p̃_0:P̃(0)` that satisfies the judgmental equality
```text
p̃_0(0,p)≐ p_0
```
for any `p:0≤ 0`.

### Proof

<!-- rosetta-item: subheading-13.5-proof -->

*Proof.* The fact that we have such a dependent function `p̃_0` follows immediately by induction on `m` and `p:m≤ 0`. ◻

<!-- rosetta-agda-block: lemma-13.5.2-bounded-base -->

```agda
zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  zero-strong-ind-ℕ P p0 zero-ℕ t ＝ p0
eq-zero-strong-ind-ℕ P p0 t = refl
```
<!-- rosetta-item-end: lemma-13.5.2 -->

## Lemma 13.5.3

<!-- rosetta-item: lemma-13.5.3; latex-label: lem:succ-strong-ind-N -->

There is a function
```text
p̃_S : Π(n:ℕ) P̃(n)→P̃(n+1)
```
equipped with

1.  an identification
```text
p̃_S(n,H,m,p) = H(m,q)
```
    for every `H:P̃(n)` and every `p:m≤ n+1` and `q:m≤ n`, and

2.  an identification
```text
p̃_S(n,H,n+1,p) = p_S(n,H)
```
    for every `p:n+1≤ n+1`.

### Proof

<!-- rosetta-item: subheading-13.5-proof-2 -->

*Proof.* To define the function `p̃_S(n,H)`, note that there is a function
```text
f : (m≤ n+1)→ (m≤ n)+(m=n+1)(*)
```
which can be defined by induction on `n` and `m`.
Using the fact that the domain and codomain of this map are both propositions, this function is easily seen to be an equivalence.
Therefore we define first a function
```text
h(n,H) :Π(m:ℕ) ((m≤ n)+(m=n+1))→ P(m)
```
by case analysis on `x:(m≤ n)+(m=n+1)`.
There are two cases to consider: one where we have `q:m≤ n`, and one where we have `q:m=n+1`.
Note that in the second case it suffices to make a definition for `q≐ refl`.
Therefore we define
```text
h(n,H,m,x) =
cases {
H(m,q) if x≐inl(q)
p_S(n,H) if x≐inr(refl).
}
```
Now we define `p̃_S` by
```text
p̃_S(n,H,m,p)≔ h(n,H,m,f(p)),
```
where `f:(m≤ n+1)→ (m≤ n)+(m=n+1)` is the map we mentioned in (\*).

To construct the identifications claimed in (i) and (ii), note that there is an equivalence
```text
(p̃_S(n,H,m,p)=y)≃ (h(n,H,m,x)=y),
```
for any `y:P(m)`.
This equivalence is obtained from the fact that `f(p)=x` for any `x:(m≤ n)+(m=n+1)`, i.e., the fact that `(m≤ n)+(m=n+1)` is a proposition.
Now the identifications in (i) and (ii) are obtained as a simple consequence of the computation rule for coproducts. ◻

<!-- rosetta-agda-block: lemma-13.5.3-order-is-a-proposition -->

```agda
abstract
  is-prop-leq-ℕ :
    (m n : ℕ) → is-prop (leq-ℕ m n)
  is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
  is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
  is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n
```

<!-- rosetta-agda-block: lemma-13.5.3-case-type-is-a-proposition -->

```agda
is-prop-leq-succ-cases :
  (m n : ℕ) → is-prop ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
is-prop-leq-succ-cases m n =
  is-prop-coproduct
    ( λ q α →
      contradiction-leq-ℕ n n (refl-leq-ℕ n)
        ( concatenate-eq-leq-ℕ n (inv α) q))
    ( is-prop-leq-ℕ m n)
    ( is-set-ℕ m (succ-ℕ n))
```

<!-- rosetta-agda-block: lemma-13.5.3-case-splitting-equivalence -->

```agda
equiv-leq-succ-cases :
  (m n : ℕ) → (m ≤-ℕ succ-ℕ n) ≃ ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
equiv-leq-succ-cases m n =
  equiv-iff-is-prop
    ( is-prop-leq-ℕ m (succ-ℕ n))
    ( is-prop-leq-succ-cases m n)
    ( decide-leq-succ-ℕ m n)
    ( rec-coproduct
      ( preserves-leq-succ-ℕ m n)
      ( leq-eq-ℕ m (succ-ℕ n)))
```

<!-- rosetta-agda-block: lemma-13.5.3-case-independence -->

```agda
eq-cases-leq-succ :
  (m n : ℕ) (p : m ≤-ℕ succ-ℕ n) (x : (m ≤-ℕ n) + (m ＝ succ-ℕ n)) →
  decide-leq-succ-ℕ m n p ＝ x
eq-cases-leq-succ m n p x =
  eq-is-prop' (is-prop-leq-succ-cases m n) (decide-leq-succ-ℕ m n p) x
```

<!-- rosetta-agda-block: lemma-13.5.3-bounded-successor -->

```agda
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p)
```

<!-- rosetta-agda-block: lemma-13.5.3-bounded-successor-laws -->

```agda
cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : (leq-ℕ m k) + (m ＝ succ-ℕ k)) →
  (q : leq-ℕ m k) →
  ( cases-succ-strong-ind-ℕ P pS k H m c) ＝
  ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (eq-is-prop (is-prop-leq-ℕ m k))
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso (contradiction-leq-ℕ k k (refl-leq-ℕ k) (concatenate-eq-leq-ℕ k (inv α) q))

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  ( succ-strong-ind-ℕ P pS k H m p) ＝
  ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p) q

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : (leq-ℕ (succ-ℕ k) k) + (succ-ℕ k ＝ succ-ℕ k)) →
  ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c)) ＝
  ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso (contradiction-leq-ℕ k k (refl-leq-ℕ k) p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap
    ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
    ( eq-is-prop' (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p)) ＝
  ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (decide-leq-succ-ℕ (succ-ℕ k) k p)
```

<!-- rosetta-agda-block: lemma-13.5.3-case-evaluation-identifications -->

```agda
equiv-identifications-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l)
  (pS : (n : ℕ) → □-≤-ℕ P n → P (succ-ℕ n))
  (n : ℕ) (H : □-≤-ℕ P n) (m : ℕ) (p : m ≤-ℕ succ-ℕ n)
  (x : (m ≤-ℕ n) + (m ＝ succ-ℕ n)) (y : P m) →
  (succ-strong-ind-ℕ P pS n H m p ＝ y) ≃
  (cases-succ-strong-ind-ℕ P pS n H m x ＝ y)
equiv-identifications-succ-strong-ind-ℕ P pS n H m p x y =
  equiv-inv-concat
    ( ap (cases-succ-strong-ind-ℕ P pS n H m)
      ( eq-cases-leq-succ m n p x))
    ( y)
```
<!-- rosetta-item-end: lemma-13.5.3 -->

We are now ready to finish the proof of Theorem 13.5.1.

### Proof

<!-- rosetta-item: subheading-13.5-proof-3 -->

*Proof of Theorem 13.5.1.* Using `p̃_0` and `p̃_S`, we obtain by induction on `n` a function
```text
s̃:Π(n:ℕ) P̃(n)
```
satisfying the computation rules
```text
s̃(0) ≐ p̃_0
s̃(n+1) ≐ p̃_S(n,s̃(n)).
```

<!-- rosetta-agda-block: theorem-13.5.1-bounded-induction -->

```agda
induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ P p0 pS zero-ℕ = p0
induction-strong-ind-ℕ P p0 pS (succ-ℕ n) =
  pS n (induction-strong-ind-ℕ P p0 pS n)

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (p0 : □-≤-ℕ P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  ( induction-strong-ind-ℕ P p0 pS (succ-ℕ n)) ＝
  ( pS n (induction-strong-ind-ℕ P p0 pS n))
computation-succ-strong-ind-ℕ P p0 pS n = refl
```

Now we define
```text
strong-ind-ℕ(p_0,p_S,n) ≔ s̃(n,n,refl-≤-ℕ(n)),
```
where `refl-≤-ℕ(n):n≤ n` is the proof of reflexivity of `≤`.

<!-- rosetta-agda-block: theorem-13.5.1-diagonal-evaluation -->

```agda
ε-□-≤-ℕ :
  {l : Level} {P : ℕ → Type l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ f n = f n n (refl-leq-ℕ n)
```


It remains to show that `strong-ind-ℕ` satisfies the computation rules of the strong induction principle.
The identification that computes `strong-ind-ℕ` at `0` is easy to obtain, because we have the judgmental equalities
```text
strong-ind-ℕ(p_0,p_S,0) ≐ s̃(0,0,refl-≤-ℕ(0))
≐ p̃_{0}(0,refl-≤-ℕ(0))
≐ p_0.
```
To construct the identification that computes `strong-ind-ℕ` at a successor, we start by a similar computation:
```text
strong-ind-ℕ(p_0,p_S,n+1) ≐ s̃(n+1,n+1,refl-≤-ℕ(n+1))
≐ p̃_S(n,s̃(n),n+1,refl-≤-ℕ(n+1))
= p_S(n,s̃(n)).
```
The last identification is obtained from Lemma 13.5.3 (ii).
Therefore we see that, in order to show that
```text
p_S(n,s̃(n))=p_S(n,(λ m. λ p. s̃(m,m,refl-≤-ℕ(m)))),
```
we need to prove that
```text
s̃(n)=λ m. λ p. s̃(m,m,refl-≤-ℕ(m)).
```
Here we apply function extensionality, so it suffices to show that
```text
s̃(n,m,p)=s̃(m,m,refl-≤-ℕ(m))
```
for every `m:ℕ` and `p:m≤ n`.
We proceed by induction on `n:ℕ`.
The base case is trivial.
For the inductive step, we note that
```text
s̃(n+1,m,p)=p̃_S(n,s̃(n),m,p)=cases {
s̃(n,m,p) if m≤ n
p_S(n,s̃(n)) if m=n+1.
}
```
Therefore it follows by the inductive hypothesis that
```text
s̃(n+1,m,p)=s̃(m,m,refl-≤-ℕ(m))
```
if `m≤ n` holds.
In the remaining case, where `m=n+1`, note that we have
```text
s̃(n+1,n+1,refl-≤-ℕ(n+1)) = p̃_S(n,s̃(n),n+1,refl-≤-ℕ(n+1))
= p_S(n,s̃(n)).
```
Therefore we see that we also have an identification
```text
s̃(n+1,m,p)=s̃(m,m,refl-≤-ℕ(m))
```
when `m=n+1`.
This completes the proof of the computation rules for the strong induction principle of `ℕ`. ◻

<!-- rosetta-agda-block: theorem-13.5.1-strong-induction-and-computations -->

```agda
strong-ind-ℕ :
  {l : Level} → (P : ℕ → Type l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ P p0 pS =
  ε-□-≤-ℕ
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

compute-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  strong-ind-ℕ P p0 pS zero-ℕ ＝ p0
compute-zero-strong-ind-ℕ P p0 pS = refl

cases-eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
      ( λ k z m₁ z₁ →
        cases-succ-strong-ind-ℕ P pS k z m₁ (decide-leq-succ-ℕ m₁ k z₁))
      n m p) ＝
    ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  ( succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n) m p) ＝
  ( strong-ind-ℕ P p0 pS m)
cases-eq-compute-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-compute-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p₁))
          n)
        ( succ-ℕ n))
      ( eq-cases-leq-succ (succ-ℕ n) n (refl-leq-ℕ n) (inr refl))))

eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
    ( λ k z m₁ z₁ →
      cases-succ-strong-ind-ℕ P pS k z m₁ (decide-leq-succ-ℕ m₁ k z₁))
    n m p) ＝
  ( strong-ind-ℕ P p0 pS m)
eq-compute-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ _ = refl
eq-compute-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-compute-succ-strong-ind-ℕ P p0 pS n
    ( eq-compute-succ-strong-ind-ℕ P p0 pS n) m p
    ( decide-leq-succ-ℕ m n p)

compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  strong-ind-ℕ P p0 pS (succ-ℕ n) ＝ pS n (λ m p → strong-ind-ℕ P p0 pS m)
compute-succ-strong-ind-ℕ P p0 pS n =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( refl-leq-ℕ n)) ∙
  ( ap
    ( pS n)
    ( eq-htpy (eq-htpy ∘ eq-compute-succ-strong-ind-ℕ P p0 pS n)))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → Type l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( h zero-ℕ ＝ p0) ×
      ( (n : ℕ) → h (succ-ℕ n) ＝ pS n (λ m p → h m)))
pr1 (total-strong-ind-ℕ P p0 pS) = strong-ind-ℕ P p0 pS
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-zero-strong-ind-ℕ P p0 pS
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-succ-strong-ind-ℕ P p0 pS
```
