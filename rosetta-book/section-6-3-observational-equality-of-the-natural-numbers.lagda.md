# Section 6.3 Observational equality of the natural numbers

```agda
module section-6-3-observational-equality-of-the-natural-numbers where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
```

Using universes, we can define many relations on the natural numbers.
We give here the example of *observational equality* of `ℕ`.
The idea of observational equality is that, if we want to prove that `m` and `n` are observationally equal, we may do so by looking at `m` and `n`:

1. If both `m` and `n` are `0`, then they are observationally equal.

2. If one of them is `0` and the other is a successor, then they are not observationally equal.

3. If both `m` and `n` are successors, say `m≐succ-ℕ(m')` and `n≐ succ-ℕ(n')`, then `m` and `n` are observationally equal if and only if their predecessors `m'` and `n'` are observationally equal.

Thus, observational equality is an inductively defined relation, which gives us an algorithm for checking equality on `ℕ`.
Indeed, it can be used to show that equality of natural numbers is *decidable*, i.e., there is a program that decides for any two natural numbers `m` and `n` whether they are equal or not.

## Definition 6.3.1

We define the **observational equality** of `ℕ` as binary relation `Eq-ℕ:ℕ→(ℕ→𝒰_0)` satisfying
```text
Eq-ℕ(0,0) ≐ unit Eq-ℕ(succ-ℕ(n),0) ≐ empty
Eq-ℕ(0,succ-ℕ(n)) ≐ empty Eq-ℕ(succ-ℕ(n),succ-ℕ(m)) ≐ Eq-ℕ(n,m).
```

### Construction

We define `Eq-ℕ` by double induction on `ℕ`.
By the first application of induction it suffices to provide
```text
E_0 : ℕ→𝒰_0
E_S : ℕ→ ((ℕ→𝒰_0)→(ℕ→𝒰_0))
```
We define `E_0` by induction, taking `E_{00}≔ unit` and `E_{0S}(n,X,m)≔ empty`.
The resulting family `E_0` satisfies
```text
E_0(0) ≐ unit
E_0(succ-ℕ(n)) ≐ empty.
```
We define `E_S` by induction, taking `E_{S0}≔ empty` and `E_{SS}(n,X,m)≔ X(m)`.
The resulting family `E_S` satisfies
```text
E_S(n,X,0) ≐ empty
E_S(n,X,succ-ℕ(m)) ≐ X(m)
```
Therefore we have by the computation rule for the first induction that the judgmental equality
```text
Eq-ℕ(0,m) ≐ E_0(m)
Eq-ℕ(succ-ℕ(n),m) ≐ E_S(n,Eq-ℕ(n),m)
```
holds, from which the judgmental equalities in the statement of the definition follow.

```agda
Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n
```

The observational equality of the natural numbers is important because it can be used to prove equalities and negations of equalities.
Proposition 6.3.3 enables us to do so.

## Lemma 6.3.2

Observational equality of `ℕ` is a reflexive relation, i.e., we have
```text
refl-Eq-ℕ : Π(n:ℕ) Eq-ℕ(n,n).
```

### Proof

*Proof.* The function `refl-Eq-ℕ` is defined by induction on `n`, taking
```text
refl-Eq-ℕ(0) ≔ ⋆
refl-Eq-ℕ(succ-ℕ(n)) ≔ refl-Eq-ℕ(n).
```
 ◻

```agda
refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n
```

## Proposition 6.3.3

For any two natural numbers `m` and `n`, we have
```text
(m=n)↔ Eq-ℕ(m,n).
```

### Proof

*Proof.* The function `(m=n)→Eq-ℕ(m,n)` is defined by the induction principle of identity types, using the reflexivity of `Eq-ℕ`.

The converse `Eq-ℕ(m,n)→ (m=n)` is defined by induction on `m` and `n`.
If both `m` and `n` are zero, we have `refl:0=0`.
If one of `m` and `n` is zero and the other is a successor, then `Eq-ℕ(m,n)` is empty and we have a function `empty→ (m=n)` by the induction principle of the empty type.
In the inductive step, suppose we have a function `f:Eq-ℕ(m,n)→ (m=n)`.
Then we can define a function
```text
Eq-ℕ(succ-ℕ(m),succ-ℕ(n))→ (succ-ℕ(m)=succ-ℕ(n))
```
as the composite

*Square-shaped diagram (automatic draft).*

```text
[Eq-ℕ(succ-ℕ(m),succ-ℕ(n))]---->[(succ-ℕ(m)=succ-ℕ(n))]
             |                             |
        [Eq-ℕ(m,n)]        ---->        [(m=n)]

Arrows:
- Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) --unlabeled--> (succ-ℕ(m)=succ-ℕ(n))
- Eq-ℕ(succ-ℕ(m),succ-ℕ(n)) --id--> Eq-ℕ(m,n)
- Eq-ℕ(m,n) --f--> (m=n)
- (m=n) --ap{succ-ℕ}--> (succ-ℕ(m)=succ-ℕ(n))
```
Note that the map on the left is the identity function, because we have the judgmental equality `Eq-ℕ(succ-ℕ(m),succ-ℕ(n))≐Eq-ℕ(m,n)` by definition of `Eq-ℕ`. ◻

```agda
Eq-eq-ℕ : {x y : ℕ} → x ＝ y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → x ＝ y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)
```
