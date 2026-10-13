# Section 17.6 The binomial types

```agda
module section-17-6-the-binomial-types where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import section-16-3-finite-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
```

To wrap up this section on univalence, we will use the univalence axiom to construct for any two types `A` and `B` a type `(A choose B)` that has properties similar to the binomial coefficients `(n choose k)`.
Indeed, we will show that if `A` is an `n`-element type and `B` is a `k`-element type, then `(A choose B)` is an `(n choose k)`-element type.
The binomial types are defined using decidable embeddings.

## Definition 17.6.1

A map `f : A → B` is said to be **decidable** if it comes equipped with an element of type

```text
  is-decidable(f) ≔ Π(b : B) is-decidable(fib(f,b)).
```

We will write `A ↪ᵈ B` for the type of **decidable embeddings** from `A` to `B`, i.e., for the type of embeddings that are also decidable maps.

## Definition 17.6.2

Consider a type `A` and a universe `𝒰`.
We define the **connected component** of `𝒰` at `A` by

```text
  𝒰_A ≔ Σ(X : 𝒰) ‖A ≃ X‖.
```

```agda
component-UU-Level :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
component-UU-Level l1 A = type-subtype (mere-equiv-Prop {l2 = l1} A)

type-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} → component-UU-Level l1 A → UU l1
type-component-UU-Level X = pr1 X

abstract
  mere-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    mere-equiv A (type-component-UU-Level X)
  mere-equiv-component-UU-Level X = pr2 X

component-UU :
  {l1 : Level} (A : UU l1) → UU (lsuc l1)
component-UU {l1} A = component-UU-Level l1 A

type-component-UU : {l1 : Level} {A : UU l1} (X : component-UU A) → UU l1
type-component-UU X = type-component-UU-Level X

abstract
  mere-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    mere-equiv A (type-component-UU X)
  mere-equiv-component-UU X = mere-equiv-component-UU-Level X

equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) → UU l1
equiv-component-UU-Level X Y =
  type-component-UU-Level X ≃ type-component-UU-Level Y

id-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
  equiv-component-UU-Level X X
id-equiv-component-UU-Level X = id-equiv

equiv-eq-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} {X Y : component-UU-Level l1 A} →
  X ＝ Y → equiv-component-UU-Level X Y
equiv-eq-component-UU-Level {X = X} refl =
  id-equiv-component-UU-Level X

abstract
  is-torsorial-equiv-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X : component-UU-Level l1 A) →
    is-torsorial (equiv-component-UU-Level X)
  is-torsorial-equiv-component-UU-Level X =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv (type-component-UU-Level X))
      ( λ Y → is-prop-mere-equiv _ Y)
      ( type-component-UU-Level X)
      ( id-equiv)
      ( mere-equiv-component-UU-Level X)

abstract
  is-equiv-equiv-eq-component-UU-Level :
    {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
    is-equiv (equiv-eq-component-UU-Level {X = X} {Y})
  is-equiv-equiv-eq-component-UU-Level X =
    fundamental-theorem-id
      ( is-torsorial-equiv-component-UU-Level X)
      ( λ Y → equiv-eq-component-UU-Level {X = X} {Y})

eq-equiv-component-UU-Level :
  {l1 l2 : Level} {A : UU l2} (X Y : component-UU-Level l1 A) →
  equiv-component-UU-Level X Y → X ＝ Y
eq-equiv-component-UU-Level X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-component-UU-Level X Y)

equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) → UU l1
equiv-component-UU X Y = equiv-component-UU-Level X Y

id-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X : component-UU A) → equiv-component-UU X X
id-equiv-component-UU X = id-equiv-component-UU-Level X

equiv-eq-component-UU :
  {l1 : Level} {A : UU l1} {X Y : component-UU A} →
  X ＝ Y → equiv-component-UU X Y
equiv-eq-component-UU p = equiv-eq-component-UU-Level p

abstract
  is-torsorial-equiv-component-UU :
    {l1 : Level} {A : UU l1} (X : component-UU A) →
    is-torsorial (equiv-component-UU X)
  is-torsorial-equiv-component-UU X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-component-UU :
    {l1 : Level} {A : UU l1} (X Y : component-UU A) →
    is-equiv (equiv-eq-component-UU {X = X} {Y})
  is-equiv-equiv-eq-component-UU X Y =
    is-equiv-equiv-eq-component-UU-Level X Y

eq-equiv-component-UU :
  {l1 : Level} {A : UU l1} (X Y : component-UU A) →
  equiv-component-UU X Y → X ＝ Y
eq-equiv-component-UU X Y =
  eq-equiv-component-UU-Level X Y
```

## Example 17.6.3

Note that type `𝒰_{Fin{n}}` is the type `BS_n` of all `n`-element types.
Note also that if `A ≃ B`, then `𝒰_A ≃ 𝒰_B`.

## Definition 17.6.4

Consider two types `A` and `B` and a universe `𝒰` containing both `A` and `B`.
We define the **binomial type** `(A choose B)_𝒰` by

```text
  (A choose B)_𝒰 ≔ Σ(X : 𝒰_B) X ↪ᵈ A.
```

## Remark 17.6.5

We define the binomial types using decidable embeddings because the usual properties of binomial coefficients generalize most naturally under the extra assumption of decidability.
In particular the binomial theorem for types, which is stated as Exercise 17.14 and generalized in Exercise 18.14, rely on the use of decidable embeddings.

## Proposition 17.6.6

Consider two types `A` and `B`, and a universe `𝒰` containing both `A` and `B`.
Then we have an equivalence

```text
  (A choose B)_𝒰 ≃ Σ(P : A → decidable-Prop_𝒰) ‖B ≃ Σ(a : A) P(a)‖.
```

from the binomial type `(A choose B)_𝒰` to the type of decidable subtypes of `A` that are merely equivalent to `B`.

### Proof

This equivalence follows from Theorem 17.4.2, by which we have

```text
  (Σ(X : 𝒰) X ↪ᵈ A) ≃ (A → decidable-Prop_𝒰). ◻
```

## Remark 17.6.7

Combining Corollary 17.2.4 and Proposition 17.6.6, we obtain an equivalence

```text
  (A choose B)_𝒰 ≃ Σ(f : A →bool) ‖B ≃ Σ(a : A) f(a) = true‖.
```

for any universe `𝒰` that contains both `A` and `B`.
This equivalence is important, because the right hand side doesn’t depend on the universe `𝒰`.
Therefore we will simply write `(A choose B)` for `(A choose B)_𝒰`, if the universe `𝒰` contains both `A` and `B`.

## Lemma 17.6.8

For any two types `A` and `B`, we have equivalences

```text
          (∅ choose ∅) ≃ 1
      (A + 1 choose ∅) ≃ 1
      (∅ choose B + 1) ≃ ∅
  (A + 1 choose B + 1) ≃ (A choose B) + (A choose B + 1).
```

### Proof

For the first two equivalences, we prove that `(X choose ∅)` is contractible for any type `X`.
To see this, we first note that the type `𝒰_∅` is contractible.
Indeed, at the center of contraction we have the empty type, and any two types that are merely equivalent to the empty type are empty and hence equivalent.
Therefore it follows that

```text
  (X choose ∅) ≃ ∅ ↪ᵈ X.
```

The type of decidable embeddings `∅ ↪ᵈ X` is contractible, because the type `∅ → X` is contractible with the map `ex-falso : ∅ → X` at the center of contraction, which is of course a decidable embedding.

Next, the fact that the binomial type `(∅ choose B+1)` is empty follows from the fact that the type of maps `X → ∅` is empty for any type `X` merely equivalent to `B + 1`.

For the last equivalence we will use Proposition 17.6.6.
Using the universal property of `A + 1`, we see that

```text
  (A + 1 choose B + 1)
  ≃ Σ(P : A → decidable-Prop_𝒰) Σ(Q : decidable-Prop_𝒰) ‖(B + 1) ≃ Σ(a : A) P(a) + Q‖.
```

Using the fact that `decidable-Prop_𝒰 ≃ Fin{2}`, observe that we have an equivalence

```text
  Σ(Q : decidable-Prop_𝒰) ‖(B + 1) ≃ (Σ(a : A) P(a) + Q)‖
  ≃ ‖(B + 1) ≃ (Σ(a : A) P(a) + 1)‖ + ‖(B + 1) ≃ Σ(a : A) P(a)‖.
```

Furthermore, note that it follows from Proposition 16.2.1 that

```text
  ‖(B + 1) ≃ (Σ(a : A) P(a) + 1)‖ ≃ ‖B ≃ Σ(a : A) P(a)‖.
```

Thus we see that

```text
  (A + 1 choose B + 1)
  ≃ ( Σ(P : A → decidable-Prop_𝒰) ‖B ≃ Σ(a : A) P(a)‖)
    + (Σ(P : A → decidable-Prop_𝒰) ‖(B + 1) ≃ Σ(a : A) P(a)‖). ◻
```

## Theorem 17.6.9

If `A` and `B` are finite types of cardinality `n` and `k`, respectively, then the type `(A choose B)` is finite of cardinality `(n choose k)`.

### Proof

The claim that the type `(A choose B)` is finite of cardinality `(n choose k)` is a proposition, so we may assume `e : Fin{n} ≃ A` and `f : Fin{k} ≃ B`.
The claim now follows by induction on `n` and `k`, using Lemma 17.6.8. ◻

## Remark 17.6.10

It is perhaps remarkable that the type `Σ(X : 𝒰_B) X ↪ᵈ A` is a good generalisation of the binomial coefficients to types.
Note that when `A` and `B` are finite types of cardinality `n` and `k`, respectively, then the type `B ↪ᵈ A` has a factor `k!` too many elements.
When we seemingly enlarge it by the type `𝒰_B` of all types merely equivalent to `B`, it turns out that we obtain the correct generalisation of the binomial coefficients.

One reason why it works is that the identity type of `Σ(X : 𝒰_B) X ↪ᵈ A` is characterized, via the univalence axiom, by

```text
  ((X,f) = (Y,g)) ≃ Σ(e : X ≃ Y) f ~ g ∘ e.
```

Therefore it follows that for any two decidable embeddings `f, g : B ↪ᵈ A`, if `f` and `g` are the same up to a permutation on `B`, then we get an identification `(B,f) = (B,g)` in the type `Σ(X : 𝒰_B) X ↪ᵈ A`.

From a group theoretic perspective we may observe that the automorphism group `B ≃ B` acts freely on the set of decidable embeddings `B ↪ᵈ A`, and the type `Σ(X : 𝒰_B) X ↪ A` can be viewed as the type of orbits of that action.
Since this action of `Aut(B)` on `B ↪ᵈ A` is free, we see that the number of orbits is `1/k!` times the number of elements in `B ↪ᵈ A`.

## Supplement

### We characterize the identity type of `Type-With-Cardinality-ℕ`

```agda
equiv-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k : ℕ) →
  Type-With-Cardinality-ℕ l1 k →
  Type-With-Cardinality-ℕ l2 k →
  UU (l1 ⊔ l2)
equiv-Type-With-Cardinality-ℕ k X Y =
  type-Type-With-Cardinality-ℕ k X ≃ type-Type-With-Cardinality-ℕ k Y

id-equiv-Type-With-Cardinality-ℕ :
  {l : Level} {k : ℕ} (X : Type-With-Cardinality-ℕ l k) →
  equiv-Type-With-Cardinality-ℕ k X X
id-equiv-Type-With-Cardinality-ℕ X = id-equiv-component-UU-Level X

equiv-eq-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) {X Y : Type-With-Cardinality-ℕ l k} →
  X ＝ Y → equiv-Type-With-Cardinality-ℕ k X Y
equiv-eq-Type-With-Cardinality-ℕ k p = equiv-eq-component-UU-Level p

abstract
  is-torsorial-equiv-Type-With-Cardinality-ℕ :
    {l : Level} {k : ℕ} (X : Type-With-Cardinality-ℕ l k) →
    is-torsorial
      ( λ (Y : Type-With-Cardinality-ℕ l k) →
        equiv-Type-With-Cardinality-ℕ k X Y)
  is-torsorial-equiv-Type-With-Cardinality-ℕ {l} {k} X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
    is-equiv (equiv-eq-Type-With-Cardinality-ℕ k {X = X} {Y})
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ k X =
    is-equiv-equiv-eq-component-UU-Level X

eq-equiv-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
  equiv-Type-With-Cardinality-ℕ k X Y → X ＝ Y
eq-equiv-Type-With-Cardinality-ℕ k X Y =
  eq-equiv-component-UU-Level X Y

equiv-equiv-eq-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
  (X ＝ Y) ≃ equiv-Type-With-Cardinality-ℕ k X Y
pr1 (equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y) =
  equiv-eq-Type-With-Cardinality-ℕ k
pr2 (equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y) =
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y
```

### The type Type-With-Cardinality-ℕ is a 1-type

```agda
is-1-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → is-1-type (Type-With-Cardinality-ℕ l k)
is-1-type-Type-With-Cardinality-ℕ k X Y =
  is-set-equiv
    ( equiv-Type-With-Cardinality-ℕ k X Y)
    ( equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y)
    ( is-set-equiv-is-set
      ( is-set-type-Type-With-Cardinality-ℕ k X)
      ( is-set-type-Type-With-Cardinality-ℕ k Y))

Type-With-Cardinality-ℕ-1-Type : (l : Level) (k : ℕ) → 1-Type (lsuc l)
pr1 (Type-With-Cardinality-ℕ-1-Type l k) = Type-With-Cardinality-ℕ l k
pr2 (Type-With-Cardinality-ℕ-1-Type l k) =
  is-1-type-Type-With-Cardinality-ℕ k
```
