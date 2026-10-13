# Section 18.5 Set truncations

```agda
module section-18-5-set-truncations where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-7-3-the-standard-finite-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-7-fibers-of-projections
open import section-12-1-propositions
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-14-1-the-universal-property-of-propositional-truncations
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-2-surjective-maps
open import section-16-3-finite-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-17-6-the-binomial-types
open import section-18-1-equivalence-relations-and-the-replacement-axiom
open import section-18-2-the-universal-property-of-set-quotients
```

An important instance of set quotients in the univalent foundations of mathematics is the notion of set truncation.
Analogous to the propositional truncation, the set truncation of a type `A` is a map `η:A→ ‖A‖_0` into a set `‖A‖_0` such that any map `f:A→ X` into a set `X` extends uniquely along `η`:

_Triangle-shaped diagram (automatic draft)._

```text
  [A]
   |
[‖A‖_0]----> [X]

Arrows:
- A --f--> X
- A --η--> ‖A‖_0
- ‖A‖_0 --unlabeled--> X
```

In other words, the set truncation `η:A→‖A‖_0` is the universal way of mapping `A` into a set.
We first specify what it means for a map `f:A→ B` into a set `B` to be a set truncation of `A`.

## Definition 18.5.1

We say that a map `f:A→ B` into a set `B` is a **set truncation** if the precomposition function

```text
_∘ f : (B→ X)→ (A→ X)
```

is an equivalence for every set `X`.

```agda
is-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) → (A → type-Set B) → UUω
is-set-truncation B f =
  {l : Level} (C : Set l) → is-equiv (precomp-Set f C)
```

In the following theorem we prove several conditions that are equivalent to being a set truncation.

## Theorem 18.5.2

Consider a map `f:A→ B` into a set `B`.
Then the following are equivalent:

1. The map `f` is a set truncation.

2. The map `f` satisfies the **dependent universal property** of the set truncation: For every family `X` of sets over `B`, the precomposition function

```text
_∘ f : (Π(b:B) X(b))→(Π(a:A) X(f(a)))
```

    is an equivalence.

3. The map `f` is surjective and effective with respect to the equivalence relation `x,y↦‖x=y‖`, i.e., we have equivalences

```text
(f(x)=f(y))≃ ‖x=y‖
```

    for every `x,y:A`.

### Proof

_Proof._ The fact that (2) implies (1) is immediate.
Moreover, the fact that (1) is equivalent to (3) follows from the fact that any map `h:A→ X` into a set `X` comes equipped with a function

```text
‖x=y‖→ (h(x)=h(y))
```

for every `x,y:A`.

It remains to prove that (1) implies (2).
Consider a family `X` of sets over `B`, and consider the commuting square

_Square-shaped diagram (automatic draft)._

```text
[Σ(g:B→ B) Π(b:B) X(g(b))]---->[Σ(h:A→ B) Π(a:A) X(h(a))]
            |                              |
    [(B→Σ(b:B) X(b))]     ---->    [(A→Σ(b:B) X(b))]

Arrows:
- Σ(g:B→ B) Π(b:B) X(g(b)) --≃--> (B→Σ(b:B) X(b))
- Σ(g:B→ B) Π(b:B) X(g(b)) --{(g,s)↦ (g∘ f,s∘ f)}--> Σ(h:A→ B) Π(a:A) X(h(a))
- Σ(h:A→ B) Π(a:A) X(h(a)) --≃--> (A→Σ(b:B) X(b))
- (B→Σ(b:B) X(b)) --_∘ f--> (A→Σ(b:B) X(b))
```

The side maps are equivalences by the distributivity of `Π` over `Σ`, and the bottom map is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows that the top map is an equivalence.
Furthermore, note that the map

```text
_∘ f : (B→ B)→ (A→ B)
```

is an equivalence by the assumption that `f` is a set truncation.
Therefore it follows from Theorem 11.1.6 that the map

```text
_∘ f : (Π(b:B) X(g(b)))→ (Π(a:A) X(g(f(a))))
```

is an equivalence for every `g:B→ B`.
Now we take `g≔ id` to complete the proof that (1) implies (2). ◻

## Corollary 18.5.3

On any universe `𝒰`, there is an operation `‖_‖_0:𝒰→Set_𝒰` such that every type `A` in `𝒰` comes equipped with a map

```text
η:A→‖A‖_0
```

that satisfies the universal property of the set truncation.
The set `‖A‖_0` is called the **set truncation** of `A`.

### Proof

_Proof._ By Theorem 18.5.2 it follows that a map `f:A→ B` into a set `B` is a set truncation if and only if it is a quotient map with respect to the equivalence relation `x,y↦‖x=y‖`.
Given a type `A` in `𝒰`, the quotient of `A` by `x,y↦‖x=y‖` is equivalent to a type in `𝒰` by the replacement axiom. ◻

```agda
trunc-Set : {l : Level} → UU l → Set l
trunc-Set = trunc zero-𝕋

type-trunc-Set : {l : Level} → UU l → UU l
type-trunc-Set = type-trunc zero-𝕋

is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)
is-set-type-trunc-Set = is-trunc-type-trunc

unit-trunc-Set : {l : Level} {A : UU l} → A → type-trunc-Set A
unit-trunc-Set = unit-trunc

unit-trunc-Set' : {l : Level} (A : UU l) → A → type-trunc-Set A
unit-trunc-Set' A = unit-trunc-Set

is-set-truncation-trunc-Set :
  {l1 : Level} (A : UU l1) → is-set-truncation (trunc-Set A) unit-trunc-Set
is-set-truncation-trunc-Set A = is-truncation-trunc

║_║₀ : {l : Level} → UU l → UU l
║_║₀ = type-trunc-Set
```

## Corollary 18.5.4

The set truncation `η:A→‖A‖_0` is surjective and effective with respect to the equivalence relation `x,y↦‖x=y‖`, i.e., we have an equivalence

```text
(η(x)=η(y))≃ ‖x=y‖
```

for each `x,y:A`.

By this corollary, we may think of the set truncation `‖A‖_0` of `A` as the set of connected components of `A`.
Indeed, if we have an unspecified identification `‖x=y‖` in `A`, then we think of `x` and `y` as being in the same connected component.
For example, any `k`-element set is a type that is in the same connected component of `𝒰` as the type `Fin{k}`.

## Definition 18.5.5

A type `A` is said to be **connected** if its set truncation `‖A‖_0` is contractible.
We define

```text
is-conn(A)≔is-contr‖A‖_0.
```

Furthermore, we say that a map `f:A→ B` is **connected** if all its fibers are connected.

## Remark 18.5.6

In particular, every connected type is inhabited, because if `‖A‖_0` is contractible, then we have equivalences

```text
‖A‖≃ (‖A‖_0→‖A‖) ≃ (A→ ‖A‖),
```

and the latter type contains the unit of the propositional truncation.

Using the notion of connectivity, we can add one more property to the list of equivalent characterizations of set truncations given in Theorem 18.5.2.

## Theorem 18.5.7

Consider a map `f:A→ B` into a set `B`.
Then the following are equivalent:

1. The map `f` is a set truncation.

2. The map `f` is connected.

### Proof

_Proof._ First, suppose that `f` is a set truncation, and consider `b:B`.
Our goal is to show that the type

```text
‖fib(f, b)‖_0
```

is contractible.
Since `f` is surjective by Theorem 18.5.2, there exists an element `a:A` equipped with an identification `f(a)=b`.
We are proving a proposition, so it suffices to show that `‖fib(f, f(a))‖_0` is contractible.
At the center of contraction we have

```text
η(a,refl):‖fib(f, f(a))‖_0.
```

In order to construct the contraction, we use the dependent universal property of the set truncation, by which it suffices to construct a function

```text
Π(x:A) Π(p:f(x)=f(a)) η(a,refl)=η(x,p)
```

Recall from Theorem 18.5.2 that the map `f` is effective, so we have an equivalence `e:‖x=a‖≃ (f(x)=f(a))` for every `x:A`.
Furthermore, equality in set truncations are propositions, so we may even eliminate the propositional truncation from `‖x=a‖`.
Therefore it suffices to prove

```text
Π(x:A) Π(p:x=a) η(a,refl)=η(x,e(η(p)))
```

This is immediate, since `e(η(refl))=refl`.
This completes the proof of (1) implies (2).

For the converse, suppose that `f` is connected, and consider a set `X`.
Note that we have a commuting square

_Square-shaped diagram (automatic draft)._

```text
[(Π(b:B) ‖fib(f, b)‖_0→ X)]---->[(Π(b:B) fib(f, b)→ X)]
             |                             |
          [(B→ X)]         ---->        [(A→ X)]

Arrows:
- (Π(b:B) ‖fib(f, b)‖_0→ X) --{h↦λ b. {t}h(b,η(t))}--> (Π(b:B) fib(f, b)→ X)
- (Π(b:B) fib(f, b)→ X) --{h↦λ a. h(f(a),(a,refl))}--> (A→ X)
- (B→ X) --_∘ f--> (A→ X)
- (B→ X) --h↦λ b. λ u. h(b)--> (Π(b:B) ‖fib(f, b)‖_0→ X)
```

In this commuting square, the map on the left is an equivalence since `‖fib(f, b)‖_0` is contractible for each `b:B`.
The top map is an equivalence because `X` is a set, and the right map is an equivalence by Exercise 13.15.
Therefore it follows that the bottom map is an equivalence, which completes the proof that (2) implies (1). ◻

## Remark 18.5.8

There are truncation operations for every truncation level.
That is, we can define for every type `A` a map `η:A→‖A‖_k` such that the map

```text
_∘η : (‖A‖_k→ X)→ (A→ X)
```

is an equivalence for every `k`-truncated type `X`.
To learn more about general `k`-truncations, we refer to Chapter 7 of \[citation: `hottbook`\].

## Supplement

### The dependent universal property of set truncations

```agda
precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) → UUω
dependent-universal-property-set-truncation B f =
  {l : Level} (X : type-Set B → Set l) → is-equiv (precomp-Π-Set f X)

dependent-universal-property-trunc-Set :
  {l1 : Level} {A : UU l1} →
  dependent-universal-property-set-truncation (trunc-Set A) unit-trunc-Set
dependent-universal-property-trunc-Set = dependent-universal-property-trunc

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
equiv-dependent-universal-property-trunc-Set =
  equiv-dependent-universal-property-trunc

module _
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → Set l2)
  (f : (x : A) → type-Set (B (unit-trunc-Set x)))
  where

  Π-trunc-Set : UU (l1 ⊔ l2)
  Π-trunc-Set =
    Σ ( (x : type-trunc-Set A) → type-Set (B x))
      ( λ g → g ∘ unit-trunc-Set ~ f)

  function-dependent-universal-property-trunc-Set :
    (x : type-trunc-Set A) → type-Set (B x)
  function-dependent-universal-property-trunc-Set =
    function-dependent-universal-property-trunc B f

  compute-dependent-universal-property-trunc-Set :
    function-dependent-universal-property-trunc-Set ∘ unit-trunc-Set ~ f
  compute-dependent-universal-property-trunc-Set =
    htpy-dependent-universal-property-trunc B f

  apply-dependent-universal-property-trunc-Set' :
    (x : type-trunc-Set A) → type-Set (B x)
  apply-dependent-universal-property-trunc-Set' =
    map-inv-equiv (equiv-dependent-universal-property-trunc-Set B) f
```

### 0-connected types

```agda
is-0-connected-Prop : {l : Level} → UU l → Prop l
is-0-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-0-connected : {l : Level} → UU l → UU l
is-0-connected A = type-Prop (is-0-connected-Prop A)

is-prop-is-0-connected : {l : Level} (A : UU l) → is-prop (is-0-connected A)
is-prop-is-0-connected A = is-prop-type-Prop (is-0-connected-Prop A)
```

### Any set truncation is a quotient of the mere equality equivalence relation

```agda
abstract
  is-set-quotient-is-set-truncation :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-set-truncation B f →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f)
  is-set-quotient-is-set-truncation {A = A} B f H X =
    is-equiv-right-factor
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-equivalence-relation
              ( mere-eq-equivalence-relation A) X h)
            ( reflects-mere-eq X h)))
      ( H X)
```

### The set truncation is the set quotient by the mere equality relation

```agda
reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-equivalence-relation
    ( mere-eq-equivalence-relation A)
    ( type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

abstract
  is-set-quotient-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-set-quotient
      ( mere-eq-equivalence-relation A)
      ( trunc-Set A)
      ( reflecting-map-mere-eq-unit-trunc-Set A)
  is-set-quotient-trunc-Set A =
    is-set-quotient-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

module _
  {l : Level}
  where

  abstract
    is-surjective-and-effective-unit-trunc-Set :
      (A : UU l) →
      is-surjective-and-effective
        ( mere-eq-equivalence-relation A)
        ( unit-trunc-Set)
    is-surjective-and-effective-unit-trunc-Set A =
      is-surjective-and-effective-is-set-quotient
        ( mere-eq-equivalence-relation A)
        ( trunc-Set A)
        ( unit-trunc-Set ,
          reflects-mere-eq (trunc-Set A) unit-trunc-Set)
        ( λ {l} → is-set-quotient-trunc-Set A)

  abstract
    is-surjective-unit-trunc-Set :
      (A : UU l) → is-surjective (unit-trunc-Set {A = A})
    is-surjective-unit-trunc-Set A =
      pr1 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    is-effective-unit-trunc-Set :
      (A : UU l) →
      is-effective (mere-eq-equivalence-relation A) (unit-trunc-Set {A = A})
    is-effective-unit-trunc-Set A =
      pr2 (is-surjective-and-effective-unit-trunc-Set A)

  abstract
    apply-effectiveness-unit-trunc-Set :
      {A : UU l} {x y : A} → unit-trunc-Set x ＝ unit-trunc-Set y → mere-eq x y
    apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
      map-equiv (is-effective-unit-trunc-Set A x y)

  abstract
    apply-effectiveness-unit-trunc-Set' :
      {A : UU l} {x y : A} → mere-eq x y → unit-trunc-Set x ＝ unit-trunc-Set y
    apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
      map-inv-equiv (is-effective-unit-trunc-Set A x y)
```

### Elements of 0-connected types are all merely equal

```agda
abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → all-elements-merely-equal A
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)
```

### A type is 0-connected if it is inhabited and all elements are merely equal

```agda
abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → all-elements-merely-equal A → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K =
    apply-universal-property-trunc-Prop H
      ( is-0-connected-Prop _)
      ( λ a → is-0-connected-mere-eq a (K a))
```

### We characterize the identity type of Type-With-Cardinality-ℕ

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

### The type Type-With-Cardinality-ℕ is connected

```agda
abstract
  is-0-connected-Type-With-Cardinality-ℕ :
    {l : Level} (n : ℕ) → is-0-connected (Type-With-Cardinality-ℕ l n)
  is-0-connected-Type-With-Cardinality-ℕ {l} n =
    is-0-connected-mere-eq
      ( raise-Fin-Type-With-Cardinality-ℕ l n)
      ( λ A →
        map-trunc-Prop
          ( ( eq-equiv-Type-With-Cardinality-ℕ n
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( A)) ∘
            ( map-equiv
              ( equiv-precomp-equiv
                ( inv-equiv (compute-raise l (Fin n)))
                ( type-Type-With-Cardinality-ℕ n A))))
          ( pr2 A))
```
