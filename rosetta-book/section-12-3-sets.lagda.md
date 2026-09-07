# Section 12.3 Sets

```agda
module section-12-3-sets where

open import universe-levels
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-6-3-observational-equality-of-the-natural-numbers
open import section-8-1-decidability-and-decidable-equality
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-11-2-the-fundamental-theorem
open import section-11-3-equality-on-the-natural-numbers
open import section-12-1-propositions
open import section-12-2-subtypes
```

<!-- rosetta-item: section-12.3 -->

## Definition 12.3.1

<!-- rosetta-item: definition-12.3.1 -->

A type `A` is said to be a **set** if its identity types are propositions, i.e., if it comes equipped with a term of type
```text
is-set(A)≔ Π(x,y:A) is-prop(x = y).
```

<!-- rosetta-agda-block: definition-12.3.1-set-predicate -->

```agda
is-set : {l : Level} → Type l → Type l
is-set A = (x y : A) → is-prop (x ＝ y)
```
<!-- rosetta-item-end: definition-12.3.1 -->

## Example 12.3.2

<!-- rosetta-item: example-12.3.2; latex-label: eg:is-set-nat -->

The type of natural numbers is a set.
To see this, recall from Theorem 11.3.1 that we have an equivalence
```text
(m=n)≃ Eq-ℕ(m,n)
```
for every `m,n:ℕ`.
Therefore it suffices to show that each `Eq-ℕ(m,n)` is a proposition.
This follows easily by induction on both `m` and `n`.

<!-- rosetta-agda-block: example-12.3.2-propositional-natural-number-code -->

```agda
abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m
```

<!-- rosetta-agda-block: example-12.3.2-natural-numbers-are-a-set -->

```agda
abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ m n =
    is-prop-is-equiv (is-equiv-Eq-eq-ℕ {m} {n}) (is-prop-Eq-ℕ m n)
```
<!-- rosetta-item-end: example-12.3.2 -->

## Proposition 12.3.3

<!-- rosetta-item: proposition-12.3.3 -->

Consider a type `A`.
The following are equivalent:

1.  The type `A` is a set.

2.  The type `A` satisfies **axiom K**, i.e., if and only if it comes equipped with a term of type
```text
axiom-K(A)≔Π(x:A) Π(p:x = x) refl = p.
```

### Proof

<!-- rosetta-item: subheading-12.3-proof -->

*Proof.* If `A` is a set, then `x = x` is a proposition, so any two of its elements are equal.
This implies axiom `K`.

For the converse, if `A` satisfies axiom `K`, then for any `p,q:x = y` we have `p ∙ q^{-1} = refl`, and hence `p = q`.
This shows that `x = y` is a proposition, and hence that `A` is a set. ◻

<!-- rosetta-agda-block: proposition-12.3.3-axiom-k-predicate -->

```agda
instance-axiom-K : {l : Level} → Type l → Type l
instance-axiom-K A = (x : A) (p : x ＝ x) → refl ＝ p
```

<!-- rosetta-agda-block: proposition-12.3.3-axiom-k-characterization -->

```agda
module _
  {l : Level} {A : Type l}
  where

  abstract
    is-set-axiom-K' :
      instance-axiom-K A → (x y : A) → all-elements-equal (x ＝ y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : instance-axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y)

  abstract
    axiom-K-is-set : is-set A → instance-axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)
```
<!-- rosetta-item-end: proposition-12.3.3 -->

## Theorem 12.3.4

<!-- rosetta-item: theorem-12.3.4; latex-label: lem:prop_to_id -->

Let `A` be a type, and let `R:A→ A→𝒰` be a binary relation on `A` satisfying

1.  Each `R(x,y)` is a proposition,

2.  `R` is reflexive, as witnessed by `ρ:Π(x:A) R(x,x)`,

3.  There is a map
```text
R(x,y)→ (x=y)
```
    for each `x,y:A`.

Then any family of maps
```text
Π(x,y:A) (x = y)→ R(x,y)
```
is a family of equivalences.
Consequently, the type `A` is a set.

### Proof

<!-- rosetta-item: subheading-12.3-proof-2 -->

*Proof.* Let `f:Π(x,y:A) R(x,y)→(x = y)`.
Since `R` is assumed to be reflexive, we also have a family of maps
```text
path-ind_x(ρ(x)):Π(y:A) (x = y)→ R(x,y).
```
Since each `R(x,y)` is assumed to be a proposition, it therefore follows that each `R(x,y)` is a retract of `x = y`.
Therefore it follows that `Σ(y:A) R(x,y)` is a retract of `Σ(y:A) x=y`, which is contractible.
We conclude that `Σ(y:A) R(x,y)` is contractible, and therefore that any family of maps
```text
Π(y:A) (x=y)→ R(x,y)
```
is a family of equivalences.

Now it also follows that `A` is a set, since its identity types are equivalent to propositions, and therefore they are propositions by Lemma 12.2.2. ◻

<!-- rosetta-agda-block: theorem-12.3.4-propositional-identity-relation -->

```agda

```

<!-- rosetta-agda-block: theorem-12.3.4-binary-relation-criterion -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (R : A → A → Type l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x = is-equiv-prop-in-based-id x (R x) (p x) (ρ x) (i x)

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x =
      is-prop-based-Id-prop-in-based-id x (R x) (p x) (ρ x) (i x)
```

<!-- rosetta-agda-block: theorem-12.3.4-arbitrary-identity-maps -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (R : A → A → Type l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-id-in-prop :
      (f : (x y : A) → x ＝ y → R x y) → (x y : A) → is-equiv (f x y)
    is-equiv-id-in-prop f x =
      fundamental-theorem-id
        ( is-torsorial-prop-in-based-id x (R x) (p x) (ρ x) (i x))
        ( f x)
```
<!-- rosetta-item-end: theorem-12.3.4 -->

## Theorem 12.3.5

<!-- rosetta-item: theorem-12.3.5; latex-label: thm:hedberg -->

Any type with decidable equality is a set.

### Proof

<!-- rosetta-item: subheading-12.3-proof-3 -->

*Proof.* Let `A` be a type, and let `d:Π(x,y:A) (x = y)+ (x≠ y)` be the witness that `A` has decidable equality.
Furthermore, let `𝒰` be a universe containing the type `A`.
We will prove that `A` is a set by applying Theorem 12.3.4.

For every `x,y:A`, we first define a type family `R'(x,y):((x = y)+{(x≠ y)})→𝒰` by
```text
R'(x,y,inl(p)) ≔ unit
R'(x,y,inr(p)) ≔ empty.
```
Note that `R'(x,y,q)` is a proposition for each `x,y:A` and `q:(x = y)+(x≠ y)`.
Now we define `R(x,y)≔ R'(x,y,d(x,y))`.
Then `R` is a reflexive binary relation on `A`, and furthermore each `R(x,y)` is a proposition.
In order to apply Theorem 12.3.4, it therefore it remains to show that `R` implies identity.

Since `R` is defined as an instance of `R'`, it suffices to construct a function
```text
f(q) : R'(q)→ (x = y).
```
for each `q:(x = y)+(x≠ y)`.
Such a function is defined by
```text
f(inl(p),r) := p
f(inr(p),r) := ex-falso(r).
```
 ◻

<!-- rosetta-agda-block: theorem-12.3.5-decidable-equality-relation -->

```agda
module _
  {l : Level} {A : Type l}
  where

  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (x ＝ y) → Type lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → Type lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  is-prop-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    is-prop (Eq-has-decidable-equality' x y t)
  is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
  is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  is-prop-Eq-has-decidable-equality :
    (d : has-decidable-equality A)
    {x y : A} → is-prop (Eq-has-decidable-equality d x y)
  is-prop-Eq-has-decidable-equality d {x} {y} =
    is-prop-Eq-has-decidable-equality' x y (d x y)

  refl-Eq-has-decidable-equality :
    (d : has-decidable-equality A) (x : A) →
    Eq-has-decidable-equality d x x
  refl-Eq-has-decidable-equality d x with d x x
  ... | inl α = star
  ... | inr f = f refl

  Eq-has-decidable-equality-eq :
    (d : has-decidable-equality A) {x y : A} →
    x ＝ y → Eq-has-decidable-equality d x y
  Eq-has-decidable-equality-eq d {x} {.x} refl =
    refl-Eq-has-decidable-equality d x

  eq-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    Eq-has-decidable-equality' x y t → x ＝ y
  eq-Eq-has-decidable-equality' x y (inl p) t = p
  eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  eq-Eq-has-decidable-equality :
    (d : has-decidable-equality A) {x y : A} →
    Eq-has-decidable-equality d x y → x ＝ y
  eq-Eq-has-decidable-equality d {x} {y} =
    eq-Eq-has-decidable-equality' x y (d x y)
```

<!-- rosetta-agda-block: theorem-12.3.5-hedberg -->

```agda
module _
  {l : Level} {A : Type l}
  where

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)
```
<!-- rosetta-item-end: theorem-12.3.5 -->
