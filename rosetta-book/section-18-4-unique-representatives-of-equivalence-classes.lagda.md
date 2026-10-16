# Section 18.4 Unique representatives of equivalence classes

```agda
module section-18-4-unique-representatives-of-equivalence-classes where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import exercise-3-1-multiplication-and-exponentiation
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import exercise-4-1-arithmetic-operations-integers
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import exercise-5-5-semiring-laws-natural-numbers
open import section-6-4-peanos-seventh-and-eighth-axioms
open import exercise-6-3-order-natural-numbers
open import exercise-6-6-absolute-value-integers
open import section-7-1-the-curry-howard-interpretation
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import exercise-7-2-divisibility-poset
open import section-8-1-decidability-and-decidable-equality
open import section-8-2-constructions-by-case-analysis
open import section-8-3-the-well-ordering-principle-of-natural-numbers
open import section-8-4-the-greatest-common-divisor
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-15-2-surjective-maps
open import exercise-15-3-equivalences-are-surjective-embeddings
open import section-18-1-equivalence-relations-and-the-replacement-axiom
open import section-19-1-the-type-of-all-groups
```

A common way to construct set quotients is by showing that the equivalence classes of an equivalence relation have a choice of unique representatives.
In this section we show that if there is a choice of unique representatives, then the set quotient can be constructed as the type of those representatives.
An important reason to define set quotients as the type of canonical representatives, if that is possible, is that the universe level of the set quotient can be kept as low as possible without needing to appeal to the replacement axiom.

## Definition 18.4.1

Consider an equivalence relation `R` on a type `A`, and consider a family of types `C(x)` indexed by `x : A`.
We say that `C` is a **choice of (unique) representatives** of the equivalence classes of `R` if `C` comes equipped with an element of type

```text
  is-choice-of-reps(C) ≔ Π(x : A) is-contr(Σ(y : A) C(y) × R(x,y)).
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-choice-of-representatives :
    (A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-choice-of-representatives P =
    (a : A) → is-contr (Σ A (λ x → P x × sim-equivalence-relation R a x))

  representatives :
    {P : A → UU l3} → is-choice-of-representatives P → UU (l1 ⊔ l3)
  representatives {P} H = Σ A P
```

## Theorem 18.4.2

Consider an equivalence relation `R` on a type `A`, and let `C` be a choice of representatives of the equivalence classes of `R`, with `(h(x),c(x),r(x))` at the center of contraction of `Σ(y : A) C(y) × R(x,y)`.
Then the map

```text
  q : A → Σ(x : A) C(x)
```

given by `q(x) ≔ (h(x),c(x))` is a map into a set such that `q(x) = q(y)` for every `x, y : A` such that `R(x,y)` holds, and moreover `q` satisfies the universal property of the set quotient of `A` by `R`.

### Proof

First, we will use Theorem 12.3.4 to show that the type `Σ(y : A) C(y)` is a set, such that

```text
  ((x,c) = (y,d)) ≃ R(x,y)
```

for any `(x,c)` and `(y,d)` in `Σ(y : A) C(y)`.
Note that we have a function

```text
  R(x,y) → ((x,c) = (y,d)),
```

since for any `r : R(x,y)` both `(x,c,r)` and `(y,d,r)` are elements of the contractible type `Σ(y : A) C(y) × R(x,y)`.
Since `R` is a reflexive relation valued in propositions, the claim follows.
In particular, it follows that

```text
  (q(x) = q(y)) ≃ R(x,y)
```

for any `x, y : A`, i.e., `q` is effective.

To prove the universal property of set quotients, note that by characterization (2) in Theorem 18.2.3 it suffices to show that `q` is surjective and effective.
We have already shown above that `q` is effective, so it remains to show that `q` is surjective.
In fact, we will prove the stronger claim that the projection map

```text
  pr1 : Σ(x : A) C(x) → A
```

is a section of `q`.
Let `x : A` and `c : C(x)`.
Then `(x,c,ρ(x))` is an element of the type

```text
  Σ(y : A) C(y) × R(x,y),
```

which is contractible with center of contraction `(h(x),c(x),r(x))`.
Therefore it follows that `q(x) ≐ (h(x),c(x)) = (x,c)`.
In particular, we see that `q(pr1(x,c)) = (x,c)`, i.e., that `pr1` is a section of `q`. ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives R P) →
    representatives R H → equivalence-class R
  class-representatives H a =
    class R (pr1 a)

  abstract
    is-surjective-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives R P) →
      is-surjective (class-representatives H)
    is-surjective-class-representatives H (pair Q K) =
      apply-universal-property-trunc-Prop K
        ( trunc-Prop
          ( fiber (class-representatives H) (pair Q K)))
        ( λ (pair a φ) →
          unit-trunc-Prop
            ( pair
              ( pair (pr1 (center (H a))) (pr1 (pr2 (center (H a)))))
              ( ( apply-effectiveness-class' R
                  ( symmetric-equivalence-relation R _ _
                    ( pr2 (pr2 (center (H a)))))) ∙
                ( eq-class-equivalence-class R
                  ( pair Q K)
                  ( backward-implication
                    ( φ a)
                    ( refl-equivalence-relation R _))))))

  abstract
    is-emb-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives R P) →
      is-emb (class-representatives H)
    is-emb-class-representatives {P} H (pair a p) =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ A (λ x → P x × sim-equivalence-relation R a x))
          ( ( associative-Σ) ∘e
            ( equiv-tot (λ t → is-effective-class R a (pr1 t))))
          ( H a))
        ( λ y →
          ap (class-representatives H) {pair a p} {y})

  abstract
    is-equiv-class-representatives :
      {P : A → UU l3} (H : is-choice-of-representatives R P) →
      is-equiv (class-representatives H)
    is-equiv-class-representatives H =
      is-equiv-is-emb-is-surjective
        ( is-surjective-class-representatives H)
        ( is-emb-class-representatives H)

  equiv-equivalence-class-representatives :
    {P : A → UU l3} (H : is-choice-of-representatives R P) →
    representatives R H ≃ equivalence-class R
  pr1 (equiv-equivalence-class-representatives H) = class-representatives H
  pr2 (equiv-equivalence-class-representatives H) =
    is-equiv-class-representatives H
```

## Example 18.4.3

In Proposition 7.2.4 we constructed the congruence relations `x ≡ y mod k` on the natural numbers for every natural number `k`, and in Theorems 7.4.7 and 7.4.8 we showed that the map

```text
  x ↦ [x]ₖ₊₁ : ℕ → Fin (k + 1)
```

is effective and split surjective.
By Theorem 18.2.3 it follows that the map

```text
  x ↦ [x]ₖ₊₁ : ℕ → Fin (k + 1)
```

satisfies the universal property of the set quotient of the equivalence relation `x, y ↦ x ≡ y mod k + 1`.

We also claim that there is a choice of representatives of the congruence relations.
We define our choice of representatives by

```text
  C(y) ≔ fib(nat-Fin, y),
```

where `nat-Fin : Fin (k + 1) → ℕ` is the inclusion of `Fin (k + 1)` into `ℕ` constructed in Definition 7.3.4.
To see that `C` is a choice of representatives, we have to prove that

```text
  Σ(y : ℕ) C(y) × (x ≡ y mod k + 1)
```

is contractible for each `x : ℕ`.
At the center of contraction we have the triple `(nat-Fin([x]ₖ₊₁),([x]ₖ₊₁,refl),p)` where `p : x ≡ nat-Fin([x]ₖ₊₁) mod k + 1` is the proof obtained via Theorems 7.4.7 and 7.4.8.
In order to construct the contraction, note that both `C(y)` and `x ≡ y mod k + 1` are propositions for each `y : ℕ`.
Therefore it suffices to prove that for any `y : ℕ` such that `C(y)` and `x ≡ y mod k + 1` hold, we have

```text
  nat-Fin([x]ₖ₊₁) = y.
```

Since `C(y)` holds, we see that `y = nat-Fin([y]ₖ₊₁)`.
Therefore it suffices to prove that `[x]ₖ₊₁ = [y]ₖ₊₁`.
This follows from Theorem 7.4.7, since we assumed `x ≡ y mod k + 1`.

```agda
open import section-7-4-the-natural-numbers-modulo-k-plus-one using
  ( mod-succ-ℕ; cong-eq-mod-succ-ℕ; eq-mod-succ-cong-ℕ;
    is-split-surjective-mod-succ-ℕ; is-section-nat-Fin)

abstract
  is-surjective-is-split-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-split-surjective f → is-surjective f
  is-surjective-is-split-surjective H x =
    unit-trunc-Prop (H x)

is-surjective-mod-succ-ℕ :
  (k : ℕ) → is-surjective (mod-succ-ℕ k)
is-surjective-mod-succ-ℕ k =
  is-surjective-is-split-surjective (is-split-surjective-mod-succ-ℕ k)
```

Note: There is no code in agda-unimath showing that ℤ/ₙ is a set quotient.

## Example 18.4.4

Consider the type of **(integer) fractions**

```text
  Q ≔ ℤ × Σ(y : ℤ) y ≠ 0.
```

We define an equivalence relation on `Q` by

```text
  ((x,y) ~ (x',y')) ≔ (xy' = x'y).
```

This equivalence relation has a choice of representatives defined by

```text
  C(x,y) ≔ (y > 0) ∧ (gcd(x,y) = 1).
```

In other words, we say that `(x,y)` is a **reduced fraction** if `y > 0` and `x` and `y` are coprime.

To see that `C` defines a choice of unique representatives, we first need to construct the center of contraction of

```text
  Σ(q : Q) C(q) × ((x,y) ~ q).
```

Note that if `y < 0` then `(x,y) ~ (-x,-y)`, and we have `-y > 0`.
It is therefore safe to assume that `y > 0`.
We claim that

```text
  (x / gcd(x,y), y / gcd(x,y)) : Q
```

satisfies `C` and is equivalent to `(x,y)`.
It is immediate that `y / gcd(x,y) > 0` and that `(x,y) ~ (x / gcd(x,y),y / gcd(x,y))`.
The fact that `x / gcd(x,y)` and `y / gcd(x,y)` are coprime follows from the fact that

```text
  gcd(x / d,y / d) = gcd(x,y) / d
```

for any common divisor `d` of `x` and `y`.

To construct a contraction, let `(x',y') : Q` such that `C(x',y')` and `(x,y) ~ (x',y')`.
Since `C(q)` and `(x,y) ~ q` are propositions for every `q : Q` it suffices to show that

```text
  x' = x / gcd(x,y) and y' = y / gcd(x,y).
```

Since `x'` and `y'` are assumed to be coprime, it follows from the equation

```text
  x'y / gcd(x,y) = xy' / gcd(x,y)
```

that `x'` divides `x / gcd(x,y)`.
Similarly `x / gcd(x,y)` and `y / gcd(x,y)` are coprime, it follows from the same equation that `x / gcd(x,y)` divides `x'`, so we conclude that `ux' = x / gcd(x,y)` for some `u = ± 1`.
The fact that `vy' = y / gcd(x,y)` for some `v = ± 1` is proven similarly.
However, since both `y` and `y'` are positive, and the `gcd(x,y)` of any two integers is positive, it follows that `v = 1`.
Using the assumption that `x'y / gcd(x,y) = xy' / gcd(x,y)`, this allows us to deduce that also `u = 1`.

We define the type of **rational numbers** by

```text
  ℚ ≔ Σ((x,y) : Q) (y > 0) ∧ gcd(x,y) = 1,
```

and we define the quotient map `(x,y) ↦ x / y : Q → ℚ` to be the quotient map `q` in Theorem 18.4.2.
By Theorem 18.4.2 it also follows that `(x,y) ↦ x / y` satisfies the universal property of the set quotient of the equivalence relation `~` on `Q`.

```agda
is-nonzero-prop-ℤ : ℤ → Prop lzero
is-nonzero-prop-ℤ k = neg-type-Prop (k ＝ zero-ℤ)

is-nonzero-ℤ : ℤ → UU lzero
is-nonzero-ℤ k = type-Prop (is-nonzero-prop-ℤ k)

is-prop-is-nonzero-ℤ : (k : ℤ) → is-prop (is-nonzero-ℤ k)
is-prop-is-nonzero-ℤ k = is-prop-type-Prop (is-nonzero-prop-ℤ k)

nonzero-ℤ : UU lzero
nonzero-ℤ = type-subtype is-nonzero-prop-ℤ

module _
  (k : nonzero-ℤ)
  where

  int-nonzero-ℤ : ℤ
  int-nonzero-ℤ = pr1 k

  is-nonzero-nonzero-ℤ : is-nonzero-ℤ int-nonzero-ℤ
  is-nonzero-nonzero-ℤ = pr2 k

is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

abstract
  is-prop-is-positive-ℤ : (x : ℤ) → is-prop (is-positive-ℤ x)
  is-prop-is-positive-ℤ (inl x) = is-prop-empty
  is-prop-is-positive-ℤ (inr (inl x)) = is-prop-empty
  is-prop-is-positive-ℤ (inr (inr x)) = is-prop-unit

subtype-positive-ℤ : subtype lzero ℤ
subtype-positive-ℤ x = (is-positive-ℤ x , is-prop-is-positive-ℤ x)

positive-ℤ : UU lzero
positive-ℤ = type-subtype subtype-positive-ℤ

ℤ⁺ : UU lzero
ℤ⁺ = positive-ℤ

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ = tr is-positive-ℤ

one-positive-ℤ : positive-ℤ
one-positive-ℤ = (one-ℤ , star)

one-ℤ⁺ : ℤ⁺
one-ℤ⁺ = one-positive-ℤ

is-decidable-is-positive-ℤ : is-decidable-family is-positive-ℤ
is-decidable-is-positive-ℤ (inl x) = inr id
is-decidable-is-positive-ℤ (inr (inl x)) = inr id
is-decidable-is-positive-ℤ (inr (inr x)) = inl star

decidable-subtype-positive-ℤ : decidable-subtype lzero ℤ
decidable-subtype-positive-ℤ x =
  ( is-positive-ℤ x ,
    is-prop-is-positive-ℤ x ,
    is-decidable-is-positive-ℤ x)

is-nonzero-is-positive-ℤ : {x : ℤ} → is-positive-ℤ x → is-nonzero-ℤ x
is-nonzero-is-positive-ℤ {inr (inr x)} H ()

is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ =
  is-set-type-subtype subtype-positive-ℤ is-set-ℤ

positive-ℤ-Set : Set lzero
positive-ℤ-Set = positive-ℤ , is-set-positive-ℤ

is-positive-in-pos-ℤ :
  (n : ℕ) → is-positive-ℤ (in-pos-ℤ n)
is-positive-in-pos-ℤ n = star

abstract
  is-positive-succ-is-positive-ℤ :
    {x : ℤ} → is-positive-ℤ x → is-positive-ℤ (succ-ℤ x)
  is-positive-succ-is-positive-ℤ {inr (inr x)} H = H

succ-positive-ℤ : positive-ℤ → positive-ℤ
succ-positive-ℤ (x , H) = (succ-ℤ x , is-positive-succ-is-positive-ℤ H)

abstract
  is-positive-int-is-nonzero-ℕ :
    (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
  is-positive-int-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
  is-positive-int-is-nonzero-ℕ (succ-ℕ x) H = star

positive-int-ℕ⁺ : ℕ⁺ → positive-ℤ
positive-int-ℕ⁺ (n , n≠0) = int-ℕ n , is-positive-int-is-nonzero-ℕ n n≠0

positive-nat-ℤ⁺ : positive-ℤ → ℕ⁺
positive-nat-ℤ⁺ (inr (inr x) , k>0) = succ-nonzero-ℕ' x

nat-ℤ⁺ : positive-ℤ → ℕ
nat-ℤ⁺ x = nat-ℕ⁺ (positive-nat-ℤ⁺ x)

module _
  {l : Level} {A : UU l}
  where

  is-prop-nonequal : {x y : A} → is-prop (x ≠ y)
  is-prop-nonequal = is-prop-neg

  nonequal-Prop : (x y : A) → Prop l
  pr1 (nonequal-Prop x y) = x ≠ y
  pr2 (nonequal-Prop x y) = is-prop-nonequal

eq-nonzero-ℕ : {m n : nonzero-ℕ} → nat-nonzero-ℕ m ＝ nat-nonzero-ℕ n → m ＝ n
eq-nonzero-ℕ m=n = eq-pair-Σ m=n (eq-is-prop is-prop-nonequal)

abstract
  is-section-positive-nat-ℤ⁺ :
    (k : ℤ⁺) → positive-int-ℕ⁺ (positive-nat-ℤ⁺ k) ＝ k
  is-section-positive-nat-ℤ⁺ (inr (inr k) , k>0) =
    eq-type-subtype subtype-positive-ℤ refl

  is-retraction-positive-nat-ℤ⁺ :
    (n : ℕ⁺) → positive-nat-ℤ⁺ (positive-int-ℕ⁺ n) ＝ n
  is-retraction-positive-nat-ℤ⁺ (zero-ℕ , n≠0) = ex-falso (n≠0 refl)
  is-retraction-positive-nat-ℤ⁺ (succ-ℕ n , n≠0) = eq-nonzero-ℕ refl

  is-equiv-positive-int-ℕ⁺ : is-equiv positive-int-ℕ⁺
  is-equiv-positive-int-ℕ⁺ =
    is-equiv-is-invertible
      ( positive-nat-ℤ⁺)
      ( is-section-positive-nat-ℤ⁺)
      ( is-retraction-positive-nat-ℤ⁺)

positive-int-ℕ : ℕ → positive-ℤ
positive-int-ℕ = rec-ℕ one-positive-ℤ (λ _ → succ-positive-ℤ)

module _
  (p : positive-ℤ)
  where

  int-positive-ℤ : ℤ
  int-positive-ℤ = pr1 p

  int-ℤ⁺ : ℤ
  int-ℤ⁺ = int-positive-ℤ

  is-positive-int-positive-ℤ : is-positive-ℤ int-positive-ℤ
  is-positive-int-positive-ℤ = pr2 p

abstract
  int-positive-int-ℕ : (n : ℕ) → int-positive-ℤ (positive-int-ℕ n) ＝ in-pos-ℤ n
  int-positive-int-ℕ 0 = refl
  int-positive-int-ℕ (succ-ℕ n) = ap succ-ℤ (int-positive-int-ℕ n)

nat-positive-ℤ : positive-ℤ → ℕ
nat-positive-ℤ (inr (inr x) , H) = x

eq-nat-positive-succ-positive-ℤ :
  (x : positive-ℤ) →
  nat-positive-ℤ (succ-positive-ℤ x) ＝ succ-ℕ (nat-positive-ℤ x)
eq-nat-positive-succ-positive-ℤ (inr (inr x) , H) = refl

abstract
  is-section-nat-positive-ℤ :
    (x : positive-ℤ) → positive-int-ℕ (nat-positive-ℤ x) ＝ x
  is-section-nat-positive-ℤ (inr (inr zero-ℕ) , H) = refl
  is-section-nat-positive-ℤ (inr (inr (succ-ℕ x)) , H) =
    ap succ-positive-ℤ (is-section-nat-positive-ℤ ( inr (inr x) , H))

  is-retraction-nat-positive-ℤ :
    (n : ℕ) → nat-positive-ℤ (positive-int-ℕ n) ＝ n
  is-retraction-nat-positive-ℤ zero-ℕ = refl
  is-retraction-nat-positive-ℤ (succ-ℕ n) =
    eq-nat-positive-succ-positive-ℤ (positive-int-ℕ n) ∙
    ap succ-ℕ (is-retraction-nat-positive-ℤ n)

  is-equiv-positive-int-ℕ : is-equiv positive-int-ℕ
  is-equiv-positive-int-ℕ =
    is-equiv-is-invertible
      ( nat-positive-ℤ)
      ( is-section-nat-positive-ℤ)
      ( is-retraction-nat-positive-ℤ)

equiv-positive-int-ℕ : ℕ ≃ positive-ℤ
pr1 equiv-positive-int-ℕ = positive-int-ℕ
pr2 equiv-positive-int-ℕ = is-equiv-positive-int-ℕ

fraction-ℤ : UU lzero
fraction-ℤ = ℤ × positive-ℤ

numerator-fraction-ℤ : fraction-ℤ → ℤ
numerator-fraction-ℤ x = pr1 x

positive-denominator-fraction-ℤ : fraction-ℤ → positive-ℤ
positive-denominator-fraction-ℤ x = pr2 x

denominator-fraction-ℤ : fraction-ℤ → ℤ
denominator-fraction-ℤ x = pr1 (positive-denominator-fraction-ℤ x)

is-positive-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (denominator-fraction-ℤ x)
is-positive-denominator-fraction-ℤ x = pr2 (positive-denominator-fraction-ℤ x)

nat-denominator-fraction-ℤ : fraction-ℤ → ℕ
nat-denominator-fraction-ℤ x =
  nat-positive-ℤ (positive-denominator-fraction-ℤ x)

in-fraction-ℤ : ℤ → fraction-ℤ
pr1 (in-fraction-ℤ x) = x
pr2 (in-fraction-ℤ x) = one-positive-ℤ

int-fraction-ℕ : ℕ → fraction-ℤ
int-fraction-ℕ n = in-fraction-ℤ (int-ℕ n)

neg-one-fraction-ℤ : fraction-ℤ
neg-one-fraction-ℤ = in-fraction-ℤ neg-one-ℤ

is-neg-one-fraction-ℤ : fraction-ℤ → UU lzero
is-neg-one-fraction-ℤ x = (x ＝ neg-one-fraction-ℤ)

zero-fraction-ℤ : fraction-ℤ
zero-fraction-ℤ = in-fraction-ℤ zero-ℤ

is-zero-fraction-ℤ : fraction-ℤ → UU lzero
is-zero-fraction-ℤ x = (x ＝ zero-fraction-ℤ)

is-nonzero-fraction-ℤ : fraction-ℤ → UU lzero
is-nonzero-fraction-ℤ k = ¬ (is-zero-fraction-ℤ k)

one-fraction-ℤ : fraction-ℤ
one-fraction-ℤ = in-fraction-ℤ one-ℤ

is-one-fraction-ℤ : fraction-ℤ → UU lzero
is-one-fraction-ℤ x = (x ＝ one-fraction-ℤ)

neg-fraction-ℤ : fraction-ℤ → fraction-ℤ
neg-fraction-ℤ (d , n) = (neg-ℤ d , n)

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = (x ＝ one-ℤ)

is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ (inl x) = empty
is-nonnegative-ℤ (inr x) = unit

is-prop-is-nonnegative-ℤ : (x : ℤ) → is-prop (is-nonnegative-ℤ x)
is-prop-is-nonnegative-ℤ (inl x) = is-prop-empty
is-prop-is-nonnegative-ℤ (inr x) = is-prop-unit

subtype-nonnegative-ℤ : subtype lzero ℤ
subtype-nonnegative-ℤ x = (is-nonnegative-ℤ x , is-prop-is-nonnegative-ℤ x)

nonnegative-ℤ : UU lzero
nonnegative-ℤ = type-subtype subtype-nonnegative-ℤ

is-nonnegative-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ = tr is-nonnegative-ℤ

module _
  (p : nonnegative-ℤ)
  where

  int-nonnegative-ℤ : ℤ
  int-nonnegative-ℤ = pr1 p

  is-nonnegative-int-nonnegative-ℤ : is-nonnegative-ℤ int-nonnegative-ℤ
  is-nonnegative-int-nonnegative-ℤ = pr2 p

module _
  (m n : ℕ)
  where

  bounded-div-ℕ : UU lzero
  bounded-div-ℕ = Σ ℕ (λ k → (k ≤-ℕ n) × (k *ℕ m ＝ n))

  quotient-bounded-div-ℕ : bounded-div-ℕ → ℕ
  quotient-bounded-div-ℕ = pr1

  upper-bound-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H ≤-ℕ n
  upper-bound-quotient-bounded-div-ℕ H = pr1 (pr2 H)

  eq-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H *ℕ m ＝ n
  eq-quotient-bounded-div-ℕ H = pr2 (pr2 H)

  eq-quotient-bounded-div-ℕ' :
    (H : bounded-div-ℕ) → m *ℕ quotient-bounded-div-ℕ H ＝ n
  eq-quotient-bounded-div-ℕ' H =
    commutative-mul-ℕ m (quotient-bounded-div-ℕ H) ∙ eq-quotient-bounded-div-ℕ H

div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = Σ ℤ (λ k → k *ℤ d ＝ x)

quotient-div-ℤ : (x y : ℤ) → div-ℤ x y → ℤ
quotient-div-ℤ x y H = pr1 H

is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ x y k ↔ div-ℤ k d)

nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = gcd-ℕ (abs-ℤ x) (abs-ℤ y)

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = int-ℕ (nat-gcd-ℤ x y)

is-relatively-prime-ℤ : ℤ → ℤ → UU lzero
is-relatively-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)

is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ x =
  is-relatively-prime-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)

ℚ : UU lzero
ℚ = Σ fraction-ℤ is-reduced-fraction-ℤ

module _
  (x : ℚ)
  where

  fraction-ℚ : fraction-ℤ
  fraction-ℚ = pr1 x

  is-reduced-fraction-ℚ : is-reduced-fraction-ℤ fraction-ℚ
  is-reduced-fraction-ℚ = pr2 x

  numerator-ℚ : ℤ
  numerator-ℚ = numerator-fraction-ℤ fraction-ℚ

  positive-denominator-ℚ : positive-ℤ
  positive-denominator-ℚ = positive-denominator-fraction-ℤ fraction-ℚ

  denominator-ℚ : ℤ
  denominator-ℚ = denominator-fraction-ℤ fraction-ℚ

  is-positive-denominator-ℚ : is-positive-ℤ denominator-ℚ
  is-positive-denominator-ℚ = is-positive-denominator-fraction-ℤ fraction-ℚ
```
