# Section 22.3 The (dependent) universal property of the integers

```agda
module section-22-3-the-dependent-universal-property-of-the-integers where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-4-coproducts
open import section-4-5-the-type-of-integers
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import exercise-5-2-inverse-concatenation-maps
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-11-6-the-structure-identity-principle
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-12-dependent-products-of-truncated-maps
```

The dependent universal property precisely characterizes sections of families over the integers, for those families `A(k)` indexed by `k : ℤ` that come equipped with families of equivalences `A(k) ≃ A(k+1)` for all `k : ℤ`.

## Lemma 22.3.1

Let `B` be a family over `ℤ`, equipped with an element `b_0:B(0)`, and an equivalence

```text
e_k : B(k) ≃ B(succ-ℤ(k))
```

for each `k : ℤ`.
Then there is a dependent function `f : Π(k : ℤ) B(k)` equipped with identifications `f(0) = b_0` and

```text
f(succ-ℤ(k)) = e_k(f(k))
```

for any `k : ℤ`.

### Proof

_Proof._ The map is defined using the induction principle for the integers, stated in Remark 4.5.2.
First we take

```text
f(-1) ≔ e_{-1}^{-1}(b_0)
f(0) ≔ b_0
f(1) ≔ e_0(b_0).
```

For the induction step on the negative integers we use

```text
λ n. e_{in-neg(succ-ℕ(n))}^{-1} : Π(n : ℕ) B(in-neg(n)) → B(in-neg(succ-ℕ(n)))
```

For the induction step on the positive integers we use

```text
λ n. e_{in-pos(n)} : Π(n : ℕ) B(in-pos(n)) → B(in-pos(succ-ℕ(n))).
```

The computation rules follow in a straightforward way from the computation rules of `ℤ`-induction and the fact that `e^{-1}` is an inverse of `e`. ◻

```agda
abstract
  elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( k : ℤ) → P k
  elim-ℤ P p0 pS (inl zero-ℕ) =
    map-inv-is-equiv (is-equiv-map-equiv (pS neg-one-ℤ)) p0
  elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    map-inv-is-equiv
      ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (inl x))
  elim-ℤ P p0 pS (inr (inl _)) = p0
  elim-ℤ P p0 pS (inr (inr zero-ℕ)) = map-equiv (pS zero-ℤ) p0
  elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
    map-equiv
      ( pS (inr (inr x)))
      ( elim-ℤ P p0 pS (inr (inr x)))

  compute-zero-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    elim-ℤ P p0 pS zero-ℤ ＝ p0
  compute-zero-elim-ℤ P p0 pS = refl

  compute-succ-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
    elim-ℤ P p0 pS (succ-ℤ k) ＝ map-equiv (pS k) (elim-ℤ P p0 pS k)
  compute-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl zero-ℕ)))
        ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
  compute-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
        ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
  compute-succ-elim-ℤ P p0 pS (inr (inl _)) = refl
  compute-succ-elim-ℤ P p0 pS (inr (inr _)) = refl
```

## Example 22.3.2

For any type `A`, we obtain a map `f : ℤ → A` from any `x : A` and any equivalence `e : A ≃ A`, such that `f(0) = x` and the square

```text
       [ℤ] --f--> [A]
        |          |
succ-ℤ  |          | e
        V          V
       [ℤ] --f--> [A]
```

commutes.
In particular, if we take `A ≔ (x=x)` for some `x : X`, then for any `p : x = x` we have the equivalence `λ q. p ∙ q : (x = x) → (x = x)`.
This equivalence induces a map

```text
k ↦ p^k : ℤ → (x = x),
```

for any `p : x = x`.
This induces the **degree `k` map** on the circle

```text
deg(k) : S¹ → S¹,
```

for any `k : ℤ`, see Exercise 22.2.

In the following proposition we show that the dependent function constructed in Lemma 22.3.1 is unique.
This is the **dependent universal property of the integers**.

## Proposition 22.3.3

Consider a type family `B : ℤ → 𝒰` equipped with `b : B(0)` and a family of equivalences

```text
e : Π(k : ℤ) B(k) ≃ B(succ-ℤ (k)).
```

Then the type

```text
Σ(f : Π(k : ℤ) B(k)) (f(0) = b) × Π(k : ℤ) f(succ-ℤ (k)) = e_k(f(k))
```

is contractible.

### Proof

_Proof._ In Lemma 22.3.1 we have already constructed an element of the asserted type.
Therefore it suffices to show that any two elements of this type can be identified.
Note that the type `(f,p,H) = (f',p',H')` is equivalent to the type of triples `(K,α,β)` consisting of

```text
K : f ~ f'
α : K(0) = p ∙ (p')^{-1}
β : Π(k : ℤ) K(succ-ℤ (k)) = (H(k) ∙ ap_{e_k}(K(k))) ∙ H'(k)^{-1}.
```

We obtain such a triple by applying Lemma 22.3.1 to the family `C` over `ℤ` given by `C(k) ≔ f(k) = f'(k)`, which comes equipped with the base point

```text
p ∙ (p')^{-1} : C(0),
```

and the family of equivalences

```text
Π(k:ℤ) C(k) ≃ C(succ-ℤ (k))
```

given by `r ↦ (H(k) ∙ ap_{e_k}(r)) ∙ H'(k)^{-1}`. ◻

```agda
ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → UU l1
ELIM-ℤ P p0 pS =
  Σ ( (k : ℤ) → P k)
    ( λ f →
      ( ( f zero-ℤ ＝ p0) ×
        ( (k : ℤ) → f (succ-ℤ k) ＝ map-equiv (pS k) (f k))))

Elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → ELIM-ℤ P p0 pS
pr1 (Elim-ℤ P p0 pS) = elim-ℤ P p0 pS
pr1 (pr2 (Elim-ℤ P p0 pS)) = compute-zero-elim-ℤ P p0 pS
pr2 (pr2 (Elim-ℤ P p0 pS)) = compute-succ-elim-ℤ P p0 pS

equiv-comparison-map-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (k : ℤ) →
  (pr1 s k ＝ pr1 t k) ≃ (pr1 s (succ-ℤ k) ＝ pr1 t (succ-ℤ k))
equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k =
  ( ( equiv-concat (pr2 (pr2 s) k) (pr1 t (succ-ℤ k))) ∘e
    ( equiv-concat' (map-equiv (pS k) (pr1 s k)) (inv (pr2 (pr2 t) k)))) ∘e
  ( equiv-ap (pS k) (pr1 s k) (pr1 t k))

zero-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
zero-Eq-ELIM-ℤ P p0 pS s t H =
  (H zero-ℤ ＝ pr1 (pr2 s) ∙ inv (pr1 (pr2 t)))

succ-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
succ-Eq-ELIM-ℤ P p0 pS s t H =
  ( k : ℤ) →
  H (succ-ℤ k) ＝
  map-equiv (equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k) (H k)

Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → UU l1
Eq-ELIM-ℤ P p0 pS s t =
  ELIM-ℤ
    ( λ k → pr1 s k ＝ pr1 t k)
    ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
    ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)

reflexive-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s s
pr1 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H)) = refl-htpy
pr1 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv (right-inv p)
pr2 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv ∘ (right-inv ∘ H)

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → s ＝ t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq P p0 pS s .s refl = reflexive-Eq-ELIM-ℤ P p0 pS s

abstract
  is-torsorial-Eq-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s : ELIM-ℤ P p0 pS) → is-torsorial (Eq-ELIM-ℤ P p0 pS s)
  is-torsorial-Eq-ELIM-ℤ P p0 pS s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (pr1 s))
      ( pair (pr1 s) refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-contr-is-equiv'
          ( Σ (pr1 s zero-ℤ ＝ p0) (λ α → α ＝ pr1 (pr2 s)))
          ( tot (λ α → right-transpose-eq-concat refl α (pr1 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α → is-equiv-right-transpose-eq-concat refl α (pr1 (pr2 s))))
          ( is-torsorial-Id' (pr1 (pr2 s))))
        ( pair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
        ( is-contr-is-equiv'
          ( Σ ( ( k : ℤ) → pr1 s (succ-ℤ k) ＝ pr1 (pS k) (pr1 s k))
              ( λ β → β ~ pr2 (pr2 s)))
          ( tot (λ β → right-transpose-htpy-concat refl-htpy β (pr2 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ β →
              is-equiv-right-transpose-htpy-concat refl-htpy β (pr2 (pr2 s))))
          ( is-torsorial-htpy' (pr2 (pr2 s)))))

abstract
  is-equiv-Eq-ELIM-ℤ-eq :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
  is-equiv-Eq-ELIM-ℤ-eq P p0 pS s =
    fundamental-theorem-id
      ( is-torsorial-Eq-ELIM-ℤ P p0 pS s)
      ( Eq-ELIM-ℤ-eq P p0 pS s)

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → s ＝ t
eq-Eq-ELIM-ℤ P p0 pS s t = map-inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq P p0 pS s t)

abstract
  is-prop-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-prop (ELIM-ℤ P p0 pS)
  is-prop-ELIM-ℤ P p0 pS =
    is-prop-all-elements-equal
      ( λ s t → eq-Eq-ELIM-ℤ P p0 pS s t
        ( Elim-ℤ
          ( λ k → pr1 s k ＝ pr1 t k)
          ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
          ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)))

abstract
  is-contr-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-contr (ELIM-ℤ P p0 pS)
  is-contr-ELIM-ℤ P p0 pS =
    is-proof-irrelevant-is-prop (is-prop-ELIM-ℤ P p0 pS) (Elim-ℤ P p0 pS)
```

The **universal property of the integers** is a simple corollary of the dependent universal property.
One way of phrasing it is that `ℤ` is the _initial type equipped with a point and an automorphism_.

## Corollary 22.3.4

For any type `X` equipped with a base point `x_0 : X` and an automorphism `e : X ≃ X`, the type

```text
Σ(f : ℤ → X) (f(0) = x_0)× ((f ∘ succ-ℤ) ~ (e∘ f))
```

is contractible.

```agda
ELIM-ℤ' :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → UU l1
ELIM-ℤ' {X = X} x e = ELIM-ℤ (λ k → X) x (λ k → e)

abstract
  universal-property-ℤ :
    { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
  universal-property-ℤ {X = X} x e = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)
```

Using the fact that equivalences are contractible maps, we can reformulate the dependent universal property of the integers as follows.

## Theorem 22.3.5

For any type family `A` over `ℤ` equipped with a family of equivalences

```text
e : Π(k : ℤ) A(k) ≃ A(succ-ℤ(k)),
```

the map

```text
ev_0 : (Σ(f : Π(k : ℤ) A(k)) Π(k : ℤ) f(succ-ℤ(k)) = e_k(f(k))) → A(0)
```

given by `(f,H) ↦ f(0)` is an equivalence.

### Proof

BENCHMARK PROBLEM

_Proof._ Note that the fibers of `ev_0` are equivalent to the types that are shown to be contractible in Proposition 22.3.3. ◻

The following corollary will be used to prove that the fundamental cover of the circle is equivalent to the identity type based at `base : S¹`.

## Corollary 22.3.6

For any type `X` equipped with an equivalence `e : X ≃ X`, the map

```text
(Σ(f : ℤ → X) f ∘ succ-ℤ ~ e ∘ f) → X
```

given by `(f,H) ↦ f(0)` is an equivalence.

BENCHMARK PROBLEM
