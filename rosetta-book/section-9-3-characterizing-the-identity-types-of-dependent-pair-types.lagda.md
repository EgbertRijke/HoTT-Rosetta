# Section 9.3 Characterizing the identity types of dependent pair types

```agda
module section-9-3-characterizing-the-identity-types-of-dependent-pair-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
```

<!-- rosetta-item: section-9.3 -->

In this section we characterize the identity type of a `Σ`-type as a `Σ`-type of identity types.
Characterizing identity types is a task that a homotopy type theorist routinely performs, so we will follow the general outline of how such a characterization goes:

1.  First we define a binary relation `R:A→ A→ 𝒰` on the type `A` that we are interested in.
This binary relation is intended to be equivalent to its identity type.

2.  Then we will show that this binary relation is reflexive, by constructing a dependent function of type
```text
Π(x:A) R(x,x)
```

3.  Using the reflexivity we will show that there is a canonical map
```text
(x=y)→ R(x,y)
```
    for every `x,y:A`. This map is just constructed by path induction, using the reflexivity of `R`.

4.  Finally, it has to be shown that the map
```text
(x=y)→ R(x,y)
```
    is an equivalence for each `x,y:A`.

The last step is usually the most difficult, and we will refine our methods for this step in Chapter 11, where we establish the fundamental theorem of identity types.

In this section we consider a type family `B` over `A`.
Given two pairs
```text
(x,y),(x',y'):Σ(x:A) B(x),
```
if we have a path `α:x=x'` then we can compare `y:B(x)` to `y':B(x')` by first transporting `y` along `α`, i.e., we consider the identity type
```text
tr_B(α,y)=y'.
```
Thus it makes sense to think of `(x,y)` to be identical to `(x',y')` if there is an identification `α:x=x'` and an identification `β:tr_B(α,y)=y'`.
In the following definition we turn this idea into a binary relation on the `Σ`-type.

<!-- rosetta-agda-block: section-9.3-transport-action -->

```agda
tr-ap :
  {l1 l2 l3 l4 : Level} {A : Type l1} {B : A → Type l2} {C : Type l3} {D : C → Type l4}
  (f : A → C) (g : (x : A) → B x → D (f x))
  {x y : A} (p : x ＝ y) (z : B x) →
  tr D (ap f p) (g x z) ＝ g y (tr B p z)
tr-ap f g refl z = refl
```

## Definition 9.3.1

<!-- rosetta-item: definition-9.3.1 -->

We will define a relation
```text
Eq-Σ : (Σ(x:A) B(x))→(Σ(x:A) B(x))→𝒰
```
by defining
```text
Eq-Σ(s,t)≔Σ(α:pr 1(s)=pr 1(t)) tr_B(α,pr 2(s))=pr 2 (t).
```

<!-- rosetta-agda-block: definition-9.3.1-equality-sigma -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  Eq-Σ : (s t : Σ A B) → Type (l1 ⊔ l2)
  Eq-Σ s t =
    Σ (pr1 s ＝ pr1 t) (λ α → dependent-identification B α (pr2 s) (pr2 t))
```
<!-- rosetta-item-end: definition-9.3.1 -->

## Lemma 9.3.2

<!-- rosetta-item: lemma-9.3.2 -->

The relation `Eq-Σ` is reflexive, i.e., we can construct
```text
reflexive-Eq-Σ:Π(s:Σ(x:A) B(x)) Eq-Σ(s,s).
```

### Construction

<!-- rosetta-item: subheading-9.3-construction -->

The element `reflexive-Eq-Σ` is constructed by `Σ`-induction on `s:Σ(x:A) B(x)`.
Thus, it suffices to construct a dependent function of type
```text
Π(x:A) Π(y:B(x)) Σ(α:x=x) tr_B(α,y)=y.
```
Here we take `λ x. λ y. (refl,refl)`.

<!-- rosetta-agda-block: lemma-9.3.2-reflexivity -->

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  refl-Eq-Σ s = refl , refl
```
<!-- rosetta-item-end: lemma-9.3.2 -->

## Definition 9.3.3

<!-- rosetta-item: definition-9.3.3 -->

Consider a type family `B` over `A`.
Then for any `s,t:Σ(x:A) B(x)` we define a map
```text
pair-eq: (s=t)→ Eq-Σ(s,t)
```
by path induction, taking `pair-eq(refl)≔reflexive-Eq-Σ(s)`.

<!-- rosetta-agda-block: definition-9.3.3-pair-equality -->

```agda
  eq-base-eq-pair : {s t : Σ A B} → s ＝ t → pr1 s ＝ pr1 t
  eq-base-eq-pair = ap pr1

  dependent-identification-eq-pair :
    {s t : Σ A B} (p : s ＝ t) →
    dependent-identification B (eq-base-eq-pair p) (pr2 s) (pr2 t)
  dependent-identification-eq-pair {s} p = tr-ap pr1 (λ x _ → pr2 x) p (pr1 s)

  pair-eq-Σ : {s t : Σ A B} → s ＝ t → Eq-Σ s t
  pair-eq-Σ p = eq-base-eq-pair p , dependent-identification-eq-pair p
```
<!-- rosetta-item-end: definition-9.3.3 -->

## Theorem 9.3.4

<!-- rosetta-item: theorem-9.3.4; latex-label: thm:eq_sigma -->

Let `B` be a type family over `A`.
Then the map
```text
pair-eq: (s=t)→ Eq-Σ(s,t)
```
is an equivalence for every `s,t:Σ(x:A) B(x)`.

### Proof

<!-- rosetta-item: subheading-9.3-proof -->

*Proof.* The maps in the converse direction
```text
eq-pair : Eq-Σ(s,t)→(s = t)
```
are defined by repeated `Σ`-induction.
By `Σ`-induction on `s` and `t` we see that it suffices to define a map
```text
eq-pair : (Σ(p:x=x') tr_B(p,y) = y')→((x,y) = (x',y')).
```
A map of this type is again defined by `Σ`-induction.
Thus it suffices to define a dependent function of type
```text
Π(p:x=x') (tr_B(p,y) = y') → ((x,y) = (x',y')).
```
Such a dependent function is defined by double path induction by sending `(refl,refl)` to `refl`.
This completes the definition of the function `eq-pair`.

<!-- rosetta-agda-block: theorem-9.3.4-inverse-map -->

```agda
  eq-pair-eq-base :
    {x y : A} {s : B x} (p : x ＝ y) → (x , s) ＝ (y , tr B p s)
  eq-pair-eq-base refl = refl

  eq-pair-eq-base' :
    {x y : A} {t : B y} (p : x ＝ y) → (x , tr B (inv p) t) ＝ (y , t)
  eq-pair-eq-base' refl = refl

  eq-pair-eq-fiber :
    {x : A} {s t : B x} → s ＝ t → (x , s) ＝ (x , t)
  eq-pair-eq-fiber {x} = ap {B = Σ A B} (pair x)

  eq-pair-Σ :
    {s t : Σ A B}
    (α : pr1 s ＝ pr1 t) →
    dependent-identification B α (pr2 s) (pr2 t) → s ＝ t
  eq-pair-Σ refl = eq-pair-eq-fiber

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → s ＝ t
  eq-pair-Σ' p = eq-pair-Σ (pr1 p) (pr2 p)
```


Next, we must show that `eq-pair` is a section of `pair-eq`.
In other words, we must construct an identification
```text
pair-eq(eq-pair(α,β))=(α,β)
```
for each `(α,β):Σ(α:x=x') tr_B(α,y) = y'`.
We proceed by path induction on `α`, followed by path induction on `β`.
Then our goal becomes to construct an identification of type
```text
pair-eq(eq-pair(refl,refl))=(refl,refl)
```
By the definition of `eq-pair` we have `eq-pair(refl,refl)≐ refl`, and by the definition of `pair-eq` we have `pair-eq(refl)≐(refl,refl)`.
Thus we may take `refl{(refl,refl)}` to complete the construction of the homotopy `pair-eq∘eq-pair~id`.

To complete the proof, we must show that `eq-pair` is a retraction of `pair-eq`.
In other words, we must construct an identification
```text
eq-pair(pair-eq(p))=p
```
for each `p:s=t`.
We proceed by path induction on `p:s=t`, so it suffices to construct an identification
```text
eq-pair(refl,refl)=refl.
```
Now we proceed by `Σ`-induction on `s:Σ(x:A) B(x)`, so it suffices to construct an identification
```text
eq-pair(refl,refl)=refl.
```
Since `eq-pair(refl,refl)` computes to `refl`, we may simply take `refl{refl}`. ◻

<!-- rosetta-agda-block: theorem-9.3.4-equivalence-proof -->

```agda
  ap-pr1-eq-pair-eq-fiber :
    {x : A} {s t : B x} (p : s ＝ t) → ap pr1 (eq-pair-eq-fiber p) ＝ refl
  ap-pr1-eq-pair-eq-fiber refl = refl

  is-retraction-pair-eq-Σ :
    (s t : Σ A B) → pair-eq-Σ {s} {t} ∘ eq-pair-Σ' {s} {t} ~ id {A = Eq-Σ s t}
  is-retraction-pair-eq-Σ (x , y) (.x , .y) (refl , refl) = refl

  is-section-pair-eq-Σ :
    (s t : Σ A B) → eq-pair-Σ' {s} {t} ∘ pair-eq-Σ {s} {t} ~ id
  is-section-pair-eq-Σ (x , y) .(x , y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-is-invertible
        ( pair-eq-Σ)
        ( is-section-pair-eq-Σ s t)
        ( is-retraction-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ (s ＝ t)
  pr1 (equiv-eq-pair-Σ s t) = eq-pair-Σ'
  pr2 (equiv-eq-pair-Σ s t) = is-equiv-eq-pair-Σ s t

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-is-invertible
        ( eq-pair-Σ')
        ( is-retraction-pair-eq-Σ s t)
        ( is-section-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → (s ＝ t) ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = (pair-eq-Σ , is-equiv-pair-eq-Σ s t)
```
<!-- rosetta-item-end: theorem-9.3.4 -->
