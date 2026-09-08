# Section 13.3 Universal properties

```agda
module section-13-3-universal-properties where

open import universe-levels
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-13-1-equivalent-forms-of-function-extensionality
```

<!-- rosetta-item: section-13.3 -->

The function extensionality principle allows us to prove *universal properties*.
Universal properties are characterizations of all maps out of or into a given type, so they are very important.
Among other applications, universal properties characterize a type up to equivalence.
We prove here the universal properties of dependent pair types and of identity types.
In the exercises, you are asked to prove the universal properties of `unit`, `empty`, and coproducts.

### The universal property of `Σ`-types

<!-- rosetta-item: subheading-13.3-the-universal-property-of-types -->

The **universal property of `Σ`-types** characterizes maps *out of* a dependent pair type `Σ(x:A) B(x)`.
It asserts that the map
```text
ev-pair:((Σ(x:A) B(x))→ X)→ (Π(x:A) (B(x)→ X)),
```
given by `f↦λ x. λ y. f(x,y)`, is an equivalence for any type `X`.
In fact, we will prove a slight generalization of this universal property.
We will prove the **dependent universal property** of `Σ`-types, which characterizes *dependent* functions out of `Σ(x:A) B(x)`.

## Theorem 13.3.1

<!-- rosetta-item: theorem-13.3.1; latex-label: thm:up-sigma -->

Let `B` be a type family over `A`, and let `C` be a type family over `Σ(x:A) B(x)`.
Then the map
```text
ev-pair:(Π(z:Σ(x:A) B(x)) C(z))→ (Π(x:A) Π(y:B(x)) C(x,y)),
```
given by `f↦λ x. λ y. f(x,y)`, is an equivalence.

### Proof

<!-- rosetta-item: subheading-13.3-proof -->

*Proof.* The map in the converse direction is obtained by the induction principle of `Σ`-types.
It is simply the map
```text
ind-Σ : (Π(x:A) Π(y:B(x)) C(x,y))→ (Π(z:Σ(x:A) B(x)) C(z)).
```
By the computation rule for `Σ`-types we have the homotopy
```text
refl-htpy:ev-pair∘ind-Σ~id.
```
This shows that `ind-Σ` is a section of `ev-pair`.

To show that `ind-Σ∘ev-pair~id` we will apply the function extensionality principle.
Therefore it suffices to show that `ind-Σ(λ x. λ y. f(x,y))=f`.
We apply function extensionality again, so it suffices to show that
```text
Π(t:Σ(x:A) B(x)) ind-Σ(λ x. λ y. f(x,y))(t)=f(t).
```
We obtain this homotopy by another application of `Σ`-induction. ◻

<!-- rosetta-agda-block: theorem-13.3.1-dependent-universal-property-sigma -->

```agda
module _
  { l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : Σ A B → Type l3}
  where

  abstract
    is-equiv-ev-pair : is-equiv (ev-pair {C = C})
    pr1 (pr1 is-equiv-ev-pair) = ind-Σ
    pr2 (pr1 is-equiv-ev-pair) = refl-htpy
    pr1 (pr2 is-equiv-ev-pair) = ind-Σ
    pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

  equiv-ev-pair : ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (a , b))
  pr1 equiv-ev-pair = ev-pair
  pr2 equiv-ev-pair = is-equiv-ev-pair
```

### Ordinary Σ universal property from the introduction

<!-- rosetta-agda-block: theorem-13.3.1-ordinary-sigma-specialization -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {X : Type l3}
  where

  is-equiv-ev-pair-nondependent : is-equiv (ev-pair {B = B} {C = λ _ → X})
  is-equiv-ev-pair-nondependent = is-equiv-ev-pair {C = λ _ → X}

  equiv-ev-pair-nondependent : (Σ A B → X) ≃ ((a : A) → B a → X)
  equiv-ev-pair-nondependent = equiv-ev-pair {C = λ _ → X}
```
<!-- rosetta-item-end: theorem-13.3.1 -->

## Corollary 13.3.2

<!-- rosetta-item: corollary-13.3.2; latex-label: cor:times_up_out -->

Let `A`, `B`, and `X` be types.
Then the map
```text
ev-pair: (A× B → X)→ (A→ (B→ X))
```
given by `f↦λ a. λ b. f(a,b)` is an equivalence.

<!-- rosetta-agda-block: corollary-13.3.2-product-currying -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {X : Type l3}
  where

  is-equiv-ev-product : is-equiv (ev-pair {A = A} {B = λ _ → B} {C = λ _ → X})
  is-equiv-ev-product = is-equiv-ev-pair {C = λ _ → X}

  equiv-ev-product : (A × B → X) ≃ (A → B → X)
  equiv-ev-product = equiv-ev-pair {C = λ _ → X}
```
<!-- rosetta-item-end: corollary-13.3.2 -->

### The universal property of identity types

<!-- rosetta-item: subheading-13.3-the-universal-property-of-identity-types -->

The universal property of identity types is the fact that families of maps out of the identity type are uniquely determined by their action on the reflexivity identification.
More precisely, the map
```text
ev-refl:(Π(x:A) (a=x)→ B(x))→ B(a)
```
given by `λ f. f(a,refl)` is an equivalence, for every type family `B` over `A`.
Since this result is similar to the Yoneda lemma of category theory, the universal property of identity types is sometimes referred to as the *type theoretic Yoneda lemma*.
We will prove the *dependent* universal property of identity types, a slight generalization of the universal property.

## Theorem 13.3.3

<!-- rosetta-item: theorem-13.3.3; latex-label: thm:yoneda -->

Consider a type `A` equipped with `a:A`, and consider a family of types `B(x,p)` indexed by `x:A` and `p:a=x`.
Then the map
```text
ev-refl:(Π(x:A) Π(p:a=x) B(x,p))→ B(a,refl),
```
given by `λ f. f(a,refl)`, is an equivalence.

### Proof

<!-- rosetta-item: subheading-13.3-proof-2 -->

*Proof.* The inverse is the function
```text
path-ind_a : B(a,refl)→ Π(x:A) Π(p:a=x) B(x,p).
```
It is immediate from the computation rule of the path induction principle that `ev-refl∘path-ind_a~ id`.

To see that `path-ind_a∘ ev-refl~id`, let `f:Π(x:A) (a=x)→ B(x,p)`.
To show that `path-ind_a(f(a,refl))=f` we apply function extensionality twice.
Therefore it suffices to show that
```text
Π(x:A) Π(p:a=x) path-ind_a(f(a,refl),x,p)=f(x,p).
```
This follows by path induction on `p`, since `path-ind_a(f(a,refl),a,refl)≐ f(a,refl)` by the computation rule of path induction. ◻

<!-- rosetta-agda-block: theorem-13.3.3-dependent-universal-property-identity -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (a : A) {B : (x : A) → a ＝ x → Type l2}
  where

  ev-refl : ((x : A) (p : a ＝ x) → B x p) → B a refl
  ev-refl f = f a refl

  is-retraction-ev-refl : is-retraction (ind-Id a B) ev-refl
  is-retraction-ev-refl = refl-htpy

  abstract
    is-section-ev-refl : is-section (ind-Id a B) ev-refl
    is-section-ev-refl f =
      eq-htpy
        ( λ x →
          eq-htpy
            ( ind-Id a
              ( λ x' p' → ind-Id a _ (f a refl) x' p' ＝ f x' p')
              ( refl)
              ( x)))

  is-equiv-ev-refl : is-equiv ev-refl
  is-equiv-ev-refl =
    is-equiv-is-invertible (ind-Id a B) is-retraction-ev-refl is-section-ev-refl

  equiv-ev-refl : ((x : A) (p : a ＝ x) → B x p) ≃ B a refl
  equiv-ev-refl = (ev-refl , is-equiv-ev-refl)
```

### Ordinary identity universal property from the introduction

<!-- rosetta-agda-block: theorem-13.3.3-ordinary-identity-specialization -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} (a : A) {B : A → Type l2}
  where

  is-equiv-ev-refl-nondependent :
    is-equiv (ev-refl a {B = λ x _ → B x})
  is-equiv-ev-refl-nondependent = is-equiv-ev-refl a {B = λ x _ → B x}

  equiv-ev-refl-nondependent : ((x : A) → a ＝ x → B x) ≃ B a
  equiv-ev-refl-nondependent = equiv-ev-refl a {B = λ x _ → B x}
```
<!-- rosetta-item-end: theorem-13.3.3 -->
