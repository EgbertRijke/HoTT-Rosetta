# Section 13.4 Composing with equivalences

```agda
module section-13-4-composing-with-equivalences where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-11-10-path-split-maps
open import section-13-1-equivalent-forms-of-function-extensionality
```

We show in the following theorem that a map `f : A → B` is an equivalence if and only if precomposing by `f` is an equivalence.

## Theorem 13.4.1

For any map `f : A → B`, the following are equivalent:

1. `f` is an equivalence.

2. For any type family `P` over `B` the map

   ```text
     (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
   ```
   
   given by `h↦ h∘ f` is an equivalence.

3. For any type `X` the map

   ```text
     (B → X) → (A → X)
   ```
   
   given by `g ↦ g ∘ f` is an equivalence.

### Proof

To show that (i) implies (ii), we first recall from Lemma 10.4.5 that any equivalence is also coherently invertible.
Therefore `f` comes equipped with

```text
  g : B → A
  G : f ∘ g ~ id[B]
  H : g ∘ f ~ id[A]
  K : G · f ~ f · H.
```

Then we define the inverse of `- ∘ f` to be the map

```text
  φ : (Π(x : A) P(f(x))) → (Π(y : B) P(y))
```

given by `h ↦ λ y. tr_P(G(y),h(g(y)))`.

To see that `φ` is a section of `- ∘ f`, let `h : Π(x : A) P(f(x))`.
By function extensionality it suffices to construct a homotopy `φ(h) ∘ f ~ h`.
In other words, we have to show that

```text
  tr_P(G(f(x)),h(g(f(x))) = h(x)
```

for any `x : A`.
Now we use the additional homotopy `K` from our assumption that `f` is coherently invertible.
Since we have `K(x) : G(f(x)) = ap_{f}(H(x))` it suffices to show that

```text
  tr_P(ap_{f}(H(x)),h(g(f(x)))) = h(x).
```

A simple path-induction argument yields that

```text
  tr_P(ap_{f}(p)) ~ tr_{P∘ f}(p)
```

for any path `p : x = y` in `A`, so it suffices to construct an identification

```text
  tr_{P ∘ f}(H(x),h(g(f(x)))) = h(x).
```

We have such an identification by `apd_{h}(H(x))`.

To see that `φ` is a retraction of `- ∘ f`, let `h : Π(y : B) P(y)`.
By function extensionality it suffices to construct a homotopy `φ(h ∘ f) ~ h`.
In other words, we have to show that

```text
  tr_P(G(y),h(f(g(y)))) = h(y)
```

for any `y : B`.
We have such an identification by `apd_{h}(G(y))`.
This completes the proof that (i) implies (ii).

Note that (iii) is an immediate consequence of (ii), since we can just choose `P` to be the constant family `X`.

It remains to show that (iii) implies (i).
Suppose that

```text
  - ∘ f : (B → X) → (A → X)
```

is an equivalence for every type `X`.
Then its fibers are contractible by Theorem 10.4.6.
In particular, choosing `X≐ A` we see that the fiber

```text
  fib(- ∘ f, id[A]) ≐ Σ(h : B → A) h ∘ f = id
```

is contractible.
Thus we obtain a function `h : B → A` and a homotopy `H : h ∘ f ~ id` showing that `h` is a retraction of `f`.
We will show that `h` is also a section of `f`.
To see this, we use that the fiber

```text
  fib(- ∘ f, f) ≐ Σ(i : B → B) i ∘ f = f
```

is contractible (choosing `X ≔ B`).
Of course we have `(id,refl)` in this fiber.
However we claim that there also is an identification `p : (f ∘ h) ∘ f = f`, showing that `(f ∘ h,p)` is in this fiber, because

```text
  (f ∘ h) ∘ f ≐ f ∘ (h ∘ f)
  = f ∘ id
  ≐ f
```

From the contractibility of the fiber we obtain an identification `(id,refl) = (f ∘ h,p)`.
In particular we obtain that `id = f ∘ h`, showing that `h` is a section of `f`. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-equiv : UUω
  dependent-universal-property-equiv =
    {l : Level} (C : B → UU l) → is-equiv (precomp-Π f C)

  universal-property-equiv : UUω
  universal-property-equiv = {l : Level} (X : UU l) → is-equiv (precomp f X)

  abstract
    is-equiv-precomp-is-equiv-precomp-Π :
      dependent-universal-property-equiv →
      universal-property-equiv
    is-equiv-precomp-is-equiv-precomp-Π H C = H (λ _ → C)

  abstract
    is-equiv-precomp-Π-is-coherently-invertible :
      is-coherently-invertible f → dependent-universal-property-equiv
    is-equiv-precomp-Π-is-coherently-invertible
      ( g , is-section-g , is-retraction-g , coh) C =
      is-equiv-is-invertible
        ( λ s y → tr C (is-section-g y) (s (g y)))
        ( λ s →
          eq-htpy
            ( λ x →
              ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
              ( substitution-law-tr C f (is-retraction-g x)) ∙
              ( apd s (is-retraction-g x))))
        ( λ s → eq-htpy (λ y → apd s (is-section-g y)))

module _
  {α : Level → Level} (𝒫 : {l : Level} → UU l → UU (α l))
  {l1 l2 : Level} (A : Σ (UU l1) 𝒫) (B : Σ (UU l2) 𝒫) (f : pr1 A → pr1 B)
  where

  universal-property-equiv-structured-type : UUω
  universal-property-equiv-structured-type =
    {l : Level} (C : Σ (UU l) 𝒫) → is-equiv (precomp f (pr1 C))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  abstract
    is-equiv-precomp-Π-is-equiv :
      dependent-universal-property-equiv f
    is-equiv-precomp-Π-is-equiv =
      is-equiv-precomp-Π-is-coherently-invertible f
        ( is-coherently-invertible-is-path-split f
          ( is-path-split-is-equiv f H))

  map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) → ((a : A) → C (f a)) → ((b : B) → C b)
  map-inv-is-equiv-precomp-Π-is-equiv C =
    map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C)

  is-section-map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) →
    (h : (a : A) → C (f a)) →
    precomp-Π f C (map-inv-is-equiv-precomp-Π-is-equiv C h) ~ h
  is-section-map-inv-is-equiv-precomp-Π-is-equiv C h =
    htpy-eq (is-section-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C) h)

  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) →
    (g : (b : B) → C b) →
    map-inv-is-equiv-precomp-Π-is-equiv C (precomp-Π f C g) ~ g
  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv C g =
    htpy-eq (is-retraction-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C) g)

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) = is-equiv-precomp-Π-is-equiv (is-equiv-map-equiv e) C

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-precomp-is-equiv :
      is-equiv f → universal-property-equiv f
    is-equiv-precomp-is-equiv H =
      is-equiv-precomp-is-equiv-precomp-Π f
        ( is-equiv-precomp-Π-is-equiv H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  abstract
    is-equiv-precomp-equiv :
      universal-property-equiv (map-equiv e)
    is-equiv-precomp-equiv =
      is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e)

  equiv-precomp : {l3 : Level} (C : UU l3) → (B → C) ≃ (A → C)
  pr1 (equiv-precomp C) = precomp (map-equiv e) C
  pr2 (equiv-precomp C) = is-equiv-precomp-equiv C

module _
  {α : Level → Level} (𝒫 : {l : Level} → UU l → UU (α l))
  {l1 l2 : Level} (A : Σ (UU l1) 𝒫) (B : Σ (UU l2) 𝒫) (f : pr1 A → pr1 B)
  (H : universal-property-equiv-structured-type 𝒫 A B f)
  where

  map-inv-is-equiv-precomp-structured-type : pr1 B → pr1 A
  map-inv-is-equiv-precomp-structured-type =
    pr1 (center (is-contr-map-is-equiv (H A) id))

  is-section-map-inv-is-equiv-precomp-structured-type :
    is-section f map-inv-is-equiv-precomp-structured-type
  is-section-map-inv-is-equiv-precomp-structured-type =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv (H B) f)
          ( ( f ∘ (pr1 (center (is-contr-map-is-equiv (H A) id)))) ,
            ( ap
              ( λ g → f ∘ g)
              ( pr2 (center (is-contr-map-is-equiv (H A) id)))))
          ( id , refl)))

  is-retraction-map-inv-is-equiv-precomp-structured-type :
    is-retraction f map-inv-is-equiv-precomp-structured-type
  is-retraction-map-inv-is-equiv-precomp-structured-type =
    htpy-eq (pr2 (center (is-contr-map-is-equiv (H A) id)))

  abstract
    is-equiv-is-equiv-precomp-structured-type : is-equiv f
    is-equiv-is-equiv-precomp-structured-type =
      is-equiv-is-invertible
        ( map-inv-is-equiv-precomp-structured-type)
        ( is-section-map-inv-is-equiv-precomp-structured-type)
        ( is-retraction-map-inv-is-equiv-precomp-structured-type)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-precomp :
      universal-property-equiv f → is-equiv f
    is-equiv-is-equiv-precomp H =
      is-equiv-is-equiv-precomp-structured-type
        ( λ X → A → B)
        ( A , f)
        ( B , f)
        ( f)
        ( λ C → H (pr1 C))

abstract
  is-equiv-is-equiv-precomp-Π :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    dependent-universal-property-equiv f →
    is-equiv f
  is-equiv-is-equiv-precomp-Π f H =
    is-equiv-is-equiv-precomp f (is-equiv-precomp-is-equiv-precomp-Π f H)
```
