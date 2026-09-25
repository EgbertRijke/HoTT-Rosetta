# Exercise 13.12

```agda
module exercise-13-12-dependent-products-of-truncated-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-4-embeddings
open import section-12-2-subtypes
open import section-12-4-general-truncation-levels
open import exercise-12-8-retracts-of-truncated-types
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-7-universal-property-contractible-types
```

## Problem statement

### Exercise 13.12(a)

Consider a family of `k`-truncated maps `f_i : A_i → B_i` indexed by `i : I`.
Show that the map

```text
  λ h. λ i. f_i(h(i)) : (Π(i : I) A_i) → (Π(i : I) B_i)
```

is also `k`-truncated.

### Exercise 13.12(b)

Consider an equivalence `e : I ≃ J`, and a family of equivalences `f_i : A_i ≃ B_{e(i)}` indexed by `i : I`, where `A` is a family of types indexed by `I` and `B` family of types indexed by `J`.
Show that the map

```text
  λ h. λ j. f_{e⁻¹(j)}(h(e⁻¹(j))) : (Π(i : I) A_i) → (Π(j : J) B_j)
```

is an equivalence.

### Exercise 13.12(c)

Consider a family of maps `f_i : A_i → B_i` indexed by `i : I`.
Show that the following are equivalent:

1. Each `f_i` is `k`-truncated.

2. For every map `α : X → I`, the map

   ```text
     λ h. λ x. f_{α(x)}(h(x)) : (Π(x : X) A_{α(x)}) → (Π(x : X) B_{α(x)})
   ```

   is `k`-truncated.

### Exercise 13.12(d)

Show that for any map `f : A → B` the following are equivalent:

1. The map `f` is `k`-truncated.

2. For every type `X`, the postcomposition function

   ```text
     f ∘ - : (X → A) → (X → B)
   ```

   is `k`-truncated.

In particular, `f` is an equivalence if and only if `f ∘ -` is an equivalence, and `f` is an embedding if and only if `f ∘ -` is an embedding.

## Solutions

### Exercise 13.12(a)

```agda
map-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) →
  ((i : I) → B i)
map-Π f h i = f i (h i)

compute-fiber-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fiber (f i) (h i)) ≃ fiber (map-Π f) h
compute-fiber-map-Π f h = equiv-tot (λ _ → equiv-eq-htpy) ∘e distributive-Π-Σ

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  abstract
    is-trunc-map-map-Π :
      (k : 𝕋) (f : (i : I) → A i → B i) →
      ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
    is-trunc-map-map-Π k f H h =
      is-trunc-equiv' k
        ( (i : I) → fiber (f i) (h i))
        ( compute-fiber-map-Π f h)
        ( is-trunc-Π k (λ i → H i (h i)))

  abstract
    is-emb-map-Π :
      {f : (i : I) → A i → B i} → ((i : I) → is-emb (f i)) → is-emb (map-Π f)
    is-emb-map-Π {f} H =
      is-emb-is-prop-map
        ( is-trunc-map-map-Π neg-one-𝕋 f (λ i → is-prop-map-is-emb (H i)))

  emb-Π : ((i : I) → A i ↪ B i) → ((i : I) → A i) ↪ ((i : I) → B i)
  emb-Π f = (map-Π (map-emb ∘ f) , is-emb-map-Π (is-emb-map-emb ∘ f))

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  abstract
    is-contr-map-map-Π-is-fiberwise-contr-map :
      {f : (i : I) → A i → B i} →
      ((i : I) → is-contr-map (f i)) → is-contr-map (map-Π f)
    is-contr-map-map-Π-is-fiberwise-contr-map H g =
      is-contr-equiv' _ (compute-fiber-map-Π _ g) (is-contr-Π (λ i → H i (g i)))

  abstract
    is-equiv-map-Π-is-fiberwise-equiv :
      {f : (i : I) → A i → B i} → is-fiberwise-equiv f → is-equiv (map-Π f)
    is-equiv-map-Π-is-fiberwise-equiv is-equiv-f =
      is-equiv-is-contr-map
        ( is-contr-map-map-Π-is-fiberwise-contr-map
          ( is-contr-map-is-equiv ∘ is-equiv-f))

  equiv-Π-equiv-family :
    (e : (i : I) → A i ≃ B i) → ((i : I) → A i) ≃ ((i : I) → B i)
  equiv-Π-equiv-family e =
    ( map-Π (λ i → map-equiv (e i)) ,
      is-equiv-map-Π-is-fiberwise-equiv (λ i → is-equiv-map-equiv (e i)))

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  compute-inv-equiv-Π-equiv-family :
    (e : (i : I) → A i ≃ B i) →
    ( map-inv-equiv (equiv-Π-equiv-family e)) ~
    ( map-equiv (equiv-Π-equiv-family (λ x → inv-equiv (e x))))
  compute-inv-equiv-Π-equiv-family e f =
    is-injective-equiv
      ( equiv-Π-equiv-family e)
      ( ( is-section-map-inv-equiv (equiv-Π-equiv-family e) f) ∙
        ( eq-htpy (λ x → inv (is-section-map-inv-equiv (e x) (f x)))))
```

### Exercise 13.12(b)

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  (e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where

  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (is-section-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  abstract
    is-equiv-map-equiv-Π : is-equiv map-equiv-Π
    is-equiv-map-equiv-Π =
      is-equiv-comp
        ( map-Π
          ( λ a →
            ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
            ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
        ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
        ( is-equiv-precomp-Π-is-equiv
          ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
          ( B'))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a →
            is-equiv-comp
              ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))
              ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
              ( is-equiv-map-equiv
                ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
              ( is-equiv-tr B
                ( is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  equiv-Π = (map-equiv-Π , is-equiv-map-equiv-Π)
```

### Exercise 13.12(c)

```agda
map-Π' :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) →
  ((i : I) → A i → B i) →
  ((j : J) → A (α j)) →
  ((j : J) → B (α j))
map-Π' α f = map-Π (f ∘ α)

compute-fiber-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fiber (f (α j)) (h j)) ≃ fiber (map-Π' α f) h
compute-fiber-map-Π' α f = compute-fiber-map-Π (f ∘ α)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  is-trunc-map-map-Π' :
    (k : 𝕋) {l4 : Level} {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
    ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
  is-trunc-map-map-Π' k {J = J} α f H h =
    is-trunc-equiv' k
      ( (j : J) → fiber (f (α j)) (h j))
      ( compute-fiber-map-Π' α f h)
      ( is-trunc-Π k (λ j → H (α j) (h j)))

  is-trunc-map-is-trunc-map-map-Π'-lzero :
    (k : 𝕋) (f : (i : I) → A i → B i) →
    ({J : UU lzero} (α : J → I) → is-trunc-map k (map-Π' α f)) →
    (i : I) → is-trunc-map k (f i)
  is-trunc-map-is-trunc-map-map-Π'-lzero k f H i b =
    is-trunc-equiv' k
      ( fiber (map-Π (λ _ → f i)) (point b))
      ( equiv-Σ
        ( λ a → f i a ＝ b)
        ( equiv-universal-property-unit (A i))
        ( λ h →
          equiv-ap
            ( equiv-universal-property-unit (B i))
            ( map-Π (λ _ → f i) h)
            ( point b)))
      ( H (λ _ → i) (point b))

  is-trunc-map-is-trunc-map-map-Π' :
    (k : 𝕋) (f : (i : I) → A i → B i) →
    ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
    (i : I) → is-trunc-map k (f i)
  is-trunc-map-is-trunc-map-map-Π' k f H i b =
    is-trunc-map-is-trunc-map-map-Π'-lzero k f H i b

  is-emb-map-Π' :
    {l4 : Level} {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
    ((i : I) → is-emb (f i)) → is-emb (map-Π' α f)
  is-emb-map-Π' α f H =
    is-emb-is-prop-map
      ( is-trunc-map-map-Π' neg-one-𝕋 α f (λ i → is-prop-map-is-emb (H i)))
```

### Exercise 13.12(d)

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-trunc-map-postcomp-is-trunc-map :
    is-trunc-map k f →
    {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)
  is-trunc-map-postcomp-is-trunc-map is-trunc-f A =
    is-trunc-map-map-Π' k (terminal-map A) (point f) (point is-trunc-f)

  is-trunc-map-is-trunc-map-postcomp-lzero :
    ((A : UU lzero) → is-trunc-map k (postcomp A f)) →
    is-trunc-map k f
  is-trunc-map-is-trunc-map-postcomp-lzero is-trunc-postcomp-f =
    is-trunc-map-is-trunc-map-map-Π'-lzero k
      ( point f)
      ( λ {J} α → is-trunc-postcomp-f J)
      ( star)

  is-trunc-map-is-trunc-map-postcomp :
    ({l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
    is-trunc-map k f
  is-trunc-map-is-trunc-map-postcomp is-trunc-postcomp-f =
    is-trunc-map-is-trunc-map-postcomp-lzero is-trunc-postcomp-f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-emb-postcomp-is-emb :
    is-emb f →
    {l3 : Level} (A : UU l3) → is-emb (postcomp A f)
  is-emb-postcomp-is-emb is-emb-f A =
    is-emb-is-prop-map
      ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 f
        ( is-prop-map-is-emb is-emb-f)
        ( A))

  is-emb-is-emb-postcomp-lzero :
    ((A : UU lzero) → is-emb (postcomp A f)) →
    is-emb f
  is-emb-is-emb-postcomp-lzero is-emb-postcomp-f =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-map-postcomp-lzero neg-one-𝕋 f
        ( is-prop-map-is-emb ∘ is-emb-postcomp-f))

  is-emb-is-emb-postcomp :
    ({l3 : Level} (A : UU l3) → is-emb (postcomp A f)) →
    is-emb f
  is-emb-is-emb-postcomp is-emb-postcomp-f =
    is-emb-is-emb-postcomp-lzero is-emb-postcomp-f

emb-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ Y) (A : UU l3) →
  (A → X) ↪ (A → Y)
pr1 (emb-postcomp f A) = postcomp A (map-emb f)
pr2 (emb-postcomp f A) = is-emb-postcomp-is-emb (map-emb f) (is-emb-map-emb f) A

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-retraction-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ B) → inv-equiv f ∘e (f ∘e e) ＝ e
  is-retraction-postcomp-equiv-inv-equiv f e =
    eq-htpy-equiv (λ x → is-retraction-map-inv-equiv f (map-equiv e x))

  is-section-postcomp-equiv-inv-equiv :
    (f : B ≃ C) (e : A ≃ C) → f ∘e (inv-equiv f ∘e e) ＝ e
  is-section-postcomp-equiv-inv-equiv f e =
    eq-htpy-equiv (λ x → is-section-map-inv-equiv f (map-equiv e x))

  is-equiv-postcomp-equiv-equiv :
    (f : B ≃ C) → is-equiv (λ (e : A ≃ B) → f ∘e e)
  is-equiv-postcomp-equiv-equiv f =
    is-equiv-is-invertible
      ( inv-equiv f ∘e_)
      ( is-section-postcomp-equiv-inv-equiv f)
      ( is-retraction-postcomp-equiv-inv-equiv f)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) = f ∘e_
pr2 (equiv-postcomp-equiv f A) = is-equiv-postcomp-equiv-equiv f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (H : {l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  where

  map-inv-is-equiv-is-equiv-postcomp : Y → X
  map-inv-is-equiv-is-equiv-postcomp = map-inv-is-equiv (H Y) id

  is-section-map-inv-is-equiv-is-equiv-postcomp :
    ( f ∘ map-inv-is-equiv-is-equiv-postcomp) ~ id
  is-section-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq (is-section-map-inv-is-equiv (H Y) id)

  is-retraction-map-inv-is-equiv-is-equiv-postcomp :
    ( map-inv-is-equiv-is-equiv-postcomp ∘ f) ~ id
  is-retraction-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr
          ( is-contr-map-is-equiv (H X) f)
          { x =
              ( map-inv-is-equiv-is-equiv-postcomp ∘ f) ,
              ( ap (_∘ f) (is-section-map-inv-is-equiv (H Y) id))}
          { y = id , refl}))

  abstract
    is-equiv-is-equiv-postcomp : is-equiv f
    is-equiv-is-equiv-postcomp =
      is-equiv-is-invertible
        map-inv-is-equiv-is-equiv-postcomp
        is-section-map-inv-is-equiv-is-equiv-postcomp
        is-retraction-map-inv-is-equiv-is-equiv-postcomp

is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp' {l} {X} {Y} f is-equiv-postcomp-f =
  let section-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-is-invertible
    ( pr1 section-f)
    ( htpy-eq (pr2 section-f))
    ( htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
          ( pr1 section-f ∘ f , ap (_∘ f) (pr2 section-f))
          ( id , refl))))

is-equiv-postcomp-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
  {l3 : Level} (A : UU l3) → is-equiv (postcomp A f)
is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
  is-equiv-is-invertible
    ( postcomp A (map-inv-is-equiv is-equiv-f))
    ( eq-htpy ∘
      right-whisker-comp (is-section-map-inv-is-equiv is-equiv-f))
    ( eq-htpy ∘
      right-whisker-comp (is-retraction-map-inv-is-equiv is-equiv-f))

is-equiv-postcomp-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ≃ Y) →
  {l3 : Level} (A : UU l3) → is-equiv (postcomp A (map-equiv f))
is-equiv-postcomp-equiv f =
  is-equiv-postcomp-is-equiv (map-equiv f) (is-equiv-map-equiv f)

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A
```

## Supplement

```agda
map-implicit-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({i : I} → A i) →
  ({i : I} → B i)
map-implicit-Π f h {i} = map-Π f (λ i → h {i}) i

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  is-equiv-map-implicit-Π-is-fiberwise-equiv :
      {f : (i : I) → A i → B i} → is-fiberwise-equiv f →
      is-equiv (map-implicit-Π f)
  is-equiv-map-implicit-Π-is-fiberwise-equiv is-equiv-f =
    is-equiv-comp _ _
      ( is-equiv-explicit-implicit-Π)
      ( is-equiv-comp _ _
        ( is-equiv-map-Π-is-fiberwise-equiv is-equiv-f)
        ( is-equiv-implicit-explicit-Π))

  equiv-implicit-Π-equiv-family :
    (e : (i : I) → (A i) ≃ (B i)) → ({i : I} → A i) ≃ ({i : I} → B i)
  equiv-implicit-Π-equiv-family e =
    ( equiv-implicit-explicit-Π) ∘e
    ( equiv-Π-equiv-family e) ∘e
    ( equiv-explicit-implicit-Π)
```
