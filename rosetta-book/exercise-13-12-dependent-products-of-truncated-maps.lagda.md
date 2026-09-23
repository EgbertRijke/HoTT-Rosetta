# Exercise 13.12

```agda
module exercise-13-12-dependent-products-of-truncated-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import exercise-12-8-retracts-of-truncated-types
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-13-4-composing-with-equivalences
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

PARTIAL BENCHMARK PROBLEM

```agda
map-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) →
  ((i : I) → B i)
map-Π f h i = f i (h i)

map-Π' :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) →
  ((i : I) → A i → B i) →
  ((j : J) → A (α j)) →
  ((j : J) → B (α j))
map-Π' α f = map-Π (f ∘ α)

map-implicit-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({i : I} → A i) →
  ({i : I} → B i)
map-implicit-Π f h {i} = map-Π f (λ i → h {i}) i

compute-fiber-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fiber (f i) (h i)) ≃ fiber (map-Π f) h
compute-fiber-map-Π f h = equiv-tot (λ _ → equiv-eq-htpy) ∘e distributive-Π-Σ

compute-fiber-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fiber (f (α j)) (h j)) ≃ fiber (map-Π' α f) h
compute-fiber-map-Π' α f = compute-fiber-map-Π (f ∘ α)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  abstract
    is-contr-map-map-Π-is-fiberwise-contr-map :
      {f : (i : I) → A i → B i} →
      ((i : I) → is-contr-map (f i)) → is-contr-map (map-Π f)
    is-contr-map-map-Π-is-fiberwise-contr-map H g =
      is-contr-equiv' _ (compute-fiber-map-Π _ g) (is-contr-Π (λ i → H i (g i)))
```

### Exercise 13.12(b)

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

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

BENCHMARK PROBLEM

### Exercise 13.12(d)

BENCHMARK PROBLEM
