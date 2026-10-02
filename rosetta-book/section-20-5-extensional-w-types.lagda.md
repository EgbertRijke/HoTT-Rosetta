# Section 20.5 Extensional W-types

```agda
module section-20-5-extensional-w-types where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-2-identity-systems-on-pi-types
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-20-1-the-type-of-well-founded-trees
open import section-20-2-observational-equality-of-w-types
open import section-20-4-the-elementhood-relation-on-w-types

open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import exercise-10-3-contractible-equivalences
open import exercise-10-7-fibers-of-projections
open import exercise-13-4-equivalence-structure-is-a-proposition
open import exercise-13-12-dependent-products-of-truncated-maps
open import exercise-13-15-morphisms-over-a-type
```

It is tempting to think that an element `w : W(A, B)` is completely determined by the elements `z : W(A, B)` equipped with a proof `z ∈ w`.
However, this may not be the case.
For instance, a W-type `W(A, B)` might have *two* unary constructors, e.g., when `A ≔ unit + bool` and the family `B` over `A` is given by

```text
B(inl(x)) ≔ empty
B(inr(y)) ≔ unit.
```

If we write `f` and `g` for the two unary constructors of `W(A, B)`, then we see that for any element `w : W(A, B)`, the elements

```text
u ≔ tree(inr(false), const_w)  and  v ≔ tree(inr(true), const_w)
```

both only contain the element `w`.
However, the elements `u` and `v` are distinct in `W(A, B)`.

Something similar happens in the type of oriented binary rooted trees.
Given two binary rooted trees `S` and `T`, there are two ways to combine `S` and `T` into a new binary tree: we have `[S, T]` and `[T, S]`.
Both contain precisely the elements `S` and `T`, but they are distinct.
Nevertheless, there are many important W-types in which the elements `w` are uniquely determined by the elements `z ∈ w`.
Such W-types are called extensional.

## Definition 20.5.1

We say that a W-type `W(A,B)` is **extensional** if the canonical map

```text
(x = y) → Π(z : W(A, B)) (z ∈ x) ≃ (z ∈ y)
```

is an equivalence.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  extensional-Eq-eq-𝕎 :
    {x y : 𝕎 A B} → x ＝ y → (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)
  extensional-Eq-eq-𝕎 refl z = id-equiv

is-extensional-𝕎 :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
is-extensional-𝕎 A B =
  (x y : 𝕎 A B) → is-equiv (extensional-Eq-eq-𝕎 {x = x} {y})

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-ext-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-ext-𝕎 x y = (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)

  refl-Eq-ext-𝕎 : (x : 𝕎 A B) → Eq-ext-𝕎 x x
  refl-Eq-ext-𝕎 x z = id-equiv

  Eq-ext-eq-𝕎 : {x y : 𝕎 A B} → x ＝ y → Eq-ext-𝕎 x y
  Eq-ext-eq-𝕎 {x} refl = refl-Eq-ext-𝕎 x
```

In the following theorem we give a precise characterization of the inhabited extensional W-types.

## Theorem 20.5.2

Consider an inhabited W-type `W(A, B)`.
Then the following are equivalent:

1. The W-type `W(A, B)` is extensional.

2. The family `B` is **univalent** in the sense that the map

```text
tr_B : (x = y) → (B(x) ≃ B(y))
```

is an equivalence, for every `x, y : A`.

```agda
is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : x ＝ y) → equiv-tr B p)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-prop-is-univalent : is-prop (is-univalent B)
  is-prop-is-univalent =
    is-prop-iterated-Π 2 (λ x y → is-property-is-equiv (equiv-tr B))

  is-univalent-Prop : Prop (l1 ⊔ l2)
  pr1 is-univalent-Prop = is-univalent B
  pr2 is-univalent-Prop = is-prop-is-univalent
```

```agda
univalent-family :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
univalent-family l2 A = Σ (A → UU l2) is-univalent

module _
  {l1 l2 : Level} {A : UU l1} (ℬ : univalent-family l2 A)
  where

  type-family-univalent-family : A → UU l2
  type-family-univalent-family = pr1 ℬ

  is-univalent-univalent-family :
    is-univalent type-family-univalent-family
  is-univalent-univalent-family =
    pr2 ℬ

  equiv-equiv-tr-univalent-family :
    {x y : A} →
    ( x ＝ y) ≃
    ( type-family-univalent-family x ≃ type-family-univalent-family y)
  equiv-equiv-tr-univalent-family {x} {y} =
    ( equiv-tr type-family-univalent-family ,
      is-univalent-univalent-family x y)
```

## Remark 20.5.3

Note that if the W-type `W(A, B)` is empty, then it is vacuously extensional.
However, we saw in Proposition 20.1.5 that any family `B` of inhabited types over `A` gives rise to an empty W-type `W(A, B)`, so there is no hope of showing that `B` is a univalent family if `W(A, B)` is empty.

We also note that a type family `B` over `A` is univalent if and only if the map `B : A → 𝒰` is an embedding.
In other words, the claim in Theorem 20.5.2 is that an inhabited W-type `W(A, B)` is extensional if and only if `B` is the canonical type family over a subuniverse `A` of `𝒰`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-emb-is-univalent :
      is-univalent B → is-emb B
    is-emb-is-univalent U x y =
      is-equiv-top-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( univalence (B x) (B y))
        ( U x y)

    is-univalent-is-emb :
      is-emb B → is-univalent B
    is-univalent-is-emb is-emb-B x y =
      is-equiv-left-map-triangle
        ( equiv-tr B)
        ( equiv-eq)
        ( ap B)
        ( λ where refl → refl)
        ( is-emb-B x y)
        ( univalence (B x) (B y))

emb-univalent-family :
  {l1 l2 : Level} {A : UU l1} → univalent-family l2 A → A ↪ UU l2
emb-univalent-family (B , H) = (B , is-emb-is-univalent H)
```

### Proof
We will first show that (ii) is equivalent to the following property:

1. The map

```text
tr_B : (symbol(x) = y) → (B(symbol(x)) ≃ B(y))
```

is an equivalence for every `x : W(A, B)` and every `y : A`.

Clearly, (ii) implies (ii’).
For the converse we use the assumption that `W(A, B)` is inhabited.
Since the property in (ii) is a proposition, we may assume an element `w : W(A, B)`.
Using `w`, we obtain for every `x : A` the element

```text
tree(x, const_w) : W(A, B)
```

The symbol of `tree(x, const_w)` is `x`, and therefore the hypothesis that (ii’) holds implies that the map `(x = y) → (B(x) ≃ B(y))` is an equivalence.
This concludes the proof that (ii) is equivalent to (ii’).
It remains to show that (i) is equivalent to (ii’).

Let `x : W(A, B)`.
By the fundamental theorem of identity types, the W-type `W(A, B)` is extensional if and only if the total space

```text
Σ(y : W(A, B)) Π(z : W(A, B)) (z ∈ x) ≃ (z ∈ y)
```

is contractible, for any `x : W(A, B)`.
When `x` is of the form `tree(a, α)`, the type `z ∈ x` is just the fiber `fib(α, z)`.
Using this observation, we see that the above type is equivalent to the type

```text
Σ(b : A) Σ(β : B(b) → W(A, B)) Π(z : W(A, B)) fib(α, z) ≃ fib(β, z).
```

By Exercise 13.15 it follows that this type is equivalent to the type

```text
Σ(y : A) Σ(β : B(y) → W(A, B)) Σ(e : B(x) ≃ B(y)) α ~ e ∘ β.
```

Note that the type `Σ(β : B(y) → W(A, B)) α ~ e ∘ β` is contractible for any equivalence `e : B(x) ≃ B(y)`.
Therefore, it follows that the above type is contractible if and only if the type

```text
Σ(y:A) B(x) ≃ B(y)
```

is contractible, which is the case if and only if the map `(x = y) → (B(x) ≃ B(y))` is an equivalence for all `y : A`. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → UU (l1 ⊔ l2)
  Eq-Eq-ext-𝕎 x y u v =
    (z : 𝕎 A B) → map-equiv (u z) ~ map-equiv (v z)

  refl-Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → Eq-Eq-ext-𝕎 x y u u
  refl-Eq-Eq-ext-𝕎 x y u z = refl-htpy

  abstract
    is-torsorial-Eq-Eq-ext-𝕎 :
      (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → is-torsorial (Eq-Eq-ext-𝕎 x y u)
    is-torsorial-Eq-Eq-ext-𝕎 x y u =
      is-torsorial-Eq-Π (λ z → is-torsorial-htpy-equiv (u z))

  Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → u ＝ v → Eq-Eq-ext-𝕎 x y u v
  Eq-Eq-ext-eq-𝕎 x y u .u refl = refl-Eq-Eq-ext-𝕎 x y u

  abstract
    is-equiv-Eq-Eq-ext-eq-𝕎 :
      (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → is-equiv (Eq-Eq-ext-eq-𝕎 x y u v)
    is-equiv-Eq-Eq-ext-eq-𝕎 x y u =
      fundamental-theorem-id
        ( is-torsorial-Eq-Eq-ext-𝕎 x y u)
        ( Eq-Eq-ext-eq-𝕎 x y u)

  eq-Eq-Eq-ext-𝕎 :
    {x y : 𝕎 A B} {u v : Eq-ext-𝕎 x y} → Eq-Eq-ext-𝕎 x y u v → u ＝ v
  eq-Eq-Eq-ext-𝕎 {x} {y} {u} {v} =
    map-inv-is-equiv (is-equiv-Eq-Eq-ext-eq-𝕎 x y u v)

  equiv-total-Eq-ext-𝕎 :
    (x : 𝕎 A B) → Σ (𝕎 A B) (Eq-ext-𝕎 x) ≃ Σ A (λ a → B (shape-𝕎 x) ≃ B a)
  equiv-total-Eq-ext-𝕎 (tree-𝕎 a f) =
    ( ( equiv-tot
        ( λ x →
          ( ( right-unit-law-Σ-is-contr
              ( λ e → is-torsorial-htpy (f ∘ map-inv-equiv e))) ∘e
            ( equiv-tot
              ( λ e →
                equiv-tot
                  ( λ g →
                    equiv-Π
                      ( λ y → f (map-inv-equiv e y) ＝ g y)
                      ( e)
                      ( λ y →
                        equiv-concat
                          ( ap f (is-retraction-map-inv-equiv e y))
                          ( g (map-equiv e y))))))) ∘e
          ( ( equiv-left-swap-Σ) ∘e
            ( equiv-tot
              ( λ g →
                inv-equiv (equiv-fam-equiv-equiv-slice f g)))))) ∘e
          ( associative-Σ)) ∘e
        ( equiv-Σ
          ( λ (t : Σ A (λ x → B x → 𝕎 A B)) →
            Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t)))
          ( inv-equiv-structure-𝕎-Alg)
          ( H))
    where
    H :
      ( z : 𝕎 A (λ x → B x)) →
      Eq-ext-𝕎 (tree-𝕎 a f) z ≃
      Eq-ext-𝕎
        ( tree-𝕎 a f)
        ( tree-𝕎
          ( pr1 (map-equiv inv-equiv-structure-𝕎-Alg z))
          ( pr2 (map-equiv inv-equiv-structure-𝕎-Alg z)))
    H (tree-𝕎 b g) = id-equiv

  abstract
    is-torsorial-Eq-ext-is-univalent-𝕎 :
      is-univalent B → (x : 𝕎 A B) → is-torsorial (Eq-ext-𝕎 x)
    is-torsorial-Eq-ext-is-univalent-𝕎 H (tree-𝕎 a f) =
      is-contr-equiv
        ( Σ A (λ x → B a ≃ B x))
        ( equiv-total-Eq-ext-𝕎 (tree-𝕎 a f))
        ( fundamental-theorem-id' (λ x → equiv-tr B) (H a))

  abstract
    is-extensional-is-univalent-𝕎 :
      is-univalent B → is-extensional-𝕎 A B
    is-extensional-is-univalent-𝕎 H x =
      fundamental-theorem-id
        ( is-torsorial-Eq-ext-is-univalent-𝕎 H x)
        ( λ y → extensional-Eq-eq-𝕎 {y = y})

  abstract
    is-univalent-is-extensional-𝕎 :
      type-trunc-Prop (𝕎 A B) → is-extensional-𝕎 A B → is-univalent B
    is-univalent-is-extensional-𝕎 p H x =
      apply-universal-property-trunc-Prop p
        ( Π-Prop A (λ y → is-equiv-Prop (λ (γ : x ＝ y) → equiv-tr B γ)))
        ( λ w →
          fundamental-theorem-id
            ( is-contr-equiv'
              ( Σ (𝕎 A B) (Eq-ext-𝕎 (tree-𝕎 x (λ y → w))))
              ( equiv-total-Eq-ext-𝕎 (tree-𝕎 x (λ y → w)))
              ( fundamental-theorem-id'
                ( λ z → extensional-Eq-eq-𝕎)
                ( H (tree-𝕎 x (λ y → w)))))
            ( λ y → equiv-tr B {y = y}))
```

## Example 20.5.4

The type `N` of Example 20.1.6, the type of binary rooted trees Example 20.1.8, and the type of finitely branching rooted trees Example 20.1.9 are all examples extensional W-types.
On the other hand, the type of oriented binary rooted trees of Example 20.1.7 and the type of oriented finitely branching rooted trees of Example 20.1.9 are not extensional.

BENCHMARK PROBLEM