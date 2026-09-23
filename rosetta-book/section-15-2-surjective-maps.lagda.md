# Section 15.2 Surjective maps

```agda
module section-15-2-surjective-maps where

open import universe-levels

open import section-2-2-ordinary-function-types
open import exercise-2-3-constant-maps
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
open import exercise-11-4-embedding-triangles
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-7-universal-property-contractible-types
open import exercise-13-12-dependent-products-of-truncated-maps
open import exercise-13-15-morphisms-over-a-type
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-15-1-the-image-of-a-map
```

A map `f : A → B` is surjective if for every `b : B` there is an *unspecified* element `a : A` that maps to `b`.
We define this property using the propositional truncation.

## Definition 15.2.1

A map `f : A → B` is said to be **surjective** if there is an element of type

```text
  is-surj(f) ≔ Π(b : B) ‖fib(f,b)‖.
```

```agda
is-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-surjective-Prop {B = B} f = Π-Prop B (trunc-Prop ∘ fiber f)

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective f = type-Prop (is-surjective-Prop f)

is-prop-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-surjective f)
is-prop-is-surjective f = is-prop-type-Prop (is-surjective-Prop f)

infix 5 _↠_
_↠_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠ B = Σ (A → B) is-surjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  map-surjection : A → B
  map-surjection = pr1 f

  is-surjective-map-surjection : is-surjective map-surjection
  is-surjective-map-surjection = pr2 f
```

## Example 15.2.2

Any equivalence is a surjective map, since its fibers are contractible.
More generally, any map that has a section is surjective.
Those are sometimes called **split epimorphisms**.
Note that having a section is stronger than surjectivity, since in general we don’t have a function `‖fib(f,b)‖ → fib(f,b)`.

```agda
abstract
  is-surjective-has-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    section f → is-surjective f
  is-surjective-has-section (g , G) b = unit-trunc-Prop (g b , G b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-is-equiv : {f : A → B} → is-equiv f → is-surjective f
  is-surjective-is-equiv H = is-surjective-has-section (pr1 H)

  is-surjective-map-equiv : (e : A ≃ B) → is-surjective (map-equiv e)
  is-surjective-map-equiv e = is-surjective-is-equiv (is-equiv-map-equiv e)

  surjection-equiv : A ≃ B → A ↠ B
  surjection-equiv e = map-equiv e , is-surjective-map-equiv e

  surjection-inv-equiv : B ≃ A → A ↠ B
  surjection-inv-equiv e = surjection-equiv (inv-equiv e)

module _
  {l : Level} {A : UU l}
  where

  is-surjective-id : is-surjective (id {A = A})
  is-surjective-id a = unit-trunc-Prop (a , refl)

  id-surjection : A ↠ A
  id-surjection = (id , is-surjective-id)
```

In Exercise 14.4 we showed the dependent universal property of the propositional truncation: a map `f : A → B` into a proposition `B` satisfies the universal property of the propositional truncation if and only if for every family of propositions `P` over `B`, the precomposition map

```text
  - ∘ f : (Π(b : B) P(b)) → (Π(a : A) P(f(a)))
```

is an equivalence.
In the following proposition we show that, if we omit the condition that `B` is a proposition, then `f` satisfies this dependent universal property if and only if `f` is surjective.

## Proposition 15.2.3

Consider a map `f : A → B`.
Then the following are equivalent:

1. The map `f : A → B` is surjective.

2. The map `f : A → B` satisfies the **dependent universal property of a surjective map**: For any family `P` of propositions over `B`, the precomposition map

   ```text
     - ∘ f : (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
   ```
    
   is an equivalence. In other words, any subtype of `B` that contains all the elements of the form `f(x)` contains all the elements of `B`.

3. For any `k ≥ -2`, and for any family `P` of `(k + 1)`-truncated types over `B`, the precomposition map

   ```text
     - ∘ f : (Π(y : B) P(y)) → (Π(x : A) P(f(x)))
   ```
   
   is a `k`-truncated map.

### Proof

To prove that (i) implies (ii), suppose first that `f` is surjective, and consider the commuting square

```text
                                    - ∘ f
               (Π(y : B) P(y)) ---------------> (Π(x : A) P(f(x)))
                        |                            |
  h ↦ λ y. const_{h(y)} |                            | h ↦ λ x. h(f(x),(x,refl))
                        |                            |
                        ∨                            ∨
  (Π(y : B) ‖fib(f,y)‖ → P(y)) ---------------> (Π(y : B) fib(f,y) → P(y))
                                h ↦ h(-) ∘ η
```

In this square, the bottom map is an equivalence by Exercise 13.12 and by the universal property of the propositional truncation of `fib(f,y)`.
The map on the right is an equivalence by Exercise 13.15.
Furthermore, the map on the left is an equivalence by Exercises 13.12 and 13.7, because the type `‖fib(f,y)‖` is contractible by the assumption that `f` is surjective.
Therefore it follows that the top map is an equivalence, which completes the proof that (i) implies (ii).

The proof that (ii) implies (iii) is by induction on `k`.
The base case holds by assumption.
For the inductive step, it suffices by Theorem 12.4.7 to show that `ap_{- ∘ f}` is `k`-truncated for any `g, h : Π(y : B) P(y)`.
Notice that we have a commuting square

```text
                     ap_{- ∘ f}
          (g = h) ---------------> (g ∘ f = h ∘ f)
             |                            |
     htpy-eq |                            | htpy-eq
             |                            |
             ∨                            ∨
  Π(y : B) g(y) = h(y) -------> Π(x : A) g(f(x)) = h(f(x))
                        - ∘ f
```

The vertical maps on the left and right are equivalences by function extensionality, and the bottom map is `k`-truncated by the inductive hypothesis.
This implies that `ap_{- ∘ f}` is `k`-truncated.

To prove that (iii) implies (i), note that the assumption in (iii) implies that the precomposition function

```text
  - ∘ f : (Π(y : B) ‖fib(f,y)‖) → (Π(x : A) ‖fib(f,f(x))‖)
```

is an equivalence.
Hence it suffices to construct an element of type `‖fib(f,f(x))‖` for each `x : A`.
This is easy, because we have

```text
  η(x,refl) : ‖fib(f,f(x))‖. ◻
```

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (B : (i : I) → A i → UU l3)
  (a : (i : I) → A i)
  where

  dependent-lift-family-of-elements : UU (l1 ⊔ l3)
  dependent-lift-family-of-elements = (i : I) → B i (a i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) (a : I → A)
  where

  lift-family-of-elements : UU (l1 ⊔ l3)
  lift-family-of-elements = dependent-lift-family-of-elements (λ _ → B) a

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  (C : (x : A) → B x → UU l4)
  {a : I → A} (b : lift-family-of-elements B a)
  where

  double-lift-family-of-elements : UU (l1 ⊔ l4)
  double-lift-family-of-elements =
    dependent-lift-family-of-elements (λ i → C (a i)) b

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {C : (x : A) → B x → UU l4}
  {a : I → A} (b : lift-family-of-elements B a)
  where

  ev-double-lift-family-of-elements :
    ((x : A) (y : B x) → C x y) → double-lift-family-of-elements C b
  ev-double-lift-family-of-elements h i = h (a i) (b i)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  dependent-universal-property-family-of-fibers :
    {f : A → B} (F : B → UU l3) (δ : lift-family-of-elements F f) → UUω
  dependent-universal-property-family-of-fibers F δ =
    {l : Level} (X : (b : B) → F b → UU l) →
    is-equiv (ev-double-lift-family-of-elements {B = F} {X} δ)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-family-of-fibers :
    {f : A → B} (F : B → UU l3) (δ : lift-family-of-elements F f) → UUω
  universal-property-family-of-fibers F δ =
    {l : Level} (X : B → UU l) →
    is-equiv (ev-double-lift-family-of-elements {B = F} {λ b _ → X b} δ)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  lift-family-of-elements-fiber : lift-family-of-elements (fiber f) f
  pr1 (lift-family-of-elements-fiber a) = a
  pr2 (lift-family-of-elements-fiber a) = refl

  lift-family-of-elements-fiber' : lift-family-of-elements (fiber' f) f
  pr1 (lift-family-of-elements-fiber' a) = a
  pr2 (lift-family-of-elements-fiber' a) = refl

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fiber f y) → UU l3)
  where

  ev-lift-family-of-elements-fiber :
    ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
  ev-lift-family-of-elements-fiber =
    ev-double-lift-family-of-elements (lift-family-of-elements-fiber f)

  extend-lift-family-of-elements-fiber :
    ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
  extend-lift-family-of-elements-fiber h .(f x) (x , refl) = h x

  is-section-extend-lift-family-of-elements-fiber :
    is-section
      ( ev-lift-family-of-elements-fiber)
      ( extend-lift-family-of-elements-fiber)
  is-section-extend-lift-family-of-elements-fiber h = refl

  htpy-is-retraction-extend-lift-family-of-elements-fiber :
    (h : (y : B) (z : fiber f y) → C y z) (y : B) →
    extend-lift-family-of-elements-fiber
      ( ev-lift-family-of-elements-fiber h)
      ( y) ~
    h y
  htpy-is-retraction-extend-lift-family-of-elements-fiber h .(f z) (z , refl) =
    refl

  abstract
    is-retraction-extend-lift-family-of-elements-fiber :
      is-retraction
        ( ev-lift-family-of-elements-fiber)
        ( extend-lift-family-of-elements-fiber)
    is-retraction-extend-lift-family-of-elements-fiber h =
      eq-htpy
        ( eq-htpy ∘ htpy-is-retraction-extend-lift-family-of-elements-fiber h)

  is-equiv-extend-lift-family-of-elements-fiber :
    is-equiv extend-lift-family-of-elements-fiber
  is-equiv-extend-lift-family-of-elements-fiber =
    is-equiv-is-invertible
      ( ev-lift-family-of-elements-fiber)
      ( is-retraction-extend-lift-family-of-elements-fiber)
      ( is-section-extend-lift-family-of-elements-fiber)

  inv-equiv-dependent-universal-property-family-of-fibers :
    ((x : A) → C (f x) (x , refl)) ≃ ((y : B) (z : fiber f y) → C y z)
  inv-equiv-dependent-universal-property-family-of-fibers =
    ( extend-lift-family-of-elements-fiber ,
      is-equiv-extend-lift-family-of-elements-fiber)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-family-of-fibers-fiber :
    dependent-universal-property-family-of-fibers
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  dependent-universal-property-family-of-fibers-fiber C =
    is-equiv-is-invertible
      ( extend-lift-family-of-elements-fiber f C)
      ( is-section-extend-lift-family-of-elements-fiber f C)
      ( is-retraction-extend-lift-family-of-elements-fiber f C)

  equiv-dependent-universal-property-family-of-fibers :
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3) →
    ((y : B) (z : fiber f y) → C y z) ≃
    ((x : A) → C (f x) (x , refl))
  equiv-dependent-universal-property-family-of-fibers C =
    ( ev-lift-family-of-elements-fiber f C ,
      dependent-universal-property-family-of-fibers-fiber C)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-family-of-fibers-fiber :
    universal-property-family-of-fibers
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  universal-property-family-of-fibers-fiber C =
    dependent-universal-property-family-of-fibers-fiber f (λ y _ → C y)

  equiv-universal-property-family-of-fibers :
    {l3 : Level} (C : B → UU l3) →
    ((y : B) → fiber f y → C y) ≃ lift-family-of-elements C f
  equiv-universal-property-family-of-fibers C =
    equiv-dependent-universal-property-family-of-fibers f (λ y _ → C y)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-surjection : UUω
  dependent-universal-property-surjection =
    {l : Level} (P : B → Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

  abstract
    is-surjective-dependent-universal-property-surjection :
      dependent-universal-property-surjection → is-surjective f
    is-surjective-dependent-universal-property-surjection dup-surj-f =
      map-inv-is-equiv
        ( dup-surj-f (λ b → trunc-Prop (fiber f b)))
        ( λ x → unit-trunc-Prop (x , refl))

  abstract
    square-dependent-universal-property-surjection :
      {l3 : Level} (P : B → Prop l3) →
      ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
      ( ( λ h x → h (f x) (x , refl)) ∘
        ( λ h y → h y ∘ unit-trunc-Prop) ∘
        ( postcomp-Π _
          ( λ {y} →
            diagonal-exponential
              ( type-Prop (P y))
              ( type-trunc-Prop (fiber f y)))))
    square-dependent-universal-property-surjection P = refl-htpy

  abstract
    dependent-universal-property-surjection-is-surjective :
      is-surjective f → dependent-universal-property-surjection
    dependent-universal-property-surjection-is-surjective is-surj-f P =
      is-equiv-comp
        ( λ h x → h (f x) (x , refl))
        ( ( λ h y → h y ∘ unit-trunc-Prop) ∘
          ( postcomp-Π
            ( B)
            ( λ {y} →
              diagonal-exponential
                ( type-Prop (P y))
                ( type-trunc-Prop (fiber f y)))))
        ( is-equiv-comp
          ( λ h y → h y ∘ unit-trunc-Prop)
          ( postcomp-Π
            ( B)
            ( λ {y} →
              diagonal-exponential
                ( type-Prop (P y))
                ( type-trunc-Prop (fiber f y))))
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ y →
              is-equiv-diagonal-exponential-is-contr
                ( is-proof-irrelevant-is-prop
                  ( is-prop-type-trunc-Prop)
                  ( is-surj-f y))
                ( type-Prop (P y))))
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ b → is-propositional-truncation-trunc-Prop (fiber f b) (P b))))
        ( universal-property-family-of-fibers-fiber f (is-in-subtype P))

  equiv-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
  pr1 (equiv-dependent-universal-property-surjection-is-surjective H C) h x =
    h (f x)
  pr2 (equiv-dependent-universal-property-surjection-is-surjective H C) =
    dependent-universal-property-surjection-is-surjective H C

  apply-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((a : A) → type-Prop (C (f a))) → ((y : B) → type-Prop (C y))
  apply-dependent-universal-property-surjection-is-surjective H C =
    map-inv-equiv
      ( equiv-dependent-universal-property-surjection-is-surjective H C)

  apply-twice-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → B → Prop l) →
    ((x y : A) → type-Prop (C (f x) (f y))) → ((s t : B) → type-Prop (C s t))
  apply-twice-dependent-universal-property-surjection-is-surjective H C G s =
    apply-dependent-universal-property-surjection-is-surjective
      ( H)
      ( λ b → C s b)
      ( λ y →
        apply-dependent-universal-property-surjection-is-surjective
          ( H)
          ( λ b → C b (f y))
          ( λ x → G x y)
          ( s))

equiv-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (map-surjection f a)))
equiv-dependent-universal-property-surjection f =
  equiv-dependent-universal-property-surjection-is-surjective
    ( map-surjection f)
    ( is-surjective-map-surjection f)

apply-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((a : A) → type-Prop (C (map-surjection f a))) → ((y : B) → type-Prop (C y))
apply-dependent-universal-property-surjection f =
  apply-dependent-universal-property-surjection-is-surjective
    ( map-surjection f)
    ( is-surjective-map-surjection f)
```

As a corollary we obtain that any surjective map into a proposition satisfies the universal property of the propositional truncation.

## Corollary 15.2.4

For any map `f : A → P` into a proposition `P`, the following are equivalent:

1. The map `f` satisfies the universal property of the propositional truncation of `A`.

2. The map `f` is surjective.

Using the characterization of surjective maps of Proposition 15.2.3, we can also give a new characterization of the image of a map.

## Theorem 15.2.5

Consider a commuting triangle

```text
       q
  A ------> B
   \       /
  f \     / m
     \   /
      ∨ ∨ 
       X

```

in which `m` is an embedding.
Then the following are equivalent:

1. The embedding `m` satisfies the universal property of the image inclusion of `f`.

2. The map `q` is surjective.

### Proof

First assume that `m` satisfies the universal property of the image inclusion of `f`, and consider the composite function

```text
                         pr1      m
  (Σ(y : B) ‖fib(q,y)‖) -----> B ----> X
```

Note that `m ∘ pr1` is a composition of embeddings, so it is an embedding.
By the universal property of `m` there is a unique map `h` for which the triangle

```text
       h
  A ------> Σ(y : B) ∥fib(q,y)∥
   \       /
  m \     / m ∘ pr1
     \   /
      ∨ ∨ 
       X

```

commutes.
Now note that `pr1 ∘ h` is a map such that `m ∘ (pr1 ∘ h) ~ m`.
The identity function is another map for which we have `m ∘ id ~ m`, so it follows by uniqueness that `pr1 ∘ h ~ id`.
In other words, the map `h` is a section of the projection map.
Therefore we obtain by Corollary 13.2.3 a dependent function

```text
  Π(b : B) ‖fib(q,b)‖,
```

showing that `q` is surjective.

For the converse, suppose that `q` is surjective.
To prove that `m` satisfies the universal property of the image factorization of `f`, it suffices to construct a map

```text
  hom-slice_X(f,m') → hom-slice_X(m,m'),
```

for any embedding `m' : B' → X`.
To see that there is such an equivalence, we make the following calculation

```text
  hom-slice_X(m,m') ≃ Π(b : B) fib(m',m(b))                  (By Exercise 13.15)
                    ≃ Π(a : A) fib(m',m(q(a)))           (By Proposition 15.2.3)
                    ≃ Π(a : A) fib(m',f(a))                       (By f ~ m ∘ q)
                    ≃ hom-slice_X(f,m').                     (By Exercise 13.15)
                                                                               ◻
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  abstract
    is-surjective-is-image :
      is-image f i q → is-surjective (map-hom-slice f (map-emb i) q)
    is-surjective-is-image up-i b =
      apply-universal-property-trunc-Prop β
        ( trunc-Prop (fiber (map-hom-slice f (map-emb i) q) b))
        ( γ)
      where
      g : type-subtype (trunc-Prop ∘ fiber (map-hom-slice f (map-emb i) q)) → X
      g = map-emb i ∘ pr1
      is-emb-g : is-emb g
      is-emb-g = is-emb-comp (map-emb i) pr1
        ( is-emb-map-emb i)
        ( is-emb-inclusion-subtype (λ x → trunc-Prop _))
      α : hom-slice (map-emb i) g
      α = map-inv-is-equiv
            ( up-i
              ( Σ B ( λ b →
                      type-trunc-Prop
                        ( fiber (map-hom-slice f (map-emb i) q) b)))
              ( g , is-emb-g))
            ( map-unit-im (pr1 q) , pr2 q)
      β :
        type-trunc-Prop (fiber (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)))
      β = pr2 (pr1 α b)
      γ :
        fiber (map-hom-slice f (map-emb i) q) (pr1 (pr1 α b)) →
        type-Prop (trunc-Prop (fiber (pr1 q) b))
      γ (a , p) =
        unit-trunc-Prop
          ( a , p ∙ inv (is-injective-is-emb (is-emb-map-emb i) (pr2 α b)))

  abstract
    is-image-is-surjective' :
      is-surjective (map-hom-slice f (map-emb i) q) →
      is-image' f i q
    is-image-is-surjective' H B' m =
      map-equiv
        ( ( equiv-hom-slice-fiberwise-hom (map-emb i) (map-emb m)) ∘e
          ( inv-equiv
            ( equiv-universal-property-family-of-fibers
              ( map-emb i)
              ( fiber (map-emb m)))) ∘e
          ( inv-equiv
            ( equiv-dependent-universal-property-surjection-is-surjective
              ( pr1 q)
              ( H)
              ( λ b →
                ( fiber (map-emb m) (pr1 i b)) ,
                ( is-prop-map-emb m (pr1 i b))))) ∘e
          ( equiv-Π-equiv-family
            ( λ a → equiv-tr (fiber (map-emb m)) (pr2 q a))) ∘e
          ( equiv-universal-property-family-of-fibers f (fiber (map-emb m))) ∘e
          ( equiv-fiberwise-hom-hom-slice f (map-emb m)))

  abstract
    is-image-is-surjective :
      is-surjective (map-hom-slice f (map-emb i) q) →
      is-image f i q
    is-image-is-surjective H =
      is-image-is-image' f i q (is-image-is-surjective' H)
```

## Corollary 15.2.6

Every map factors uniquely as a surjective map followed by an embedding.

### Proof

Consider a map `f : A → X`, and two factorizations

```text
       q                  q'
  A ------> B        A ------> B'
   \       /          \       /
  f \     / i        f \     / i'
     \   /              \   /
      ∨ ∨                ∨ ∨ 
       X                  X
```

of `f` where `m` and `m'` are embeddings, and `q` and `q'` are surjective.
Then both `m` and `m'` satisfy the universal property of the image factorization of `f` by Theorem 15.2.5.
Now it follows by Theorem 15.1.8 that the type of `(e,H) : hom-slice_X(i,i')` in which `e` is an equivalence, equipped with an identification

```text
  (e,H) ∘ (q,I) = (q',I')
```

in `hom-slice_X(f,i')`, is contractible. ◻

