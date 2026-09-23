# Section 15.1 The image of a map

```agda
module section-15-1-the-image-of-a-map where

open import exercise-13-15-morphisms-over-a-type

open import universe-levels

open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import exercise-9-5-sigma-swap
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-14-2-propositional-truncations-as-higher-inductive-types
```

### The universal property of the image

Recall from Exercise 13.15 that we made the following definition:

## Definition 15.1.1

Let `f : A → X` and `g : B → X` be maps.
A **morphism from `f` to `g` over `X`** consists of a map `h : A → B` equipped with a homotopy `H : f ~ g ∘ h` witnessing that the triangle

```text
       q
  A ------> B
   \       /
  f \     / i
     \   /
      ∨ ∨ 
       X

```

commutes.
Thus, we define the type

```text
  hom-slice_X(f,g) ≔ Σ(h : A → B) f ~ g ∘ h.
```

Composition of morphisms over `X` is defined by

```text
  (k,K) ∘ (h,H) ≔ (k ∘ h,H ∙ (K · h)).
```

```agda
comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
pr1 (comp-hom-slice f g h j i) = map-hom-slice g h j ∘ map-hom-slice f g i
pr2 (comp-hom-slice f g h j i) =
  ( triangle-hom-slice f g i) ∙h
  ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i))

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
pr1 (id-hom-slice f) = id
pr2 (id-hom-slice f) = refl-htpy
```

## Definition 15.1.2

Consider a commuting triangle

```text
      q_f
  A ------> I
   \       /
  f \     / i_f
     \   /
      ∨ ∨ 
       X
```

with `H : f ~ i ∘ q`, where `i` is an embedding.
We say that `i` satisfies the **universal property of the image of `f`** if the precomposition function

```text
  - ∘ (q,H) : hom-slice_X(i,m) → hom-slice_X(f,m)
```

is an equivalence for every embedding `m : B ↪ X`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  precomp-emb :
    {l4 : Level} {C : UU l4} (j : C ↪ X) →
    hom-slice (map-emb i) (map-emb j) → hom-slice f (map-emb j)
  pr1 (precomp-emb j r) =
    map-hom-slice (map-emb i) (map-emb j) r ∘ map-hom-slice f (map-emb i) q
  pr2 (precomp-emb j r) =
    ( triangle-hom-slice f (map-emb i) q) ∙h
    ( ( triangle-hom-slice (map-emb i) (map-emb j) r) ·r
      ( map-hom-slice f (map-emb i) q))

  is-image : UUω
  is-image = {l : Level} (C : UU l) (j : C ↪ X) → is-equiv (precomp-emb j)
```

## Lemma 15.1.3

For any `f : A → X` and any embedding `m : B → X`, the type `hom-slice_X(f,m)` is a proposition.

### Proof

*Proof.* Recall from Exercise 13.15 that the type `hom-slice_X(f,m)` is equivalent to the type

```text
  Π(a : A) fib(m, f(a)).
```

Furthermore, recall from Theorem 12.2.3 that a map is an embedding if and only if its fibers are propositions.
Thus we see that the type `Π(a : A) fib(m,f(a))` is a product of propositions, hence it is a proposition by Theorem 13.1.5. ◻

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-prop-hom-slice :
      (f : A → X) (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
    is-prop-hom-slice f i =
      is-prop-is-equiv
        ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
        ( is-prop-Π
          ( λ x → is-prop-Π
            ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))
```

## Proposition 15.1.4

Consider a commuting triangle

```text
       q
  A ------> I
   \       /
  f \     / i
     \   /
      ∨ ∨ 
       X
```

with `H : f ~ i ∘ q`, where `i` is an embedding.
Then the following are equivalent:

1. The embedding `i` satisfies the universal property of the image inclusion of `f`.

2. For every embedding `m : B → X` there is a map

   ```text
     hom-slice_X(f,m) → hom-slice_X(i,m).
   ```

### Proof

Since `hom-slice_X(f,m)` is a proposition for every embedding `m : B → X`, the claim follows immediately by the observation made in Remark 14.1.2. ◻

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  where

  is-image' : UUω
  is-image' =
    {l : Level} (C : UU l) (j : C ↪ X) →
    hom-slice f (map-emb j) → hom-slice (map-emb i) (map-emb j)

abstract
  is-image-is-image' :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    { B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i)) →
    is-image' f i q → is-image f i q
  is-image-is-image' f i q up' C j =
    is-equiv-has-converse-is-prop
      ( is-prop-hom-slice (map-emb i) j)
      ( is-prop-hom-slice f j)
      ( up' C j)
```

### The existence of the image

The image of a map `f : A → X` can be defined using the propositional truncation.

## Definition 15.1.5

For any map `f : A → X` we define the **image** of `f` to be the type

```text
  im(f) ≔ Σ(x : X) ‖fib(f,x)‖.
```

Furthermore, we define

1. the **image inclusion**

   ```text
     i_f : im(f) → X
   ```
   
   to be the projection `pr1`,

2. the map

   ```text
     q_f : A → im(f)
   ```

   to be the map given by `q_f(x) ≔ (f(x),η(x,refl))`, and

3. the homotopy `I_f : f ~ i_f ∘ q_f` witnessing that the triangle

   ```text
         q_f
     A ------> I
      \       /
     f \     / i_f
        \   /
         ∨ ∨ 
          X
   ```

   commutes, to be given by `I_f(x) ≔ refl`.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  subtype-im : subtype (l1 ⊔ l2) X
  subtype-im x = trunc-Prop (fiber f x)

  is-in-im : X → UU (l1 ⊔ l2)
  is-in-im = is-in-subtype subtype-im

  im : UU (l1 ⊔ l2)
  im = type-subtype subtype-im

  inclusion-im : im → X
  inclusion-im = inclusion-subtype subtype-im

  map-unit-im : A → im
  pr1 (map-unit-im a) = f a
  pr2 (map-unit-im a) = unit-trunc-Prop (a , refl)

  triangle-unit-im : coherence-triangle-maps f inclusion-im map-unit-im
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  pr1 unit-im = map-unit-im
  pr2 unit-im = triangle-unit-im

  Eq-im : im → im → UU l1
  Eq-im x y = (pr1 x ＝ pr1 y)

  refl-Eq-im : (x : im) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im) → x ＝ y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  abstract
    is-torsorial-Eq-im :
      (x : im) → is-torsorial (Eq-im x)
    is-torsorial-Eq-im x =
      is-torsorial-Eq-subtype
        ( is-torsorial-Id (pr1 x))
        ( λ x → is-prop-type-trunc-Prop)
        ( pr1 x)
        ( refl)
        ( pr2 x)

  abstract
    is-equiv-Eq-eq-im : (x y : im) → is-equiv (Eq-eq-im x y)
    is-equiv-Eq-eq-im x =
      fundamental-theorem-id
        ( is-torsorial-Eq-im x)
        ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im) → (x ＝ y) ≃ Eq-im x y
  pr1 (equiv-Eq-eq-im x y) = Eq-eq-im x y
  pr2 (equiv-Eq-eq-im x y) = is-equiv-Eq-eq-im x y

  eq-Eq-im : (x y : im) → Eq-im x y → x ＝ y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)
```

## Proposition 15.1.6

The image inclusion `i_f : im(f) → X` of any map `f : A → X` is an embedding.

### Proof

The claim follows directly by Corollary 12.2.4, because the type `‖fib(f, x)‖` is a proposition for each `x : X`. ◻

```agda
abstract
  is-emb-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-emb (inclusion-im f)
  is-emb-inclusion-im f = is-emb-inclusion-subtype (trunc-Prop ∘ fiber f)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
pr1 (emb-im f) = inclusion-im f
pr2 (emb-im f) = is-emb-inclusion-im f

abstract
  is-injective-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-injective (inclusion-im f)
  is-injective-inclusion-im f = is-injective-is-emb (is-emb-inclusion-im f)
```

## Theorem 15.1.7

The image inclusion `i_f : im(f) → X` of any map `f : A → X` satisfies the universal property of the image inclusion of `f`.

### Proof

Consider an embedding `m : B ↪ X`.
Note that we have a commuting square

```text
               hom-slice_X(i_f,m) ----------------> hom-slice_X(f,m)
                        |                                    |
                        |                                    |
                        |                                    |
                        ∨                                    ∨
  (Π(x : X) fib(i_f, x) → fib(m,x)) ----> (Π(x : X) fib(f,x) → fib(m,x))
             
                              h ↦ λ x. h_x ∘ φ_x
```

in which all four types are propositions, and the vertical maps are equivalences.
Therefore it suffices to construct a map

```text
  (Π(x : X) fib(f,x) → fib(m,x)) → (Π(x : X) fib(i_f,x) → fib(m,x))
```

The fiber `fib(i_f,x)` is equivalent to the propositional truncation `‖fib(f,x)‖` and the type `fib(m,x)` is a proposition by the assumption that `m` is an embedding.
Therefore we obtain the desired map by the universal property of the propositional truncation. ◻

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} (f : A → X)
  (m : B ↪ X) (h : hom-slice f (map-emb m))
  where

  abstract
    fiberwise-map-is-image-im :
      (x : X) → type-trunc-Prop (fiber f x) → fiber (map-emb m) x
    fiberwise-map-is-image-im x =
      map-universal-property-trunc-Prop
        { A = fiber f x}
        ( fiber-emb-Prop m x)
        ( λ t →
          ( map-hom-slice f (map-emb m) h (pr1 t)) ,
          ( ( inv (triangle-hom-slice f (map-emb m) h (pr1 t))) ∙ ( pr2 t)))

  map-is-image-im : im f → B
  map-is-image-im (x , t) = pr1 (fiberwise-map-is-image-im x t)

  inv-triangle-is-image-im :
    map-emb m ∘ map-is-image-im ~ inclusion-im f
  inv-triangle-is-image-im (x , t) = pr2 (fiberwise-map-is-image-im x t)

  triangle-is-image-im :
    inclusion-im f ~ map-emb m ∘ map-is-image-im
  triangle-is-image-im = inv-htpy inv-triangle-is-image-im

abstract
  is-image-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-image f (emb-im f) (unit-im f)
  is-image-im f =
    is-image-is-image'
      ( f)
      ( emb-im f)
      ( unit-im f)
      ( λ B m h → (map-is-image-im f m h , triangle-is-image-im f m h))
```

### The uniqueness of the image

We will now show that the universal property of the image implies that the image is determined uniquely up to equivalence.

## Theorem 15.1.8

Let `f` be a map, and consider two commuting triangles

```text
       q                  q'
  A ------> B        A ------> B'
   \       /          \       /
  f \     / i        f \     / i'
     \   /              \   /
      ∨ ∨                ∨ ∨ 
       X                  X
```

with `I : f ~ i ∘ q` and `I' : f ~ i' ∘ q'`, in which `i` and `i'` are assumed to be embeddings.
Then, if any two of the following three properties hold, so does the third:

1. The embedding `i` satisfies the universal property of the image inclusion of `f`.

2. The embedding `i'` satisfies the universal property of the image inclusion of `f`.

3. The type of equivalences `e : B ≃ B'` equipped with a homotopy witnessing that the triangle

   ```text
          e
     B ------> B'
      \       /
     i \     / i'
        \   /
         ∨ ∨ 
          X
   ```

   commutes is contractible.

### Proof

*Proof.* First, we show that if (i) and (ii) hold, then (iii) holds.
Note that the type `hom-slice_X(i,i')` is a proposition, since `i'` is assumed to be an embedding.
Therefore it suffices to show that the unique map `h : B → B'` such that the triangle

*Triangle-shaped diagram (automatic draft).*

```text
       h
  B ------> B'
   \       /
  i \     / i'
     \   /
      ∨ ∨ 
       X
```

commutes, is an equivalence.
To see this, note that by Exercise 13.15 it suffices to show that the action on fibers

```text
  fib(i,x) → fib(i',x)
```

is an equivalence for each `x : X`.
This follows from the universal property of `i'`, since we similarly obtain a family of maps

```text
  fib(i',x) → fib(i,x)
```

indexed by `x : X`, and the types `fib(i,x)` and `fib(i',x)` are propositions by the assumptions that `i` and `i'` are embeddings.

Now we will show that (iii) implies that (i) holds if and only if (ii) holds.
We will assume a morphism `(e,H) : hom-slice_X(i,i')` such that the map `e` is an equivalence.
Furthermore, consider an embedding `m : C → X`.
Then the fact that (i) holds if and only if (ii) holds follows from the equivalence

```text
  (hom-slice_X(f,m) → hom-slice_X(i,m)) ≃ (hom-slice_X(f,m) → hom-slice_X(i',m)). ◻
```

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : is-image f i q)
  {C : UU l4} (j : C ↪ X) (r : hom-slice f (map-emb j))
  where

  abstract
    universal-property-image :
      is-contr
        ( Σ ( hom-slice (map-emb i) (map-emb j))
            ( λ h →
              htpy-hom-slice f
                ( map-emb j)
                ( comp-hom-slice f (map-emb i) (map-emb j) h q)
                ( r)))
    universal-property-image =
      is-contr-equiv'
        ( fiber (precomp-emb f i q j) r)
        ( equiv-tot
          ( λ h →
            extensionality-hom-slice f (map-emb j) (precomp-emb f i q j h) r))
        ( is-contr-map-is-equiv (H C j) r)

  hom-slice-universal-property-image : hom-slice (map-emb i) (map-emb j)
  hom-slice-universal-property-image =
    pr1 (center universal-property-image)

  map-hom-slice-universal-property-image : B → C
  map-hom-slice-universal-property-image =
    map-hom-slice (map-emb i) (map-emb j) hom-slice-universal-property-image

  triangle-hom-slice-universal-property-image :
    map-emb i ~ map-emb j ∘ map-hom-slice-universal-property-image
  triangle-hom-slice-universal-property-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb j)
      ( hom-slice-universal-property-image)

  htpy-hom-slice-universal-property-image :
    htpy-hom-slice f
      ( map-emb j)
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb j)
        ( hom-slice-universal-property-image)
        ( q))
      ( r)
  htpy-hom-slice-universal-property-image =
    pr2 (center universal-property-image)

  abstract
    htpy-map-hom-slice-universal-property-image :
      map-hom-slice f
        ( map-emb j)
        ( comp-hom-slice f
          ( map-emb i)
          ( map-emb j)
          ( hom-slice-universal-property-image)
          ( q)) ~
      map-hom-slice f (map-emb j) r
    htpy-map-hom-slice-universal-property-image =
      pr1 htpy-hom-slice-universal-property-image

    tetrahedron-hom-slice-universal-property-image :
      ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
          ( ( triangle-hom-slice-universal-property-image) ·r
            ( map-hom-slice f (map-emb i) q))) ∙h
        ( map-emb j ·l htpy-map-hom-slice-universal-property-image)) ~
      ( triangle-hom-slice f (map-emb j) r)
    tetrahedron-hom-slice-universal-property-image =
      pr2 htpy-hom-slice-universal-property-image

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-equiv-hom-slice-is-injective :
      {f : A → X} {g : B → X} →
      is-injective f → is-injective g →
      (h : hom-slice f g) →
      hom-slice g f →
      is-equiv-hom-slice f g h
    is-equiv-hom-slice-is-injective {f} {g} F G h i =
      is-equiv-is-invertible
        ( map-hom-slice g f i)
        ( λ y →
          G ( inv
              ( ( triangle-hom-slice g f i y) ∙
                ( triangle-hom-slice f g h (map-hom-slice g f i y)))))
        ( λ x →
          F ( inv
              ( ( triangle-hom-slice f g h x) ∙
                ( triangle-hom-slice g f i (map-hom-slice f g h x)))))

  is-equiv-hom-slice-injection :
    (f : injection A X) (g : injection B X)
    (h : hom-slice (map-injection f) (map-injection g)) →
    hom-slice (map-injection g) (map-injection f) →
    is-equiv-hom-slice (map-injection f) (map-injection g) h
  is-equiv-hom-slice-injection (f , F) (g , G) =
    is-equiv-hom-slice-is-injective F G

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  is-equiv-hom-slice-emb :
    (f : A ↪ X) (g : B ↪ X)
    (h : hom-slice (map-emb f) (map-emb g)) →
    hom-slice (map-emb g) (map-emb f) →
    is-equiv-hom-slice (map-emb f) (map-emb g) h
  is-equiv-hom-slice-emb f g =
    is-equiv-hom-slice-injection (injection-emb f) (injection-emb g)

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (h : hom-slice (map-emb i) (map-emb i'))
  where

  abstract
    is-equiv-is-image-is-image :
      is-image f i q →
      is-image f i' q' →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h)
    is-equiv-is-image-is-image up-i up-i' =
      is-equiv-hom-slice-emb i i' h (map-inv-is-equiv (up-i' B i) q)

  abstract
    is-image-is-image-is-equiv :
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      is-image f i q →
      is-image f i' q'
    is-image-is-image-is-equiv is-equiv-h up-i {l} =
      is-image-is-image' f i' q'
        ( λ C j r →
          comp-hom-slice
            ( map-emb i')
            ( map-emb i)
            ( map-emb j)
            ( map-inv-is-equiv (up-i C j) r)
            ( pair
              ( map-inv-is-equiv is-equiv-h)
              ( triangle-section
                ( map-emb i)
                ( map-emb i')
                ( map-hom-slice (map-emb i) (map-emb i') h)
                ( triangle-hom-slice (map-emb i) (map-emb i') h)
                ( pair
                  ( map-inv-is-equiv is-equiv-h)
                  ( is-section-map-inv-is-equiv is-equiv-h)))))

  abstract
    is-image-is-equiv-is-image :
      is-image f i' q' →
      is-equiv (map-hom-slice (map-emb i) (map-emb i') h) →
      is-image f i q
    is-image-is-equiv-is-image up-i' is-equiv-h {l} =
      is-image-is-image' f i q
        ( λ C j r →
          comp-hom-slice
            ( map-emb i)
            ( map-emb i')
            ( map-emb j)
            ( map-inv-is-equiv (up-i' C j) r)
            ( h))

module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (Hi : is-image f i q)
  {B' : UU l4} (i' : B' ↪ X) (q' : hom-slice f (map-emb i'))
  (Hi' : is-image f i' q')
  where

  abstract
    uniqueness-image :
      is-contr
        ( Σ ( equiv-slice (map-emb i) (map-emb i'))
            ( λ e →
              htpy-hom-slice f
                ( map-emb i')
                ( comp-hom-slice f
                  ( map-emb i)
                  ( map-emb i')
                  ( hom-equiv-slice (map-emb i) (map-emb i') e)
                  ( q))
                ( q')))
    uniqueness-image =
      is-contr-equiv
        ( Σ ( Σ ( hom-slice (map-emb i) (map-emb i'))
                ( λ h →
                  htpy-hom-slice f
                    ( map-emb i')
                    ( comp-hom-slice f (map-emb i) (map-emb i') h q)
                    ( q')))
            ( λ h → is-equiv (pr1 (pr1 h))))
        ( ( equiv-right-swap-Σ) ∘e
          ( equiv-Σ
            ( λ h →
              htpy-hom-slice f
                ( map-emb i')
                ( comp-hom-slice f (map-emb i) (map-emb i') (pr1 h) q)
                ( q'))
            ( equiv-right-swap-Σ)
            ( λ ((e , E) , H) → id-equiv)))
        ( is-contr-equiv
          ( is-equiv
            ( map-hom-slice-universal-property-image f i q Hi i' q'))
          ( left-unit-law-Σ-is-contr
            ( universal-property-image f i q Hi i' q')
            ( center (universal-property-image f i q Hi i' q')))
          ( is-proof-irrelevant-is-prop
            ( is-property-is-equiv
              ( map-hom-slice-universal-property-image f i q Hi i' q'))
            ( is-equiv-is-image-is-image f i q i' q'
              ( hom-slice-universal-property-image f i q Hi i' q')
              ( Hi)
              ( Hi'))))

  equiv-slice-uniqueness-image : equiv-slice (map-emb i) (map-emb i')
  equiv-slice-uniqueness-image =
    pr1 (center uniqueness-image)

  hom-equiv-slice-uniqueness-image : hom-slice (map-emb i) (map-emb i')
  hom-equiv-slice-uniqueness-image =
    hom-equiv-slice (map-emb i) (map-emb i') (equiv-slice-uniqueness-image)

  map-hom-equiv-slice-uniqueness-image : B → B'
  map-hom-equiv-slice-uniqueness-image =
    map-hom-slice (map-emb i) (map-emb i') (hom-equiv-slice-uniqueness-image)

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-image :
      is-equiv map-hom-equiv-slice-uniqueness-image
    is-equiv-map-hom-equiv-slice-uniqueness-image =
      is-equiv-map-equiv (pr1 equiv-slice-uniqueness-image)

  equiv-equiv-slice-uniqueness-image : B ≃ B'
  pr1 equiv-equiv-slice-uniqueness-image = map-hom-equiv-slice-uniqueness-image
  pr2 equiv-equiv-slice-uniqueness-image =
    is-equiv-map-hom-equiv-slice-uniqueness-image

  triangle-hom-equiv-slice-uniqueness-image :
    (map-emb i) ~ (map-emb i' ∘ map-hom-equiv-slice-uniqueness-image)
  triangle-hom-equiv-slice-uniqueness-image =
    triangle-hom-slice
      ( map-emb i)
      ( map-emb i')
      ( hom-equiv-slice-uniqueness-image)

  htpy-equiv-slice-uniqueness-image :
    htpy-hom-slice f
      ( map-emb i')
      ( comp-hom-slice f
        ( map-emb i)
        ( map-emb i')
        ( hom-equiv-slice-uniqueness-image)
        ( q))
      ( q')
  htpy-equiv-slice-uniqueness-image =
    pr2 (center uniqueness-image)

  htpy-map-hom-equiv-slice-uniqueness-image :
    ( map-hom-equiv-slice-uniqueness-image ∘ map-hom-slice f (map-emb i) q) ~
    ( map-hom-slice f (map-emb i') q')
  htpy-map-hom-equiv-slice-uniqueness-image =
    pr1 htpy-equiv-slice-uniqueness-image

  tetrahedron-hom-equiv-slice-uniqueness-image :
    ( ( ( triangle-hom-slice f (map-emb i) q) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-image) ·r
          ( map-hom-slice f (map-emb i) q))) ∙h
      ( map-emb i' ·l htpy-map-hom-equiv-slice-uniqueness-image)) ~
    ( triangle-hom-slice f (map-emb i') q')
  tetrahedron-hom-equiv-slice-uniqueness-image =
    pr2 htpy-equiv-slice-uniqueness-image

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  {B : UU l3} (i : B ↪ X) (q : hom-slice f (map-emb i))
  (H : is-image f i q)
  where

  abstract
    uniqueness-im :
      is-contr
        ( Σ ( equiv-slice (inclusion-im f) (map-emb i))
            ( λ e →
              htpy-hom-slice f
                ( map-emb i)
                ( comp-hom-slice f
                  ( inclusion-im f)
                  ( map-emb i)
                  ( hom-equiv-slice (inclusion-im f) (map-emb i) e)
                  ( unit-im f))
                ( q)))
    uniqueness-im =
      uniqueness-image f (emb-im f) (unit-im f) (is-image-im f) i q H

  equiv-slice-uniqueness-im : equiv-slice (inclusion-im f) (map-emb i)
  equiv-slice-uniqueness-im =
    pr1 (center uniqueness-im)

  hom-equiv-slice-uniqueness-im : hom-slice (inclusion-im f) (map-emb i)
  hom-equiv-slice-uniqueness-im =
    hom-equiv-slice (inclusion-im f) (map-emb i) equiv-slice-uniqueness-im

  map-hom-equiv-slice-uniqueness-im : im f → B
  map-hom-equiv-slice-uniqueness-im =
    map-hom-slice (inclusion-im f) (map-emb i) hom-equiv-slice-uniqueness-im

  abstract
    is-equiv-map-hom-equiv-slice-uniqueness-im :
      is-equiv map-hom-equiv-slice-uniqueness-im
    is-equiv-map-hom-equiv-slice-uniqueness-im =
      is-equiv-map-equiv (pr1 equiv-slice-uniqueness-im)

  equiv-equiv-slice-uniqueness-im : im f ≃ B
  pr1 equiv-equiv-slice-uniqueness-im = map-hom-equiv-slice-uniqueness-im
  pr2 equiv-equiv-slice-uniqueness-im =
    is-equiv-map-hom-equiv-slice-uniqueness-im

  triangle-hom-equiv-slice-uniqueness-im :
    (inclusion-im f) ~ (map-emb i ∘ map-hom-equiv-slice-uniqueness-im)
  triangle-hom-equiv-slice-uniqueness-im =
    triangle-hom-slice
      ( inclusion-im f)
      ( map-emb i)
      ( hom-equiv-slice-uniqueness-im)

  htpy-equiv-slice-uniqueness-im :
    htpy-hom-slice f
      ( map-emb i)
      ( comp-hom-slice f
        ( inclusion-im f)
        ( map-emb i)
        ( hom-equiv-slice-uniqueness-im)
        ( unit-im f))
      ( q)
  htpy-equiv-slice-uniqueness-im =
    pr2 (center uniqueness-im)

  htpy-map-hom-equiv-slice-uniqueness-im :
    ( ( map-hom-equiv-slice-uniqueness-im) ∘
      ( map-hom-slice f (inclusion-im f) (unit-im f))) ~
    ( map-hom-slice f (map-emb i) q)
  htpy-map-hom-equiv-slice-uniqueness-im =
    pr1 htpy-equiv-slice-uniqueness-im

  tetrahedron-hom-equiv-slice-uniqueness-im :
    ( ( ( triangle-hom-slice f (inclusion-im f) (unit-im f)) ∙h
        ( ( triangle-hom-equiv-slice-uniqueness-im) ·r
          ( map-hom-slice f (inclusion-im f) (unit-im f)))) ∙h
      ( map-emb i ·l htpy-map-hom-equiv-slice-uniqueness-im)) ~
    ( triangle-hom-slice f (map-emb i) q)
  tetrahedron-hom-equiv-slice-uniqueness-im =
    pr2 htpy-equiv-slice-uniqueness-im
```
