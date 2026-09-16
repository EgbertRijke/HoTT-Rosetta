# Section 11.6 The structure identity principle

```agda
module section-11-6-the-structure-identity-principle where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import exercise-9-4-three-for-two-equivalences
open import exercise-10-3-contractible-equivalences
open import exercise-10-6-dependent-pair-contractible-base
open import section-5-4-transport
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-3-contractible-maps
open import exercise-9-1-groupoid-operations-equivalences
```

We often encounter a type consisting of certain objects equipped with further structure.
For example, the fiber of a map `f : A → B` at `b : B` is the type of elements `a : A` equipped with an identification `p : f(a) = b`.
Such *structure* types occur all over mathematics, and it is important to have an efficient characterization of their identity types.
A general structure type is just a `Σ`-type, and we’re asking for a characterization of its identity type.

Recall from Theorem 9.3.4 that the identity type of the type `Σ(x : A) B(x)` at a pair `(a,b)` can be characterized as

```text
  ((a,b) = (x,y)) ≃ Σ(p : a = x) tr_B(p,b) = y.
```

However, this characterization of the identity type of `Σ(x : A) B(x)` is not as clear and useful as we like it to be, because it uses the transport function, which is completely generic.
Our plan is to use identity systems on `A` and on `B(a)` to arrive at a more useful characterization of the identity type of `Σ(x : A) B(x)`.

In order to abstract away this characterization of the identity type of `Σ(x : A) B(x)`, let `C : A → 𝒰` be the family of types given by `C(x) ≔ (a = x)`, and let

```text
  D : Π(x : A) B(x) → (C(x) → 𝒰)
```

be the family of types given by `D(x,y,p) ≔ tr_B(p,b) = y`.
Then `C` is an identity system on `A` at `a`, and the type family `y ↦ D(a,y,refl)` is an identity system on `B(a)` at `b`.
This suggests the following definition of dependent identity systems.

## Definition 11.6.1

Consider a type `A` equipped with an identity system `C` based at `a : A`, and let `c : C(a)`.
Furthermore, consider a type family `B` over `A`.
A **dependent identity system** over `C` at `b : B(a)` consists of a type family

```text
  D : Π(x : A) B(x) → (C(x) → 𝒰)
```

equipped with an element `d : D(a,b,c)` such that `y ↦ D(a,y,c)` is an identity system at `b`.

###

Note: It seems agda-unimath doesn't have a definition of dependent identity system.

## Theorem 11.6.2

Consider a type family `B` over `A`, elements `a : A` and `b : B(a)`, and an identity system `C` of `A` with `c : C(a)`.
Furthermore, consider a type family

```text
  D : Π(x : A) B(x) → (C(x) → 𝒰)
```

equipped with an element `d : D(a,b,c)`.
Then the following are equivalent:

1. Any family of maps

   ```text
     (b = y) → D(a,y,c)
   ```
   
   indexed by `y : B(a)` is a family of equivalences.

2. The total space

   ```text
     Σ(y : B(a)) D(a,y,c)
   ```

   is contractible.

3. `D` is a dependent identity system over `C` at `b : B(a)`.

4. Any family of maps

   ```text
     ((a,b) = (x,y)) → Σ(z : C(x)) D(x,y,z)
   ```

   indexed by `(x,y) : Σ(x : A) B(x)` is a family of equivalences.

5. The total space

   ```text
     Σ((x,y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x,y,z)
   ```

   is contractible.

6. The type family

   ```text
     (x,y) ↦ Σ(z : C(x)) D(x,y,z)
   ```
   
   is an identity system at `(a,b) : Σ(x : A) B(x)`.

### Proof

The first three statements as well as the last three statements are equivalent by Theorem 11.2.2.
Therefore it suffices to show that (ii) and (v) are equivalent.
Note that there is an equivalence

```text
  Σ((x,y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x,y,z)
  ≃
  Σ((x,z) : Σ(x : A) C(x)) Σ(y : B(x)) D(x,y,z).
```

This equivalence, its inverse, and the homotopies witnessing that the inverse is indeed an inverse are all straightforward to construct using pattern matching.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3}
  ( D : (x : A) → B x → C x → Type l4)
  where

  map-interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 (pr1 (map-interchange-Σ-Σ t)) = pr1 (pr1 t)
  pr2 (pr1 (map-interchange-Σ-Σ t)) = pr1 (pr2 t)
  pr1 (pr2 (map-interchange-Σ-Σ t)) = pr2 (pr1 t)
  pr2 (pr2 (map-interchange-Σ-Σ t)) = pr2 (pr2 t)

  map-inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 (pr1 (map-inv-interchange-Σ-Σ t)) = pr1 (pr1 t)
  pr2 (pr1 (map-inv-interchange-Σ-Σ t)) = pr1 (pr2 t)
  pr1 (pr2 (map-inv-interchange-Σ-Σ t)) = pr2 (pr1 t)
  pr2 (pr2 (map-inv-interchange-Σ-Σ t)) = pr2 (pr2 t)

  is-section-map-inv-interchange-Σ-Σ :
    map-interchange-Σ-Σ ∘ map-inv-interchange-Σ-Σ ~ id
  is-section-map-inv-interchange-Σ-Σ ((a , c) , (b , d)) = refl

  is-retraction-map-inv-interchange-Σ-Σ :
    map-inv-interchange-Σ-Σ ∘ map-interchange-Σ-Σ ~ id
  is-retraction-map-inv-interchange-Σ-Σ ((a , b) , (c , d)) = refl

  is-equiv-map-interchange-Σ-Σ : is-equiv map-interchange-Σ-Σ
  is-equiv-map-interchange-Σ-Σ =
    is-equiv-is-invertible
      map-inv-interchange-Σ-Σ
      is-section-map-inv-interchange-Σ-Σ
      is-retraction-map-inv-interchange-Σ-Σ

  is-equiv-map-inv-interchange-Σ-Σ : is-equiv map-inv-interchange-Σ-Σ
  is-equiv-map-inv-interchange-Σ-Σ =
    is-equiv-is-invertible
      map-interchange-Σ-Σ
      is-retraction-map-inv-interchange-Σ-Σ
      is-section-map-inv-interchange-Σ-Σ

  interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) ≃
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 interchange-Σ-Σ = map-interchange-Σ-Σ
  pr2 interchange-Σ-Σ = is-equiv-map-interchange-Σ-Σ

  inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) ≃
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 inv-interchange-Σ-Σ = map-inv-interchange-Σ-Σ
  pr2 inv-interchange-Σ-Σ = is-equiv-map-inv-interchange-Σ-Σ
```

Furthermore, notice that the type `Σ(x : A) C(x)` is contractible with center of contraction `(a,c)` since `C` is assumed to be an identity system at `a : A`.
Therefore it follows that

```text
  Σ((x,y) : Σ(x : A) B(x)) Σ(z : C(x)) D(x,y,z) ≃ Σ(y : B(a)) D(a,y,c). ◻
```

```agda
module _
  { l1 l2 l3 l4 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3}
  { D : (x : A) → B x → C x → Type l4}
  where

  abstract
    is-torsorial-Eq-structure :
      (is-torsorial-AC : is-torsorial C) (t : Σ A C) →
      is-torsorial (λ y → D (pr1 t) y (pr2 t)) →
      is-torsorial (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
    is-torsorial-Eq-structure is-torsorial-AC t is-torsorial-BD =
      is-contr-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
        ( interchange-Σ-Σ D)
        ( is-contr-Σ is-torsorial-AC t is-torsorial-BD)

module _
  {l1 l2 l3 l4 : Level} {A : Type l1} {B : A → Type l2} {Eq-A : A → Type l3}
  (Eq-B : {x : A} → B x → Eq-A x → Type l4)
  {a : A} {b : B a} (refl-A : Eq-A a) (refl-B : Eq-B b refl-A)
  where

  abstract
    structure-identity-principle :
      {f : (x : A) → a ＝ x → Eq-A x}
      {g : (y : B a) → b ＝ y → Eq-B y refl-A} →
      (h : (z : Σ A B) → (pair a b) ＝ z → Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))) →
      ((x : A) → is-equiv (f x)) → ((y : B a) → is-equiv (g y)) →
      (z : Σ A B) → is-equiv (h z)
    structure-identity-principle {f} {g} h H K =
      fundamental-theorem-id
        ( is-torsorial-Eq-structure
          ( fundamental-theorem-id' f H)
          ( pair a refl-A)
          ( fundamental-theorem-id' g K))
        ( h)

  map-extensionality-Σ :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x)
    (g : (y : B a) → (b ＝ y) ≃ Eq-B y refl-A) →
    (z : Σ A B) → pair a b ＝ z → Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))
  pr1 (map-extensionality-Σ f g .(pair a b) refl) = refl-A
  pr2 (map-extensionality-Σ f g .(pair a b) refl) = refl-B

  extensionality-Σ :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x)
    (g : (y : B a) → (b ＝ y) ≃ Eq-B y refl-A) →
    (z : Σ A B) → (pair a b ＝ z) ≃ Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))
  pr1 (extensionality-Σ f g z) = map-extensionality-Σ f g z
  pr2 (extensionality-Σ f g z) =
    structure-identity-principle
      ( map-extensionality-Σ f g)
      ( λ x → is-equiv-map-equiv (f x))
      ( λ y → is-equiv-map-equiv (g y))
      ( z)
```

### Note: It seems that agda-unimath doesn't explicitly develop the equivalence between all 6 statements. Instead, the equivalences that are actually used are formalized and the equivalences that are not used not.

## Example 11.6.3

By the structure identity principle of Theorem 11.6.2 in combination with the fundamental theorem of identity types (Theorem 11.2.2), it becomes completely routine to characterize identity types of structures: We only have to show that the types

```text
  Σ(x : A) C(x)    and    Σ(y : B(a)) D(a,y,c)
```

are contractible.
To illustrate this use of the structure identity principle, we give an alternative characterization of the fiber of a map `f : A → B` at `b : B`.
We claim that

```text
  ((x,p) = (y,q)) ≃ fib(ap{f}, p ∙ q⁻¹) ≐ Σ(α : x = y) ap_{f}(α) = p ∙ q⁻¹.
```

To see this, we apply Theorem 11.6.2.
Note that `Σ(y : A) x = y` is contractible by Theorem 10.1.4 with center of contraction `(x,refl)`.
Therefore it suffices to show that the type

```text
  Σ(q : f(x) = b) refl = p ∙ q⁻¹
```

is contractible.
Of course, this type is equivalent to `Σ(q : f(x) = b) p = q`, which is again contractible by Theorem 10.1.4.

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {b : B}
  where

  fiber-ap-eq-fiber-fiberwise :
    (s t : fiber f b) (p : pr1 s ＝ pr1 t) →
    tr (λ (a : A) → f a ＝ b) p (pr2 s) ＝ pr2 t →
    ap f p ＝ pr2 s ∙ inv (pr2 t)
  fiber-ap-eq-fiber-fiberwise (.x' , p) (x' , refl) refl =
    inv ∘ concat right-unit refl

  abstract
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise :
      (s t : fiber f b) → is-fiberwise-equiv (fiber-ap-eq-fiber-fiberwise s t)
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise (x , y) (.x , refl) refl =
      is-equiv-comp
        ( inv)
        ( concat right-unit refl)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fiber-ap-eq-fiber :
    (s t : fiber f b) → s ＝ t →
    fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t))
  pr1 (fiber-ap-eq-fiber s .s refl) = refl
  pr2 (fiber-ap-eq-fiber s .s refl) = inv (right-inv (pr2 s))

  triangle-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    fiber-ap-eq-fiber s t ~
    tot (fiber-ap-eq-fiber-fiberwise s t) ∘ pair-eq-Σ {s = s} {t}
  triangle-fiber-ap-eq-fiber (x , refl) .(x , refl) refl = refl

  abstract
    is-equiv-fiber-ap-eq-fiber :
      (s t : fiber f b) → is-equiv (fiber-ap-eq-fiber s t)
    is-equiv-fiber-ap-eq-fiber s t =
      is-equiv-left-map-triangle
        ( fiber-ap-eq-fiber s t)
        ( tot (fiber-ap-eq-fiber-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fiber-ap-eq-fiber s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise s t))

  equiv-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    (s ＝ t) ≃ fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t))
  pr1 (equiv-fiber-ap-eq-fiber s t) = fiber-ap-eq-fiber s t
  pr2 (equiv-fiber-ap-eq-fiber s t) = is-equiv-fiber-ap-eq-fiber s t

  map-inv-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t)) →
    s ＝ t
  map-inv-fiber-ap-eq-fiber (x , refl) (.x , p) (refl , u) =
    eq-pair-eq-fiber (ap inv u ∙ inv-inv p)

  ap-pr1-map-inv-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    (v : fiber (ap f {x = pr1 s} {y = pr1 t}) (pr2 s ∙ inv (pr2 t))) →
    ap pr1 (map-inv-fiber-ap-eq-fiber s t v) ＝ pr1 v
  ap-pr1-map-inv-fiber-ap-eq-fiber (x , refl) (.x , p) (refl , u) =
    ap-pr1-eq-pair-eq-fiber (ap inv u ∙ inv-inv p)

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (x y : A)
  where

  eq-fiber-fiber-ap :
    (q : f x ＝ f y) → (x , q) ＝ (y , refl) → fiber (ap f {x} {y}) q
  eq-fiber-fiber-ap q =
    tr (fiber (ap f)) right-unit ∘ fiber-ap-eq-fiber f (x , q) (y , refl)

  abstract
    is-equiv-eq-fiber-fiber-ap :
      (q : f x ＝ f y) → is-equiv (eq-fiber-fiber-ap q)
    is-equiv-eq-fiber-fiber-ap q =
      is-equiv-comp
        ( tr (fiber (ap f)) right-unit)
        ( fiber-ap-eq-fiber f (x , q) (y , refl))
        ( is-equiv-fiber-ap-eq-fiber f (x , q) (y , refl))
        ( is-equiv-tr (fiber (ap f)) right-unit)
```
