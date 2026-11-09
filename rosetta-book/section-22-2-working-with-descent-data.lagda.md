# Section 22.2 Working with descent data

```agda
module section-22-2-working-with-descent-data where

open import universe-levels
open import section-2-1-the-rules-for-dependent-function-types
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import exercise-11-2-paths-along-equivalences
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import exercise-13-1-homotopy-operations-equivalences
open import exercise-13-12-dependent-products-of-truncated-maps
open import section-19-5-the-eckmann-hilton-argument
open import section-21-1-the-induction-principle-of-the-circle
open import section-21-2-the-dependent-universal-property-of-the-circle
open import section-22-1-the-universal-cover-of-the-circle
```

The equivalence

```text
(S¹ → 𝒰) ≃ Σ(X : 𝒰) X ≃ X
```

yields that for any type family `A` over the circle the type of descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy `H` witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes is contractible.
In the remainder of this section we study arbitrary type families over the circle equipped with such descent data, which will put us in a good position to prove things about the universal cover of the circle.

## Proposition 22.2.1

Consider a type family `A` over the circle and consider descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Furthermore, consider two elements `x,y : X`.
Then we have an equivalence

```text
ᾱ : (e(x) = y) ≃ (tr_A(loop,α(x)) = α(y)).
```

### Proof

Note that the commutativity of the square implies that

```text
tr_A(loop,α(x)) = α(e(x)).
```

By Theorem 11.2.2 it therefore suffices to prove that the total space

```text
Σ(y : X) tr_A(loop,α(x)) = α(y)
```

is contractible.
This type is equivalent to `fib(α, tr_A(loop,α(x)))`, which is contractible because `α` is an equivalence. ◻

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  map-compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    map-aut-family-with-descent-data-circle A x ＝ y →
    dependent-identification (family-family-with-descent-data-circle A)
      ( loop-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x)
      ( map-equiv-family-with-descent-data-circle A y)
  map-compute-dependent-identification-loop-circle x y q =
    inv (coherence-square-family-with-descent-data-circle A x) ∙
    ( ap (map-equiv-family-with-descent-data-circle A) q)

  is-equiv-map-compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    is-equiv (map-compute-dependent-identification-loop-circle x y)
  is-equiv-map-compute-dependent-identification-loop-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fiber
          ( map-equiv-family-with-descent-data-circle A)
          ( tr
            ( family-family-with-descent-data-circle A)
            ( loop-free-loop l)
            ( map-equiv-family-with-descent-data-circle A x)))
        ( equiv-fiber _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv (equiv-family-with-descent-data-circle A))
          ( tr
            ( family-family-with-descent-data-circle A)
            ( loop-free-loop l)
            ( map-equiv-family-with-descent-data-circle A x))))
      ( map-compute-dependent-identification-loop-circle x)
      ( y)

  compute-dependent-identification-loop-circle :
    ( x y : type-family-with-descent-data-circle A) →
    ( map-aut-family-with-descent-data-circle A x ＝ y) ≃
    ( dependent-identification
      ( family-family-with-descent-data-circle A)
      ( loop-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x)
      ( map-equiv-family-with-descent-data-circle A y))
  pr1 (compute-dependent-identification-loop-circle x y) =
    map-compute-dependent-identification-loop-circle x y
  pr2 (compute-dependent-identification-loop-circle x y) =
    is-equiv-map-compute-dependent-identification-loop-circle x y
```

In the following proposition we show that sections of a type family `A` equipped with descent data `(X,e)` are equivalently described as fixed points for `e : X ≃ X`.

## Proposition 22.2.2

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Then there is a commuting square

```text
    Π(t : S¹) A(t) -------------> Σ(x : X) e(x) = x
           |                              |
  ev_base  |                              | pr₁
           v                              v
        A(base) ------------------------> X
                           α⁻¹
```

in which the top map is an equivalence.

### Proof

By the dependent universal property of the circle we have an equivalence

```text
(Π(t : S¹) A(t)) ≃ Σ(x : A(base)) tr_A(loop,x) = x.
```

This equivalence fits in a commuting triangle

```text
                      Π(t : S¹) A(t)
                       /           \
                      /             \ dgen_{S¹}
                     /               \
                    v                 v
    Σ(x : X) e(x) = x ---------------> Σ(x : A(base)) tr_A(loop,x) = x
                         tot_α(ᾱ)
```

Define the map on the left by composing `dgen_{S¹}` with the inverse of the bottom equivalence `tot_α(ᾱ)`.
The triangle then commutes, and the map on the left is an equivalence.
Its first component is `α⁻¹ ∘ ev_base`, up to the inverse laws for `α`, so the square in the statement commutes. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-coherence-triangle-identifications :
    {x y z : A} (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (ap f left) (ap f right) (ap f top)
  map-coherence-triangle-identifications .(top ∙ right) right top refl =
    ap-concat f top right

  compute-refl-right-map-coherence-triangle-identifications :
    {x y : A} (p : x ＝ y) →
    inv right-unit ＝
    map-coherence-triangle-identifications p refl p (inv right-unit)
  compute-refl-right-map-coherence-triangle-identifications refl = refl

  compute-refl-top-map-coherence-triangle-identifications :
    {x y : A} (p : x ＝ y) →
    refl ＝ map-coherence-triangle-identifications p p refl refl
  compute-refl-top-map-coherence-triangle-identifications p = refl

fixpoint-descent-data-circle :
  { l1 : Level}
  ( P : descent-data-circle l1) → UU l1
fixpoint-descent-data-circle P =
  Σ ( type-descent-data-circle P)
    ( λ x → (map-descent-data-circle P x) ＝ x)

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  ev-fixpoint-descent-data-circle :
    ( (x : S) → family-family-with-descent-data-circle A x) →
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A))
  pr1 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( equiv-family-with-descent-data-circle A)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( compute-dependent-identification-loop-circle
        ( l)
        ( A)
        ( map-inv-equiv
          ( equiv-family-with-descent-data-circle A)
          ( s (base-free-loop l)))
        ( map-inv-equiv
          ( equiv-family-with-descent-data-circle A)
          ( s (base-free-loop l))))
      ( ( ap
          ( tr (family-family-with-descent-data-circle A) (loop-free-loop l))
          ( is-section-map-inv-equiv
            ( equiv-family-with-descent-data-circle A)
            ( s (base-free-loop l)))) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv
            ( is-section-map-inv-equiv
              ( equiv-family-with-descent-data-circle A)
              ( s (base-free-loop l))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loop :
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)) ≃
    ( free-dependent-loop l (family-family-with-descent-data-circle A))
  equiv-fixpoint-descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( λ x →
        dependent-identification
          ( family-family-with-descent-data-circle A)
          ( loop-free-loop l)
          ( x)
          ( x))
      ( equiv-family-with-descent-data-circle A)
      ( λ x →
        compute-dependent-identification-loop-circle l A x x)

  comparison-fixpoint-descent-data-circle :
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)) →
    ( free-dependent-loop l (family-family-with-descent-data-circle A))
  comparison-fixpoint-descent-data-circle =
    map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  triangle-comparison-fixpoint-descent-data-circle :
    coherence-triangle-maps
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A))
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
  triangle-comparison-fixpoint-descent-data-circle s =
    eq-Eq-free-dependent-loop l
      ( family-family-with-descent-data-circle A)
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A) s)
      ( ( comparison-fixpoint-descent-data-circle ∘
          ev-fixpoint-descent-data-circle)
        ( s))
      ( inv is-section-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl
              { x =
                ap
                  ( tr
                    ( family-family-with-descent-data-circle A)
                    ( loop-free-loop l))
                  ( inv is-section-inv-α)})
            ( is-section-map-inv-is-equiv
              ( is-equiv-map-compute-dependent-identification-loop-circle
                ( l)
                ( A)
                ( map-inv-equiv
                  ( equiv-family-with-descent-data-circle A)
                  ( s (base-free-loop l)))
                ( pr1 (ev-fixpoint-descent-data-circle s)))
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv is-section-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( map-coherence-triangle-identifications
                  ( tr
                    ( family-family-with-descent-data-circle A)
                    ( loop-free-loop l))
                  ( refl)
                  ( is-section-inv-α)
                  ( inv is-section-inv-α)
                  ( inv (left-inv is-section-inv-α))))
              ( refl)))))
    where
    is-section-inv-α :
      eq-value
        ( map-equiv-family-with-descent-data-circle A ∘
          map-inv-equiv (equiv-family-with-descent-data-circle A))
        ( id)
        ( s (base-free-loop l))
    is-section-inv-α =
      is-section-map-inv-equiv
        ( equiv-family-with-descent-data-circle A)
        ( s (base-free-loop l))

  is-equiv-comparison-fixpoint-descent-data-circle :
    is-equiv comparison-fixpoint-descent-data-circle
  is-equiv-comparison-fixpoint-descent-data-circle =
    is-equiv-map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  is-equiv-ev-fixpoint-descent-data-circle :
    dependent-universal-property-circle l →
    is-equiv ev-fixpoint-descent-data-circle
  is-equiv-ev-fixpoint-descent-data-circle dup-circle =
    is-equiv-top-map-triangle
      ( ev-free-loop-Π l (family-family-with-descent-data-circle A))
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
      ( triangle-comparison-fixpoint-descent-data-circle)
      ( is-equiv-comparison-fixpoint-descent-data-circle)
      ( dup-circle (family-family-with-descent-data-circle A))

  equiv-ev-fixpoint-descent-data-circle :
    dependent-universal-property-circle l →
    ( (x : S) → (family-family-with-descent-data-circle A) x) ≃
    ( fixpoint-descent-data-circle
      ( descent-data-family-with-descent-data-circle A))
  pr1 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    ev-fixpoint-descent-data-circle
  pr2 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    is-equiv-ev-fixpoint-descent-data-circle dup-circle

  compute-ev-fixpoint-descent-data-circle :
    coherence-square-maps
      ( ev-fixpoint-descent-data-circle)
      ( ev-point (base-free-loop l))
      ( pr1)
      ( map-inv-equiv (equiv-family-with-descent-data-circle A))
  compute-ev-fixpoint-descent-data-circle = refl-htpy
```

The following corollary can be used to compare type families over the circle.
In particular, we will use it to compare the identity type of the circle with the universal cover.

## Corollary 22.2.3

Consider two type families `A` and `B` over the circle equipped with descent data `(X,e)` and `(Y,f)`, equivalences `α : X ≃ A(base)` and `β : Y ≃ B(base)`, and homotopies `H` and `K` witnessing that the squares

```text
 [X] --α-->[A(base)]         [Y] --β-->[B(base)]
  |           |               |           |
e |           | tr_A(loop)  f |           | tr_B(loop)
  V           V               V           V
 [X] --α-->[A(base)]         [Y] --β-->[B(base)]
```

commute, respectively.
Then there is a commuting square

```text
  (Π(t : S¹) A(t) → B(t)) -------------> Σ(h : X → Y) h ∘ e ~ f ∘ h
             |                                        |
    ev_base  |                                        | pr₁
             v                                        v
    (A(base) → B(base)) -------------------------> (X → Y)
                              h ↦ β⁻¹ ∘ h ∘ α
```

in which the top map is an equivalence.

### Proof

The claim follows once we observe that `(Y^X,λ h. f ∘ h ∘ e^{-1})` is descent data for the family of types `(A(t) → B(t))` indexed by `t : S¹`.
Indeed, we have the equivalence `h ↦ β ∘ h ∘ α^{-1} : Y^X ≃ B(base)^{A(base)}` for which the square

```text
                        h ↦ β ∘ h ∘ α⁻¹
                  Y^X ------------------> B(base)^{A(base)}
                   |                              |
  h ↦ f ∘ h ∘ e⁻¹  |                              | tr_{t ↦ A(t) → B(t)}(loop)
                   v                              v
                  Y^X ------------------> B(base)^{A(base)}
                        h ↦ β ∘ h ∘ α⁻¹
```

commutes. ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ (tr C p ∘ (f ∘ tr B (inv p)))
  tr-function-type refl f = refl

  compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ( (b : B x) → tr C p (f b) ＝ g (tr B p b)) ≃
    ( dependent-identification (λ a → B a → C a) p f g)
  compute-dependent-identification-function-type refl f g =
    inv-equiv equiv-funext

  map-compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) →
    dependent-identification (λ a → B a → C a) p f g
  map-compute-dependent-identification-function-type p f g =
    map-equiv (compute-dependent-identification-function-type p f g)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
  where

  horizontal-concat-htpy : ({x : A} → g {x} ~ g' {x}) → f ~ f' → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy G F = (g ·l F) ∙h (G ·r f')

  horizontal-concat-htpy' :
    ({x : A} → g {x} ~ g' {x}) → f ~ f' → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy' G F = (G ·r f) ∙h (g' ·l F)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (e : A ≃ B)
  where

  equiv-coherence-triangle-maps-inv-top' :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps' right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top' =
    equiv-Π
      ( λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a →
        equiv-concat
          ( ap left (is-retraction-map-inv-equiv e a))
          ( right (map-equiv e a)))

  equiv-coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top =
    ( equiv-inv-htpy
      ( left ∘ (map-inv-equiv e))
      ( right)) ∘e
    ( equiv-coherence-triangle-maps-inv-top')

  coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) →
    coherence-triangle-maps right left (map-inv-equiv e)
  coherence-triangle-maps-inv-top =
    map-equiv equiv-coherence-triangle-maps-inv-top

module _
  {l1 l2 : Level}
  (X : Type-With-Automorphism l1) (Y : Type-With-Automorphism l2)
  where

  hom-Type-With-Automorphism : UU (l1 ⊔ l2)
  hom-Type-With-Automorphism =
    hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  map-hom-Type-With-Automorphism :
    hom-Type-With-Automorphism →
    type-Type-With-Automorphism X → type-Type-With-Automorphism Y
  map-hom-Type-With-Automorphism =
    map-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

  coherence-square-hom-Type-With-Automorphism :
    (f : hom-Type-With-Automorphism) →
    coherence-square-maps
      ( map-hom-Type-With-Automorphism f)
      ( map-Type-With-Automorphism X)
      ( map-Type-With-Automorphism Y)
      ( map-hom-Type-With-Automorphism f)
  coherence-square-hom-Type-With-Automorphism =
    coherence-square-hom-Type-With-Endomorphism
      ( type-with-endomorphism-Type-With-Automorphism X)
      ( type-with-endomorphism-Type-With-Automorphism Y)

hom-descent-data-circle :
  { l1 l2 : Level}
  ( P : descent-data-circle l1) (Q : descent-data-circle l2) →
  UU (l1 ⊔ l2)
hom-descent-data-circle = hom-Type-With-Automorphism

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( h : hom-descent-data-circle P Q)
  where

  map-hom-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-hom-descent-data-circle =
    map-hom-Type-With-Automorphism P Q h

  coherence-square-hom-descent-data-circle :
    coherence-square-maps
      ( map-hom-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-hom-descent-data-circle)
  coherence-square-hom-descent-data-circle =
    coherence-square-hom-Type-With-Automorphism P Q h

module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-descent-data-circle-function-type : S → UU (l2 ⊔ l3)
  family-descent-data-circle-function-type x =
    family-family-with-descent-data-circle A x →
    family-family-with-descent-data-circle B x

  descent-data-circle-function-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-function-type =
    type-family-with-descent-data-circle A →
    type-family-with-descent-data-circle B
  pr2 descent-data-circle-function-type =
    ( equiv-postcomp
      ( type-family-with-descent-data-circle A)
      ( aut-family-with-descent-data-circle B)) ∘e
    ( equiv-precomp
      ( inv-equiv (aut-family-with-descent-data-circle A))
      ( type-family-with-descent-data-circle B))

module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  eq-descent-data-circle-function-type :
    equiv-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( descent-data-family-circle
        ( l)
        ( family-descent-data-circle-function-type l A B))
  pr1 eq-descent-data-circle-function-type =
    ( equiv-postcomp
      ( family-family-with-descent-data-circle A (base-free-loop l))
      ( equiv-family-with-descent-data-circle B)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-with-descent-data-circle A))
      ( type-family-with-descent-data-circle B))
  pr2 eq-descent-data-circle-function-type h =
    ( eq-htpy
      ( horizontal-concat-htpy
        ( coherence-square-family-with-descent-data-circle B)
        ( h ·l
          inv-htpy
            ( coherence-square-maps-inv-equiv
              ( equiv-family-with-descent-data-circle A)
              ( aut-family-with-descent-data-circle A)
              ( equiv-tr
                ( family-family-with-descent-data-circle A)
                ( loop-free-loop l))
              ( equiv-family-with-descent-data-circle A)
              ( coherence-square-family-with-descent-data-circle A))))) ∙
    ( inv
      ( ( tr-function-type
          ( family-family-with-descent-data-circle A)
          ( family-family-with-descent-data-circle B) (loop-free-loop l))
        ( map-equiv-descent-data-circle
          ( descent-data-circle-function-type l A B)
          ( descent-data-family-circle
            ( l)
            ( family-descent-data-circle-function-type l A B))
          ( eq-descent-data-circle-function-type)
          ( h))))

  family-with-descent-data-circle-function-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 family-with-descent-data-circle-function-type =
    family-descent-data-circle-function-type l A B
  pr1 (pr2 family-with-descent-data-circle-function-type) =
    descent-data-circle-function-type l A B
  pr2 (pr2 family-with-descent-data-circle-function-type) =
    eq-descent-data-circle-function-type

module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  equiv-fixpoint-descent-data-circle-function-type-hom :
    fixpoint-descent-data-circle (descent-data-circle-function-type l A B) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-fixpoint-descent-data-circle-function-type-hom =
    equiv-tot
      ( λ h →
        ( equiv-inv-htpy
          ( map-aut-family-with-descent-data-circle B ∘ h)
          ( h ∘ map-aut-family-with-descent-data-circle A)) ∘e
        ( inv-equiv
          ( equiv-coherence-triangle-maps-inv-top
            ( map-aut-family-with-descent-data-circle B ∘ h)
            ( h)
            ( aut-family-with-descent-data-circle A))) ∘e
        ( equiv-inv-htpy _ _) ∘e
        ( equiv-funext))

  equiv-descent-data-family-circle-function-type-hom :
    dependent-universal-property-circle l →
    ( (x : S) → family-descent-data-circle-function-type l A B x) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-descent-data-family-circle-function-type-hom dup-circle =
    equiv-fixpoint-descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( family-with-descent-data-circle-function-type l A B)
      ( dup-circle))
```

## Corollary 22.2.4

Consider a type family `A` over the circle and descent data `(X,e)` equipped with an equivalence `α : X ≃ A(base)` and a homotopy witnessing that the square

```text
 [X] --α-->[A(base)]
  |           |
e |           | tr_A(loop)
  V           V
 [X] --α-->[A(base)]
```

commutes.
Then there is a commuting square

```text
  (Π(t : S¹) E_{S¹}(t) → A(t)) -------------> Σ(h : ℤ → X) h ∘ succ-ℤ ~ e ∘ h
                |                                            |
       ev_base  |                                            | pr₁
                v                                            v
    (E_{S¹}(base) → A(base)) ---------------------------> (ℤ → X)
                                h ↦ α⁻¹ ∘ h ∘ (k ↦ k_E)
```

in which the top map is an equivalence.

In other words, a family of maps `E_{S¹}(t) → A(t)` indexed by `t : S¹` is equivalently described as a map `h : ℤ → X` for which the square

```text
      [ℤ] --h--> [X]
       |          |
succ-ℤ |          | e
       V          V
      [ℤ] --h--> [X]
```

commutes.

BENCHMARK PROBLEM

It is now time to prove the universal property of the integers.
