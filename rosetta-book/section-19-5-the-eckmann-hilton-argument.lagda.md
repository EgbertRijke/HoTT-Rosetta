# Section 19.5 The Eckmann-Hilton argument

```agda
module section-19-5-the-eckmann-hilton-argument where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-1-distributive-inv-concat
open import exercise-5-2-inverse-concatenation-maps
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
open import section-12-3-sets
open import exercise-12-8-retracts-of-truncated-types
open import section-19-1-the-type-of-all-groups
open import section-19-2-group-homomorphisms
open import section-19-4-homotopy-groups-of-types
```

The Eckmann-Hilton argument is used to show that `πₙ(A)` is an abelian group for all `n ≥ 2`.
This is achieved by constructing an identification

```text
p ∙ q = q ∙ p
```

for all `p,q : Ω^2(A)`.
Note that identification elimination is not immediately applicable here, since both `p` and `q` are identifications of type `refl = refl` with neither endpoint free.
Therefore, we must come up with something else.

## Definition 19.5.1

Consider a binary operation `f : A → (B → C)`.
The **binary action on paths** of `f` is the family of functions

```text
ap-binary_f : (x = x') → ((y = y') → (f(x,y) = f(x',y')))
```

indexed by `x,x' : A` and `y,y' : B` given by `ap-binary_f(refl,refl) ≔ refl`.

## Lemma 19.5.2

The binary action on paths of `f : A → (B → C)` satisfies the following laws:

```text
ap-binary_f(refl,q) = ap_{f(x)}(q)
ap-binary_f(p,refl) = ap_{f(_,y)}(p)
```

and moreover both triangles in the following diagram commute:

```text
           [f(x,y)] ---ap_{f(_,y)}(p)--> [f(x',y)]
               |    \                        |
ap_{f(x,_)}(q) |        \ ap-binary_f(p,q)   | ap_{f(x',_)}(q)
               |            \                |
               |                \            |
               V                    V        V
           [f(x,y')] --ap_{f(_,y')}(p)--> [f(x',y')]
```

### Proof

_Proof._ The proof is immediate by identification elimination on `p` and `q`, where applicable. ◻

````agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  left-unit-ap-binary :
    {x : A} {y y' : B} (q : y ＝ y') → ap-binary f refl q ＝ ap (f x) q
  left-unit-ap-binary _ = refl

  right-unit-ap-binary :
    {x x' : A} (p : x ＝ x') {y : B} → ap-binary f p refl ＝ ap (λ r → f r y) p
  right-unit-ap-binary refl = refl

  triangle-ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (λ r → f r y) p ∙ ap (f x') q
  triangle-ap-binary _ _ = refl

  triangle-ap-binary' :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (f x) q ∙ ap (λ r → f r y') p
  triangle-ap-binary' refl refl = refl
```

## Example 19.5.3

One particular binary operation to which we can apply the binary action on paths is concatenation of identifications

```text
_ ∙ _ : (x = y) → ((y = z) → (x = z))
````

This results in the **horizontal concatenation** operation

```text
_ ∙ₕ _ : (p = p') → ((q = q') → (p ∙ q = p' ∙ q')).
```

In other words, for any two identifications `r : p = p'` and `s : q = q'` as in the diagram

```text
[x] ----p----> [y] ----q----> [z]
        ⇓ r            ⇓ s
[x] ----p'---> [y] ----q'---> [z]
```

The repeated endpoint labels in these diagrams denote the same points.
We obtain `r ∙ₕ s ≔ ap-binary_{_ ∙ _}(r,s) : p ∙ q = p' ∙ q'`.

```agda
horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  p ＝ q → u ＝ v → p ∙ u ＝ q ∙ v
horizontal-concat-Id² α β = ap-binary (_∙_) α β
```

The **vertical concatenation** operation, which concatenates `r : p = p'` and `r' : p' = p''` as in the diagram

```text
[x] ----p----> [y]
        ⇓ r
[x] ----p'---> [y]
        ⇓ r'
[x] ----p''--> [y]
```

is given by ordinary concatenation of identifications.

```agda
vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} → p ＝ q → q ＝ r → p ＝ r
vertical-concat-Id² α β = α ∙ β
```

## Lemma 19.5.4

Horizontal concatenation satisfies the following left and right unit laws:

```text
refl_refl ∙ₕ s = s
r ∙ₕ refl_refl = r.
```

### Proof

_Proof._ This follows by identification elimination on `r` and `s`, or alternatively via Lemma 19.5.2. ◻

```agda
left-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {β : p ＝ q} →
  vertical-concat-Id² refl β ＝ β
left-unit-law-vertical-concat-Id² = left-unit

right-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α : p ＝ q} →
  vertical-concat-Id² α refl ＝ α
right-unit-law-vertical-concat-Id² = right-unit

compute-left-refl-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : x ＝ y} {u v : y ＝ z} (γ : u ＝ v) →
  horizontal-concat-Id² refl γ ＝ left-whisker-concat p γ
compute-left-refl-horizontal-concat-Id² refl = refl

compute-right-refl-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) {u : y ＝ z} →
  horizontal-concat-Id² α refl ＝ right-whisker-concat α u
compute-right-refl-horizontal-concat-Id² refl = refl
```

In the following lemma we establish the **interchange law** for horizontal and vertical concatenation.

## Lemma 19.5.5

Consider a diagram of the form

```text
[x] ----p----> [y] ----q----> [z]
        ⇓ r            ⇓ s
[x] ----p'---> [y] ----q'---> [z]
        ⇓ r'           ⇓ s'
[x] ----p''--> [y] ----q''--> [z]
```

Then there is an identification

```text
(r ∙ r') ∙ₕ (s ∙ s') = (r ∙ₕ s) ∙ (r' ∙ₕ s').
```

### Proof

_Proof._ We use path induction on both `r` and `s`.
Then it suffices to show that

```text
(refl ∙ r') ∙ₕ (refl ∙ s') = (refl ∙ₕ refl) ∙ (r' ∙ₕ s')
```

Using the unit laws for ordinary concatenation, we see that both sides reduce to `r' ∙ₕ s'`. ◻

```agda
interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : x ＝ y} {u v w : y ＝ z}
  (α : p ＝ q) (β : q ＝ r) (γ : u ＝ v) (δ : v ＝ w) →
  ( horizontal-concat-Id²
    ( vertical-concat-Id² α β)
    ( vertical-concat-Id² γ δ)) ＝
  ( vertical-concat-Id²
    ( horizontal-concat-Id² α γ)
    ( horizontal-concat-Id² β δ))
interchange-Id² refl _ refl _ = refl
```

## Theorem 19.5.6

Consider a pointed type `A`, and let `r,s : Ω^2(A)`.
Then there is an identification

```text
r ∙ s = s ∙ r
```

### Proof

_Proof._ First we observe that `r ∙ s = r ∙ₕ s` by the following calculation using the unit laws from Lemma 19.5.4 and the interchange law from Lemma 19.5.5:

```text
r ∙ s = (r ∙ₕ refl_refl) ∙ (refl_refl ∙ₕ s)
= (r ∙ refl_refl) ∙ₕ (refl_refl ∙ s)
= r ∙ₕ s
```

Similarly, we observe that `r ∙ₕ s = s ∙ r` by the following calculation:

```text
r ∙ₕ s = (refl_refl ∙ r) ∙ₕ (s ∙ refl_refl)
= (refl_refl ∙ₕ s) ∙ (r ∙ₕ refl_refl)
= s ∙ r.
```

These two calculations combined prove the claim. ◻

```agda
module _
  {l : Level}
  where

  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = iterated-loop-space 2 A

  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = refl {x = a} ＝ refl {x = a}

  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl

vertical-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
vertical-concat-Ω² α β = vertical-concat-Id² α β

horizontal-concat-Ω² :
  {l : Level} {A : UU l} {a : A} → type-Ω² a → type-Ω² a → type-Ω² a
horizontal-concat-Ω² α β = horizontal-concat-Id² α β

module _
  {l : Level} {A : UU l}
  where

  left-unit-law-vertical-concat-Ω² :
    {a : A} {α : type-Ω² a} → vertical-concat-Ω² refl-Ω² α ＝ α
  left-unit-law-vertical-concat-Ω² = left-unit

  right-unit-law-vertical-concat-Ω² :
    {a : A} {α : type-Ω² a} → vertical-concat-Ω² α refl-Ω² ＝ α
  right-unit-law-vertical-concat-Ω² = right-unit

  left-unit-law-horizontal-concat-Ω² :
    {a : A} {α : type-Ω² a} →
    horizontal-concat-Ω² refl-Ω² α ＝ α
  left-unit-law-horizontal-concat-Ω² {α = α} =
    compute-left-refl-horizontal-concat-Id² α ∙ left-unit-law-left-whisker-concat α

  naturality-right-unit :
    {x y : A} {p q : x ＝ y} (α : p ＝ q) →
    coherence-square-identifications
      ( right-unit)
      ( right-whisker-concat α refl)
      ( α)
      ( right-unit)
  naturality-right-unit {p = refl} refl = refl

  naturality-right-unit-Ω² :
    {x : A} (α : type-Ω² x) → right-whisker-concat α refl ＝ α
  naturality-right-unit-Ω² α = inv right-unit ∙ naturality-right-unit α

  right-unit-law-horizontal-concat-Ω² :
    {a : A} {α : type-Ω² a} → horizontal-concat-Ω² α refl-Ω² ＝ α
  right-unit-law-horizontal-concat-Ω² {α = α} =
    compute-right-refl-horizontal-concat-Id² α ∙ naturality-right-unit-Ω² α

  left-unit-law-left-whisker-Ω² :
    {a : A} (α : type-Ω² a) → left-whisker-concat (refl-Ω (A , a)) α ＝ α
  left-unit-law-left-whisker-Ω² α =
    left-unit-law-left-whisker-concat α

  right-unit-law-right-whisker-Ω² :
    {a : A} (α : type-Ω² a) → right-whisker-concat α (refl-Ω (A , a)) ＝ α
  right-unit-law-right-whisker-Ω² α =
    inv (right-unit-law-right-whisker-concat α ∙ right-unit)

interchange-Ω² :
  {l : Level} {A : UU l} {a : A} (α β γ δ : type-Ω² a) →
  Id
    ( horizontal-concat-Ω² (vertical-concat-Ω² α β) (vertical-concat-Ω² γ δ))
    ( vertical-concat-Ω² (horizontal-concat-Ω² α γ) (horizontal-concat-Ω² β δ))
interchange-Ω² = interchange-Id²

module _
  {l : Level} {A : Pointed-Type l}
  where

  eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) → α ∙ β ＝ β ∙ α
  eckmann-hilton-Ω² α β =
    ( inv
      ( horizontal-concat-Id²
        ( left-unit-law-left-whisker-Ω² α)
        ( right-unit-law-right-whisker-Ω² β))) ∙
    ( commutative-left-whisker-right-whisker-concat α β) ∙
    ( horizontal-concat-Id²
      ( right-unit-law-right-whisker-Ω² β)
      ( left-unit-law-left-whisker-Ω² α))

  inv-eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) → α ∙ β ＝ β ∙ α
  inv-eckmann-hilton-Ω² α β =
    ( inv
      ( horizontal-concat-Id²
        ( right-unit-law-right-whisker-Ω² α)
        ( left-unit-law-left-whisker-Ω² β))) ∙
    ( commutative-right-whisker-left-whisker-concat α β) ∙
    ( horizontal-concat-Id²
      ( left-unit-law-left-whisker-Ω² β)
      ( right-unit-law-right-whisker-Ω² α))

  compute-inv-inv-eckmann-hilton-Ω² :
    (α β : type-Ω² (point-Pointed-Type A)) →
    inv (inv-eckmann-hilton-Ω² β α) ＝ eckmann-hilton-Ω² α β
  compute-inv-inv-eckmann-hilton-Ω² α β =
    ( distributive-inv-concat
      ( ( inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α))) ∙
        ( commutative-right-whisker-left-whisker-concat β α))
      ( horizontal-concat-Id²
        ( left-unit-law-left-whisker-Ω² α)
        ( right-unit-law-right-whisker-Ω² β))) ∙
    ( left-whisker-concat
      ( inv
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
      ( distributive-inv-concat
        ( inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α)))
        ( commutative-right-whisker-left-whisker-concat β α))) ∙
    ( left-whisker-concat
      ( inv
        ( horizontal-concat-Id²
          ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
      ( horizontal-concat-Id²
        ( compute-inv-commutative-right-whisker-left-whisker-concat α β)
        ( inv-inv
          ( horizontal-concat-Id²
            ( right-unit-law-right-whisker-Ω² β)
            ( left-unit-law-left-whisker-Ω² α))))) ∙
    ( inv
      ( assoc
        ( inv
          ( horizontal-concat-Id²
            ( left-unit-law-left-whisker-Ω² α)
            ( right-unit-law-right-whisker-Ω² β)))
        ( commutative-left-whisker-right-whisker-concat α β)
        ( horizontal-concat-Id²
          ( right-unit-law-right-whisker-Ω² β)
          ( left-unit-law-left-whisker-Ω² α))))
```

## Corollary 19.5.7

For `n ≥ 2`, the `n`-th homotopy group of any pointed type is abelian.

### Proof

BENCHMARK PROBLEM

_Proof._ By Proposition 19.4.6 it follows that `πₙ(A)` is isomorphic to the second homotopy group of some pointed type, for every `n ≥ 2`.
Therefore it suffices to prove the claim for `π₂(A)` for every pointed type `A`.

Our goal is to show that

```text
Π(r,s : π₂(A)) rs = sr.
```

Since we are constructing an identification in a set, we can use the dependent universal property of `0`-truncation on both `r` and `s`, stated in Theorem 18.5.2.
Therefore it suffices to show that

```text
Π(r,s : Ω^2(A)) η(r)η(s) = η(s)η(r).
```

The claim now follows, because

```text
η(r)η(s) = η(r ∙ s) = η(s ∙ r) = η(s)η(r).
```

 ◻

## Supplement

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  module _
    (H : is-pointed-equiv f)
    where

    coherence-point-is-section-map-inv-is-pointed-equiv :
      coherence-point-unpointed-htpy-pointed-Π
        ( f ∘∗ pointed-map-inv-is-pointed-equiv f H)
        ( id-pointed-map)
        ( is-section-map-inv-is-pointed-equiv f H)
    coherence-point-is-section-map-inv-is-pointed-equiv =
      ( right-whisker-concat
        ( ap-concat
          ( map-pointed-map f)
          ( inv (ap _ (preserves-point-pointed-map f)))
          ( _) ∙
          ( horizontal-concat-Id²
            ( ap-inv
              ( map-pointed-map f)
              ( ap _ (preserves-point-pointed-map f)) ∙
              ( inv
                ( ap
                  ( inv)
                  ( ap-comp
                    ( map-pointed-map f)
                    ( map-inv-is-pointed-equiv f H)
                    ( preserves-point-pointed-map f)))))
            ( inv (coherence-map-inv-is-equiv H (point-Pointed-Type A)))))
        ( preserves-point-pointed-map f)) ∙
      ( assoc
        ( inv
          ( ap
            ( map-pointed-map f ∘ map-inv-is-pointed-equiv f H)
            ( preserves-point-pointed-map f)))
        ( (is-section-map-inv-is-pointed-equiv f H) _)
        ( preserves-point-pointed-map f)) ∙
      ( inv
        ( ( right-unit) ∙
          ( left-transpose-eq-concat
            ( ap
              ( map-pointed-map f ∘ map-inv-is-pointed-equiv f H)
              ( preserves-point-pointed-map f))
            ( (is-section-map-inv-is-pointed-equiv f H) _)
            ( ( (is-section-map-inv-is-pointed-equiv f H) _) ∙
              ( preserves-point-pointed-map f))
            ( ( inv (nat-htpy (is-section-map-inv-is-pointed-equiv f H) _)) ∙
              ( left-whisker-concat
                ( (is-section-map-inv-is-pointed-equiv f H) _)
                ( ap-id (preserves-point-pointed-map f)))))))

    is-pointed-section-pointed-map-inv-is-pointed-equiv :
      is-pointed-section f (pointed-map-inv-is-pointed-equiv f H)
    pr1 is-pointed-section-pointed-map-inv-is-pointed-equiv =
      is-section-map-inv-is-pointed-equiv f H
    pr2 is-pointed-section-pointed-map-inv-is-pointed-equiv =
      coherence-point-is-section-map-inv-is-pointed-equiv

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  is-pointed-section-pointed-map-inv-pointed-equiv :
    is-pointed-section
      ( pointed-map-pointed-equiv e)
      ( pointed-map-inv-pointed-equiv e)
  is-pointed-section-pointed-map-inv-pointed-equiv =
    is-pointed-section-pointed-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv e)
      ( is-pointed-equiv-pointed-equiv e)

  coherence-point-is-section-map-inv-pointed-equiv :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-pointed-equiv e ∘∗ pointed-map-inv-pointed-equiv e)
      ( id-pointed-map)
      ( is-section-map-inv-pointed-equiv e)
  coherence-point-is-section-map-inv-pointed-equiv =
    coherence-point-is-section-map-inv-is-pointed-equiv
      ( pointed-map-pointed-equiv e)
      ( is-pointed-equiv-pointed-equiv e)
```

### Right invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-right-inverse-element-Monoid : type-Monoid M → UU l
  is-right-inverse-element-Monoid y = mul-Monoid M x y ＝ unit-Monoid M

  is-right-invertible-element-Monoid : UU l
  is-right-invertible-element-Monoid =
    Σ (type-Monoid M) is-right-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  section-is-right-invertible-element-Monoid :
    is-right-invertible-element-Monoid M x → type-Monoid M
  section-is-right-invertible-element-Monoid = pr1

  is-right-inverse-section-is-right-invertible-element-Monoid :
    (H : is-right-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x
      ( section-is-right-invertible-element-Monoid H)
  is-right-inverse-section-is-right-invertible-element-Monoid = pr2
```

### Left invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-left-inverse-element-Monoid : type-Monoid M → UU l
  is-left-inverse-element-Monoid y = mul-Monoid M y x ＝ unit-Monoid M

  is-left-invertible-element-Monoid : UU l
  is-left-invertible-element-Monoid =
    Σ (type-Monoid M) is-left-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  retraction-is-left-invertible-element-Monoid :
    is-left-invertible-element-Monoid M x → type-Monoid M
  retraction-is-left-invertible-element-Monoid = pr1

  is-left-inverse-retraction-is-left-invertible-element-Monoid :
    (H : is-left-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x
      ( retraction-is-left-invertible-element-Monoid H)
  is-left-inverse-retraction-is-left-invertible-element-Monoid = pr2
```

### Invertible elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-inverse-element-Monoid : type-Monoid M → UU l
  is-inverse-element-Monoid y =
    is-right-inverse-element-Monoid M x y ×
    is-left-inverse-element-Monoid M x y

  is-invertible-element-Monoid : UU l
  is-invertible-element-Monoid =
    Σ (type-Monoid M) is-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M
  inv-is-invertible-element-Monoid = pr1

  is-right-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-right-inverse-inv-is-invertible-element-Monoid H = pr1 (pr2 H)

  is-left-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-left-inverse-inv-is-invertible-element-Monoid H = pr2 (pr2 H)
```

### Invertible elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  is-invertible-element-Group :
    (x : type-Group G) → is-invertible-element-Monoid (monoid-Group G) x
  pr1 (is-invertible-element-Group x) = inv-Group G x
  pr1 (pr2 (is-invertible-element-Group x)) = right-inverse-law-mul-Group G x
  pr2 (pr2 (is-invertible-element-Group x)) = left-inverse-law-mul-Group G x
```

### An element x is invertible if and only if z ↦ xz is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid H =
    map-inv-is-equiv H (unit-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H =
    is-section-map-inv-is-equiv H (unit-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H =
    is-injective-is-equiv H
      ( ( inv (associative-mul-Monoid M _ _ _)) ∙
        ( ap
          ( mul-Monoid' M x)
          ( is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H)) ∙
        ( left-unit-law-mul-Monoid M x) ∙
        ( inv (right-unit-law-mul-Monoid M x)))

  is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → is-invertible-element-Monoid M x
  pr1 (is-invertible-element-is-equiv-mul-Monoid H) =
    inv-is-invertible-element-is-equiv-mul-Monoid H
  pr1 (pr2 (is-invertible-element-is-equiv-mul-Monoid H)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H
  pr2 (pr2 (is-invertible-element-is-equiv-mul-Monoid H)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H

  left-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  left-div-is-invertible-element-Monoid H =
    mul-Monoid M (inv-is-invertible-element-Monoid M H)

  is-section-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid M x ∘ left-div-is-invertible-element-Monoid H ~ id
  is-section-left-div-is-invertible-element-Monoid H y =
    ( inv (associative-mul-Monoid M _ _ _)) ∙
    ( ap
      ( mul-Monoid' M y)
      ( is-right-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( left-unit-law-mul-Monoid M y)

  is-retraction-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    left-div-is-invertible-element-Monoid H ∘ mul-Monoid M x ~ id
  is-retraction-left-div-is-invertible-element-Monoid H y =
    ( inv (associative-mul-Monoid M _ _ _)) ∙
    ( ap
      ( mul-Monoid' M y)
      ( is-left-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( left-unit-law-mul-Monoid M y)

  is-equiv-mul-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid M x)
  is-equiv-mul-is-invertible-element-Monoid H =
    is-equiv-is-invertible
      ( left-div-is-invertible-element-Monoid H)
      ( is-section-left-div-is-invertible-element-Monoid H)
      ( is-retraction-left-div-is-invertible-element-Monoid H)

  is-equiv-mul-iff-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x ↔ is-equiv (mul-Monoid M x)
  is-equiv-mul-iff-is-invertible-element-Monoid =
    ( is-equiv-mul-is-invertible-element-Monoid ,
      is-invertible-element-is-equiv-mul-Monoid)
```

### An element x is invertible if and only if z ↦ zx is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid' H =
    map-inv-is-equiv H (unit-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid' H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H =
    is-section-map-inv-is-equiv H (unit-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid' H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H =
    is-injective-is-equiv H
      ( ( associative-mul-Monoid M _ _ _) ∙
        ( ap
          ( mul-Monoid M x)
          ( is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H)) ∙
        ( right-unit-law-mul-Monoid M x) ∙
        ( inv (left-unit-law-mul-Monoid M x)))

  is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → is-invertible-element-Monoid M x
  pr1 (is-invertible-element-is-equiv-mul-Monoid' H) =
    inv-is-invertible-element-is-equiv-mul-Monoid' H
  pr1 (pr2 (is-invertible-element-is-equiv-mul-Monoid' H)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H
  pr2 (pr2 (is-invertible-element-is-equiv-mul-Monoid' H)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H

  right-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  right-div-is-invertible-element-Monoid H =
    mul-Monoid' M (inv-is-invertible-element-Monoid M H)

  is-section-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid' M x ∘ right-div-is-invertible-element-Monoid H ~ id
  is-section-right-div-is-invertible-element-Monoid H y =
    ( associative-mul-Monoid M _ _ _) ∙
    ( ap
      ( mul-Monoid M y)
      ( is-left-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( right-unit-law-mul-Monoid M y)

  is-retraction-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    right-div-is-invertible-element-Monoid H ∘ mul-Monoid' M x ~ id
  is-retraction-right-div-is-invertible-element-Monoid H y =
    ( associative-mul-Monoid M _ _ _) ∙
    ( ap
      ( mul-Monoid M y)
      ( is-right-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( right-unit-law-mul-Monoid M y)

  is-equiv-mul-is-invertible-element-Monoid' :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid' M x)
  is-equiv-mul-is-invertible-element-Monoid' H =
    is-equiv-is-invertible
      ( right-div-is-invertible-element-Monoid H)
      ( is-section-right-div-is-invertible-element-Monoid H)
      ( is-retraction-right-div-is-invertible-element-Monoid H)

  is-equiv-mul-iff-is-invertible-element-Monoid' :
    is-invertible-element-Monoid M x ↔ is-equiv (mul-Monoid' M x)
  is-equiv-mul-iff-is-invertible-element-Monoid' =
    ( is-equiv-mul-is-invertible-element-Monoid' ,
      is-invertible-element-is-equiv-mul-Monoid')
```

### Multiplication by x from the left is an equivalence

```agda
module _
  {l : Level} (G : Group l)
  where

  left-div-Group : type-Group G → type-Group G → type-Group G
  left-div-Group x =
    left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  ap-left-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    left-div-Group x y ＝ left-div-Group x' y'
  ap-left-div-Group p q = ap-binary left-div-Group p q

  is-section-left-div-Group :
    (x : type-Group G) → (mul-Group G x ∘ left-div-Group x) ~ id
  is-section-left-div-Group x =
    is-section-left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-retraction-left-div-Group :
    (x : type-Group G) → (left-div-Group x ∘ mul-Group G x) ~ id
  is-retraction-left-div-Group x =
    is-retraction-left-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-equiv-mul-Group : (x : type-Group G) → is-equiv (mul-Group G x)
  is-equiv-mul-Group x =
    is-equiv-mul-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  equiv-mul-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group x) = mul-Group G x
  pr2 (equiv-mul-Group x) = is-equiv-mul-Group x

  is-equiv-left-div-Group : (x : type-Group G) → is-equiv (left-div-Group x)
  is-equiv-left-div-Group x =
    is-equiv-is-invertible
      ( mul-Group G x)
      ( is-retraction-left-div-Group x)
      ( is-section-left-div-Group x)

  equiv-left-div-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-left-div-Group x) = left-div-Group x
  pr2 (equiv-left-div-Group x) = is-equiv-left-div-Group x
```

### Multiplication by x from the right is an equivalence

```agda
module _
  {l : Level} (G : Group l)
  where

  right-div-Group : type-Group G → type-Group G → type-Group G
  right-div-Group x y =
    right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G y)
      ( x)

  ap-right-div-Group :
    {x x' y y' : type-Group G} → x ＝ x' → y ＝ y' →
    right-div-Group x y ＝ right-div-Group x' y'
  ap-right-div-Group p q = ap-binary right-div-Group p q

  is-section-right-div-Group :
    (x : type-Group G) → (mul-Group' G x ∘ (λ y → right-div-Group y x)) ~ id
  is-section-right-div-Group x =
    is-section-right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-retraction-right-div-Group :
    (x : type-Group G) → ((λ y → right-div-Group y x) ∘ mul-Group' G x) ~ id
  is-retraction-right-div-Group x =
    is-retraction-right-div-is-invertible-element-Monoid
      ( monoid-Group G)
      ( is-invertible-element-Group G x)

  is-equiv-mul-Group' : (x : type-Group G) → is-equiv (mul-Group' G x)
  is-equiv-mul-Group' x =
    is-equiv-is-invertible
      ( λ y → right-div-Group y x)
      ( is-section-right-div-Group x)
      ( is-retraction-right-div-Group x)

  equiv-mul-Group' : (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-mul-Group' x) = mul-Group' G x
  pr2 (equiv-mul-Group' x) = is-equiv-mul-Group' x

  is-equiv-right-div-Group :
    (x : type-Group G) → is-equiv (λ y → right-div-Group y x)
  is-equiv-right-div-Group x =
    is-equiv-is-invertible
      ( mul-Group' G x)
      ( is-retraction-right-div-Group x)
      ( is-section-right-div-Group x)

  equiv-right-div-Group :
    (x : type-Group G) → type-Group G ≃ type-Group G
  pr1 (equiv-right-div-Group x) y = right-div-Group y x
  pr2 (equiv-right-div-Group x) = is-equiv-right-div-Group x
```

### Binary equivalences and embeddings

```agda
fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  A → B → C
fix-left f a = f a

fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  B → A → C
fix-right f b a = f a b

is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-equiv {A = A} {B = B} f =
  ((b : B) → is-equiv (fix-right f b)) × ((a : A) → is-equiv (fix-left f a))

is-equiv-fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-equiv (fix-left f a)
is-equiv-fix-left f H {a} = pr2 H a

is-equiv-fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-equiv (fix-right f b)
is-equiv-fix-right f H {b} = pr1 H b

is-binary-emb :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-emb {A = A} {B = B} f =
  {x x' : A} {y y' : B} →
    is-binary-equiv (λ (p : x ＝ x') (q : y ＝ y') → ap-binary f p q)
```

### Any binary equivalence is a binary embedding

```agda
is-emb-fix-left-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-emb (fix-left f a)
is-emb-fix-left-is-binary-equiv f H {a} =
  is-emb-is-equiv (is-equiv-fix-left f H)

is-emb-fix-right-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-emb (fix-right f b)
is-emb-fix-right-is-binary-equiv f H {b} =
  is-emb-is-equiv (is-equiv-fix-right f H)

is-binary-emb-is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B → C} →
  is-binary-equiv f → is-binary-emb f
is-binary-emb-is-binary-equiv {f = f} H {x} {x'} {y} {y'} =
  pair
    ( λ q →
      is-equiv-left-map-triangle
        ( λ p → ap-binary f p q)
        ( concat' (f x y) (ap (fix-left f x') q))
        ( λ p → ap (fix-right f y) p)
        ( λ p → triangle-ap-binary f p q)
        ( is-emb-fix-right-is-binary-equiv f H x x')
        ( is-equiv-concat' (f x y) (ap (fix-left f x') q)))
    ( λ p →
      is-equiv-left-map-triangle
        ( λ q → ap-binary f p q)
        ( concat (ap (fix-right f y) p) (f x' y'))
        ( λ q → ap (fix-left f x') q)
        ( λ q → triangle-ap-binary f p q)
        ( is-emb-fix-left-is-binary-equiv f H y y')
        ( is-equiv-concat (ap (fix-right f y) p) (f x' y')))
```

### Multiplication is a binary equivalence and a binary embedding

```agda
module _
  {l : Level} (G : Group l)
  where

  is-binary-equiv-mul-Group : is-binary-equiv (mul-Group G)
  pr1 is-binary-equiv-mul-Group = is-equiv-mul-Group' G
  pr2 is-binary-equiv-mul-Group = is-equiv-mul-Group G

  is-binary-emb-mul-Group : is-binary-emb (mul-Group G)
  is-binary-emb-mul-Group =
    is-binary-emb-is-binary-equiv is-binary-equiv-mul-Group

  is-emb-mul-Group : (x : type-Group G) → is-emb (mul-Group G x)
  is-emb-mul-Group x = is-emb-is-equiv (is-equiv-mul-Group G x)

  is-emb-mul-Group' : (x : type-Group G) → is-emb (mul-Group' G x)
  is-emb-mul-Group' x = is-emb-is-equiv (is-equiv-mul-Group' G x)

  is-injective-mul-Group : (x : type-Group G) → is-injective (mul-Group G x)
  is-injective-mul-Group x = is-injective-is-equiv (is-equiv-mul-Group G x)

  is-injective-mul-Group' : (x : type-Group G) → is-injective (mul-Group' G x)
  is-injective-mul-Group' x = is-injective-is-equiv (is-equiv-mul-Group' G x)
```

### Any idempotent element in a group is the unit

```agda
module _
  {l : Level} (G : Group l)
  where

  is-idempotent-Group : type-Group G → UU l
  is-idempotent-Group x = mul-Group G x x ＝ x

  is-unit-is-idempotent-Group :
    {x : type-Group G} → is-idempotent-Group x → is-unit-Group G x
  is-unit-is-idempotent-Group {x} p =
    is-injective-mul-Group G x (p ∙ inv (right-unit-law-mul-Group G x))
```

### Group homomorphisms preserve the unit element

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-unit-Group : (type-Group G → type-Group H) → UU l2
  preserves-unit-Group f = f (unit-Group G) ＝ unit-Group H

  abstract
    preserves-unit-hom-Group :
      ( f : hom-Group G H) → preserves-unit-Group (map-hom-Group G H f)
    preserves-unit-hom-Group f =
      is-unit-is-idempotent-Group H
        ( equational-reasoning
          mul-Group H
            ( map-hom-Group G H f (unit-Group G))
            ( map-hom-Group G H f (unit-Group G))
          ＝ map-hom-Group G H f (mul-Group G (unit-Group G) (unit-Group G))
            by inv (preserves-mul-hom-Group G H f)
          ＝ map-hom-Group G H f (unit-Group G)
            by ap (map-hom-Group G H f) (left-unit-law-mul-Group G _))
```
