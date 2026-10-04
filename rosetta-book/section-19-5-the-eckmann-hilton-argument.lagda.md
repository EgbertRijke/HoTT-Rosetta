# Section 19.5 The Eckmann-Hilton argument

```agda
module section-19-5-the-eckmann-hilton-argument where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-1-distributive-inv-concat
open import exercise-5-2-inverse-concatenation-maps
open import section-10-4-equivalences-are-contractible-maps
open import section-19-4-homotopy-groups-of-types
```

The Eckmann-Hilton argument is used to show that `π_n(A)` is an abelian group for all `n ≥ 2`.
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

```agda
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
```

This results in the **horizontal concatenation** operation

```text
_ ∙_h _ : (p = p') → ((q = q') → (p ∙ q = p' ∙ q')).
```

In other words, for any two identifications `r : p = p'` and `s : q = q'` as in the diagram

```text
[x] ----p----> [y] ----q----> [z]
        ⇓ r            ⇓ s
[x] ----p'---> [y] ----q'---> [z]
```

The repeated endpoint labels in these diagrams denote the same points.
We obtain `r ∙_h s ≔ ap-binary_{_ ∙ _}(r,s) : p ∙ q = p' ∙ q'`.

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
refl_refl ∙_h s = s
r ∙_h refl_refl = r.
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
(r ∙ r') ∙_h (s ∙ s') = (r ∙_h s) ∙ (r' ∙_h s').
```

### Proof

_Proof._ We use path induction on both `r` and `s`.
Then it suffices to show that

```text
(refl ∙ r') ∙_h (refl ∙ s') = (refl ∙_h refl) ∙ (r' ∙_h s')
```

Using the unit laws for ordinary concatenation, we see that both sides reduce to `r' ∙_h s'`. ◻

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

_Proof._ First we observe that `r ∙ s = r ∙_h s` by the following calculation using the unit laws from Lemma 19.5.4 and the interchange law from Lemma 19.5.5:

```text
r ∙ s = (r ∙_h refl_refl) ∙ (refl_refl ∙_h s)
= (r ∙ refl_refl) ∙_h (refl_refl ∙ s)
= r ∙_h s
```

Similarly, we observe that `r ∙_h s = s ∙ r` by the following calculation:

```text
r ∙_h s = (refl_refl ∙ r) ∙_h (s ∙ refl_refl)
= (refl_refl ∙_h s) ∙ (r ∙_h refl_refl)
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

_Proof._ By Proposition 19.4.6 it follows that `π_n(A)` is isomorphic to the second homotopy group of some pointed type, for every `n ≥ 2`.
Therefore it suffices to prove the claim for `π_2(A)` for every pointed type `A`.

Our goal is to show that

```text
Π(r,s : π_2(A)) rs = sr.
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
