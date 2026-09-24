# Section 16.2 Double counting in type theory

```agda
module section-16-2-double-counting-in-type-theory where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-4-coproducts
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-6-4-peanos-seventh-and-eighth-axioms
open import section-7-3-the-standard-finite-types
open import section-7-4-the-natural-numbers-modulo-k-plus-one
open import section-8-1-decidability-and-decidable-equality
open import exercise-8-7-decidable-equality-coproducts
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-4-three-for-two-equivalences
open import section-10-4-equivalences-are-contractible-maps
open import section-11-4-embeddings
open import section-11-5-disjointness-of-coproducts
open import section-12-1-propositions
open import exercise-12-8-retracts-of-truncated-types
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-16-1-counting-in-type-theory
```

In combinatorics, counting arguments often proceed by showing that two finite sets are isomorphic—or, in the language of type theory, by showing that two finite types are equivalent.
The idea here is, of course, that when we count the elements of a type twice correctly, then both countings must result in the same number.
However, this is something that we must prove before we can use it.
In other words, we must show that

```text
  (Fin_{k} ≃ Fin_{l}) → (k = l)
```
for any two natural numbers `k` and `l`.
We will prove this claim as a consequence of the following general fact.

## Proposition 16.2.1

For any two types `X` and `Y`, there is a map

```text
  (X + unit ≃ Y + unit) → (X ≃ Y).
```

### Proof

We prove the claim in four steps.
We will write `i` for `inl : X → X + unit` and also for `inl : Y → Y + unit`, and we will write `⋆` for `inr(⋆) : X + unit` and also for `inr(⋆) : Y + unit`.

1. We first show that for any equivalence `e : X + unit ≃ Y + unit` and any `x : X` equipped with an identification `p : e(i(x)) = ⋆`, that there is an element

   ```text
     star-value(e,x,p) : Y
   ```
    
   equipped with an identification

   ```text
     α : i(star-value(e,x,p)) = e(⋆).
   ```

   To see this, note that the map `e` is injective.
   The elements `i(x)` and `⋆` are distinct, so it follows that the elements `e(i(x))` and `e(⋆)` are distinct.
   In particular, we have `e(⋆) ≠ ⋆`.
   Therefore it follows that there is an element `y : Y` equipped with an identification `i(y) = e(⋆)`.

2. Next, we construct for every equivalence `e : X + unit ≃ Y + unit` a map `f : X → Y` equipped with identifications

   ```text
     β : Π(y : Y) (e(i(x)) = i(y)) → (f(x) = y)
     γ : Π(p : e(i(x)) = ⋆) f(x) = star-value(e,x,p).
   ```

   In order to construct the map `f : X → Y`, we first construct a dependent function

   ```text
     f' : Π(x : X) Π(u : Y + unit) ((e(i(x)) = u) → Y).
   ```

   This function is defined by pattern matching on `u`, by

   ```text
     f'(x,i(y),p) ≔ y
        f'(x,⋆,p) ≔ star-value(e,x,p)
   ```

   Then we define `f(x) ≔ f'(x,e(i(x)),refl)`.
   By the definition of `f'` it then follows that we have an identification

   ```text
     f(x) ≐ f'(x,e(i(x)),refl)
          = f'(x,i(y),p)
          ≐ y
   ```
   
   for any `y : Y` and `p : e(i(x)) = i(y)`, and that we have an identification

   ```text
     f(x) ≐ f'(x,e(i(x)),refl)
          = f'(x,⋆,p)
          ≐ star-value(e,x,p)
   ```
    
   for any `p : e(i(x)) = ⋆`.

3. The inverse function `g : Y → X` is constructed in the same way as the
   function `f : X → Y`, using the equivalence `e⁻¹ : Y + unit ≃ X + unit`.
   This function comes equipped with

   ```text
     δ : Π(x : X) (e⁻¹(i(y)) = i(x)) → (g(y) = x)
     ε : Π(p : e⁻¹(i(y)) = ⋆) g(y) = star-value(e⁻¹,y,p).
   ```

4. It remains to show that `f` and `g` are inverse to each other.
   The proof that `g` is a retraction of `f` is similar to the proof that `g`
   is a section of `f`, so we will only prove the latter.
   In other words, we will construct an identification

   ```text
     f(g(y)) = y
   ```

   for any `y : Y`. The proof is by case analysis on `(e⁻¹(i(y)) = ⋆) + (e⁻¹(i(y)) ≠ ⋆)`. In the case where `p : e⁻¹(i(y)) = ⋆`, we have the identification

   ```text
     ε(p) : g(y) = star-value(e⁻¹,y,p).
   ```

   Furthermore, we have the identification

   ```text
     γ(q) : f(g(y)) = star-value(e,g(y),q),
   ```
   
   where `q : e(i(g(y))) = ⋆` is the composite of the identifications

   ```text
     e(i(g(y))) = e(i(star-value(e⁻¹,y,p)))
                = e(e^{-1}(⋆))
                =⋆.
   ```

   Using the identification `γ(q)`, we obtain

   ```text
     i(f(g(y))) = i(star-value(e,g(y),q))
                = e(⋆)
                = e(e⁻¹(i(y)))
                = i(y).
   ```

   Since `i : Y → Y + unit` is injective, it follows that `f(g(y)) = y`. ◻

```agda
Maybe : {l : Level} → UU l → UU l
Maybe X = X + unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe = inr star

extend-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Maybe Y) → Maybe X → Maybe Y
extend-Maybe f (inl x) = f x
extend-Maybe f (inr star) = inr star

map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → Maybe X → Maybe Y
map-Maybe f (inl x) = inl (f x)
map-Maybe f (inr star) = inr star

is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = (x ＝ exception-Maybe)

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

abstract
  is-prop-is-exception-Maybe :
    {l : Level} {X : UU l} (x : Maybe X) → is-prop (is-exception-Maybe x)
  is-prop-is-exception-Maybe (inl x) ()
  is-prop-is-exception-Maybe (inr star) refl refl = refl , (λ where refl → refl)

is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → inl y ＝ x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  inl (value-is-value-Maybe x H) ＝ x
eq-is-value-Maybe x H = pr2 H

abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe x ()

decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x + is-exception-Maybe x
decide-Maybe (inl x) = inl (x , refl)
decide-Maybe (inr star) = inr refl

abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe {l1} {X} .(inl x) (x , refl) =
    is-not-exception-unit-Maybe x

abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe = is-emb-inl

emb-unit-Maybe : {l : Level} (X : UU l) → X ↪ Maybe X
pr1 (emb-unit-Maybe X) = unit-Maybe
pr2 (emb-unit-Maybe X) = is-emb-unit-Maybe

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = is-injective-inl

module _
  {l : Level}
  {X : UU l}
  where

  is-right-is-exception-Maybe :
    (x : Maybe X) → is-exception-Maybe x → is-right x
  is-right-is-exception-Maybe _ refl = star

  is-exception-is-right-Maybe :
    (x : Maybe X) → is-right x → is-exception-Maybe x
  is-exception-is-right-Maybe (inr star) star = refl

  is-right-iff-is-exception-Maybe :
    (x : Maybe X) → is-exception-Maybe x ↔ is-right x
  is-right-iff-is-exception-Maybe x =
    ( is-right-is-exception-Maybe x , is-exception-is-right-Maybe x)

module _
  {l : Level}
  {X : UU l}
  where

  is-left-is-value-Maybe :
    (x : Maybe X) → is-value-Maybe x → is-left x
  is-left-is-value-Maybe (inl x) (.x , refl) = star

  is-value-is-left-Maybe :
    (x : Maybe X) → is-left x → is-value-Maybe x
  is-value-is-left-Maybe (inl x) star = (x , refl)

  is-left-iff-is-value-Maybe :
    (x : Maybe X) → is-value-Maybe x ↔ is-left x
  is-left-iff-is-value-Maybe x =
    ( is-left-is-value-Maybe x , is-value-is-left-Maybe x)

module _
  {l : Level} {X : UU l}
  where

  is-decidable-is-exception-Maybe :
    (x : Maybe X) → is-decidable (is-exception-Maybe x)
  is-decidable-is-exception-Maybe (inl x) =
    inr (λ p → ex-falso (is-empty-eq-coproduct-inl-inr x star p))
  is-decidable-is-exception-Maybe (inr star) = inl refl

  is-decidable-is-not-exception-Maybe :
    (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
  is-decidable-is-not-exception-Maybe x =
    is-decidable-neg (is-decidable-is-exception-Maybe x)

is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coproduct-is-empty
    ( is-value-Maybe x)
    ( is-exception-Maybe x)
    ( H)
    ( decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  inl (value-is-not-exception-Maybe x H) ＝ x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

abstract
  is-not-exception-injective-map-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
    is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
    is-not-exception-Maybe (f exception-Maybe)
  is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
    is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

abstract
  is-not-exception-map-equiv-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
    is-exception-Maybe (map-equiv e (inl x)) →
    is-not-exception-Maybe (map-equiv e exception-Maybe)
  is-not-exception-map-equiv-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-equiv e)

abstract
  is-not-exception-emb-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
    (x : X) → is-exception-Maybe (map-emb e (inl x)) →
    is-not-exception-Maybe (map-emb e exception-Maybe)
  is-not-exception-emb-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  inl (value-injective-map-exception-Maybe is-inj-f x H) ＝
  f exception-Maybe
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

compute-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe'
  {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
compute-restrict-injective-map-is-exception-Maybe'
  {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

compute-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  compute-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

compute-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe'
  is-inj-f x (inl y) p H =
  inv p
compute-restrict-injective-map-is-not-exception-Maybe'
  is-inj-f x (inr star) p H =
  ex-falso (H p)

compute-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  compute-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-equiv e)

compute-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe' e =
  compute-restrict-injective-map-is-exception-Maybe' (is-injective-equiv e)

compute-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe e x =
  compute-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

compute-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
compute-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

compute-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe e x =
  compute-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

compute-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e exception-Maybe
compute-map-inv-equiv-equiv-is-exception-Maybe e =
  compute-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

compute-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e (inl y)
compute-map-inv-equiv-equiv-is-not-exception-Maybe e =
  compute-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)

abstract
  is-section-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
  is-section-map-inv-equiv-equiv-Maybe e y with
    is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( compute-map-equiv-equiv-is-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( ( ap
              ( map-equiv e)
              ( compute-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
            ( is-section-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-equiv e) (inv p)) ∙
          ( is-section-map-inv-equiv e (inl y))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( compute-map-equiv-equiv-is-not-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( is-not-exception-is-value-Maybe
            ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
            ( pair y
              ( inv
                ( ( ap
                    ( map-equiv e)
                    ( compute-map-inv-equiv-equiv-is-not-exception-Maybe
                        e y f)) ∙
                  ( is-section-map-inv-equiv e (inl y))))))) ∙
        ( ( ap
            ( map-equiv e)
            ( compute-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
          ( is-section-map-inv-equiv e (inl y))))

abstract
  is-retraction-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
  is-retraction-map-inv-equiv-equiv-Maybe e x with
    is-decidable-is-exception-Maybe (map-equiv e (inl x))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( compute-map-inv-equiv-equiv-is-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( ( ap
              ( map-inv-equiv e)
              ( compute-map-equiv-equiv-is-exception-Maybe e x p)) ∙
            ( is-retraction-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-inv-equiv e) (inv p)) ∙
          ( is-retraction-map-inv-equiv e (inl x))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( compute-map-inv-equiv-equiv-is-not-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( is-not-exception-is-value-Maybe
            ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
            ( pair x
              ( inv
                ( ( ap
                    ( map-inv-equiv e)
                    ( compute-map-equiv-equiv-is-not-exception-Maybe
                        e x f)) ∙
                  ( is-retraction-map-inv-equiv e (inl x))))))) ∙
        ( ( ap
            ( map-inv-equiv e)
            ( compute-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
          ( is-retraction-map-inv-equiv e (inl x))))

abstract
  is-equiv-map-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    is-equiv (map-equiv-equiv-Maybe e)
  is-equiv-map-equiv-equiv-Maybe e =
    is-equiv-is-invertible
      ( map-inv-equiv-equiv-Maybe e)
      ( is-section-map-inv-equiv-equiv-Maybe e)
      ( is-retraction-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
pr1 (equiv-equiv-Maybe e) = map-equiv-equiv-Maybe e
pr2 (equiv-equiv-Maybe e) = is-equiv-map-equiv-equiv-Maybe e

compute-equiv-equiv-Maybe-id-equiv :
  {l1 : Level} {X : UU l1} →
  equiv-equiv-Maybe id-equiv ＝ id-equiv {A = X}
compute-equiv-equiv-Maybe-id-equiv = eq-htpy-equiv refl-htpy
```

## Theorem 16.2.2

For any two natural numbers `k` and `l`, there is a map

```text
  (Fin_{k} ≃ Fin_{l}) → (k = l).
```

### Proof

The proof is by induction on `k` and `l`.
In the base case, where both `k` and `l` are zero, the claim is obvious.
If `k` is zero and `l` is a successor, then we have `0 : Fin_{l}`.
Any equivalence `e : Fin_{k} ≃ Fin_{l}` now gives us the element

```text
  e⁻¹(0) : empty,
```

which is of course absurd.
Similarly, if `k` is a successor and `l` is zero, we obtain `e(0) : empty`, which is again absurd.
If both `k` and `l` are a successor, then we have by Proposition 16.2.1 the composite

```text
  (Fin_{k+1} ≃ Fin_{l+1}) ---> (Fin_{k} ≃ Fin_{l}) ---> (k = l) ---> (k+1 = l+1)
                                                                               ◻
```

```agda
is-equivalence-injective :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-equivalence-injective {A = A} P = {x y : A} → P x ≃ P y → x ＝ y

is-equivalence-injective-Fin : is-equivalence-injective Fin
is-equivalence-injective-Fin {zero-ℕ} {zero-ℕ} e =
  refl
is-equivalence-injective-Fin {zero-ℕ} {succ-ℕ l} e =
  ex-falso (map-inv-equiv e (zero-Fin l))
is-equivalence-injective-Fin {succ-ℕ k} {zero-ℕ} e =
  ex-falso (map-equiv e (zero-Fin k))
is-equivalence-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
  ap succ-ℕ (is-equivalence-injective-Fin (equiv-equiv-Maybe e))

compute-is-equivalence-injective-Fin-id-equiv :
  {n : ℕ} → is-equivalence-injective-Fin {n} {n} id-equiv ＝ refl
compute-is-equivalence-injective-Fin-id-equiv {zero-ℕ} = refl
compute-is-equivalence-injective-Fin-id-equiv {succ-ℕ n} =
  ap² succ-ℕ
    ( ( ap is-equivalence-injective-Fin compute-equiv-equiv-Maybe-id-equiv) ∙
      ( compute-is-equivalence-injective-Fin-id-equiv {n}))

abstract
  double-counting-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) (e : A ≃ B) →
    number-of-elements-count count-A ＝ number-of-elements-count count-B
  double-counting-equiv (k , f) (l , g) e =
    is-equivalence-injective-Fin (inv-equiv g ∘e e ∘e f)

abstract
  double-counting :
    {l : Level} {A : UU l} (count-A count-A' : count A) →
    number-of-elements-count count-A ＝ number-of-elements-count count-A'
  double-counting count-A count-A' =
    double-counting-equiv count-A count-A' id-equiv
```

```text
abstract
  double-counting-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
    number-of-elements-count count-C ＝
    sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x))
  double-counting-Σ count-A count-B count-C =
    ( double-counting count-C (count-Σ count-A count-B)) ∙
    ( number-of-elements-count-Σ count-A count-B)

abstract
  sum-number-of-elements-count-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : count (Σ A B)) →
    sum-count-ℕ e
      ( λ x → number-of-elements-count (count-fiber-count-Σ-count-base e f x)) ＝
    number-of-elements-count f
  sum-number-of-elements-count-fiber-count-Σ e f =
    ( inv
      ( number-of-elements-count-Σ e (count-fiber-count-Σ-count-base e f))) ∙
    ( double-counting (count-Σ e (count-fiber-count-Σ-count-base e f)) f)

abstract
  double-counting-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
    number-of-elements-count (count-B x) ＝
    number-of-elements-count (count-fiber-count-Σ-count-base count-A count-C x)
  double-counting-fiber-count-Σ count-A count-B count-C x =
    double-counting
      ( count-B x)
      ( count-fiber-count-Σ-count-base count-A count-C x)

abstract
  sum-number-of-elements-count-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
    sum-count-ℕ
      ( count-base-count-Σ b count-ΣAB count-B)
      ( λ x → number-of-elements-count (count-B x)) ＝
    number-of-elements-count count-ΣAB
  sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ b count-ΣAB count-B)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-A : count A) (count-B : (x : A) → count (B x))
    (count-ΣAB : count (Σ A B)) →
    number-of-elements-count (count-base-count-Σ b count-ΣAB count-B) ＝
    number-of-elements-count count-A
  double-counting-base-count-Σ b count-A count-B count-ΣAB =
    double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

abstract
  sum-number-of-elements-count-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
    ( count-B : (x : A) → count (B x)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    sum-count-ℕ
      ( count-base-count-Σ' count-ΣAB count-B count-nB)
      ( λ x → number-of-elements-count (count-B x)) ＝
    number-of-elements-count count-ΣAB
  sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    number-of-elements-count
      ( count-base-count-Σ' count-ΣAB count-B count-nB) ＝
    number-of-elements-count count-A
  double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
    double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A
```
