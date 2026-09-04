# Section 10.3 Contractible maps

```agda
module section-10-3-contractible-maps where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import exercise-5-2-inverse-concatenation-maps
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-1-contractible-types
```

<!-- rosetta-item: section-10.3 -->

## Definition 10.3.1

<!-- rosetta-item: definition-10.3.1 -->

Let `f:A→ B` be a function, and let `b:B`.
The **fiber** of `f` at `b` is defined to be the type
```text
fib(f, b)≔Σ(a:A) f(a)=b.
```

<!-- rosetta-agda-block: definition-10.3.1-fibers -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (b : B)
  where

  fiber : Type (l1 ⊔ l2)
  fiber = Σ A (λ x → f x ＝ b)

  fiber' : Type (l1 ⊔ l2)
  fiber' = Σ A (λ x → b ＝ f x)

module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {b : B}
  where

  inclusion-fiber : fiber f b → A
  inclusion-fiber = pr1

  compute-value-inclusion-fiber : (y : fiber f b) → f (inclusion-fiber y) ＝ b
  compute-value-inclusion-fiber = pr2

  inclusion-fiber' : fiber' f b → A
  inclusion-fiber' = pr1

  compute-value-inclusion-fiber' :
    (y : fiber' f b) → b ＝ f (inclusion-fiber' y)
  compute-value-inclusion-fiber' = pr2
```
<!-- rosetta-item-end: definition-10.3.1 -->

In other words, the fiber of `f` at `b` is the type of `a:A` that get mapped by `f` to `b`.
One may think of the fiber as a type theoretic version of the preimage of a point.

It will be useful to have a characterization of the identity type of a fiber.
In order to identify any `(x,p)` and `(x',p')` in `fib(f, y)`, we may first construct an identification `α:x=x'`.
Then we obtain a triangle
<!-- rosetta-diagram: 64b5b852d28b; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[f(x)]               [f(x')]

            [y]

Arrows:
- f(x) --p--> y
- f(x) --{ap_{f}(α)}--> f(x')
- f(x') --{p'}--> y
```
so we may consider the type of identifications `β:p=ap_{f}(α) ∙ p'`.
We will show that the type of all identifications `(x,p)=(x',p')` is equivalent to the type of such pairs `(α,β)`.

## Definition 10.3.2

<!-- rosetta-item: definition-10.3.2 -->

Let `f:A → B` be a map, and let `(x,p),(x',p'):fib(f, y)` for some `y:B`.
Then we define
```text
Eq-fib_f((x,p),(x',p'))≔ Σ(α:x=x') p=ap_{f}(α) ∙ p'
```
The relation `Eq-fib_f:fib(f, y)→fib(f, y)→𝒰` is a reflexive relation, since we have
```text
λ (x,p). (refl,refl):Π((x,p):fib(f, y)) Eq-fib_f((x,p),(x,p)).
```

<!-- rosetta-agda-block: definition-10.3.2-equality-fibers -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (b : B)
  where

  Eq-fiber : fiber f b → fiber f b → Type (l1 ⊔ l2)
  Eq-fiber s t = Σ (pr1 s ＝ pr1 t) (λ α → ap f α ∙ pr2 t ＝ pr2 s)

  refl-Eq-fiber : (s : fiber f b) → Eq-fiber s s
  pr1 (refl-Eq-fiber s) = refl
  pr2 (refl-Eq-fiber s) = refl

  Eq-eq-fiber : {s t : fiber f b} → s ＝ t → Eq-fiber s t
  Eq-eq-fiber {s} refl = refl-Eq-fiber s

  eq-Eq-fiber-uncurry : {s t : fiber f b} → Eq-fiber s t → s ＝ t
  eq-Eq-fiber-uncurry (refl , refl) = refl

  eq-Eq-fiber :
    {s t : fiber f b} (α : pr1 s ＝ pr1 t) → ap f α ∙ pr2 t ＝ pr2 s → s ＝ t
  eq-Eq-fiber α β = eq-Eq-fiber-uncurry (α , β)
```
<!-- rosetta-item-end: definition-10.3.2 -->

## Proposition 10.3.3

<!-- rosetta-item: proposition-10.3.3 -->

Consider a map `f:A→ B` and let `y:B`.
The canonical map
```text
((x,p)=(x',p'))→Eq-fib_f((x,p),(x',p'))
```
induced by the reflexivity of `Eq-fib_f` is an equivalence for any `(x,p),(x',p'):fib(f, y)`.

### Proof

<!-- rosetta-item: subheading-10.3-proof -->

*Proof.* The converse map
```text
Eq-fib_f((x,p),(x',p'))→ ((x,p)=(x',p'))
```
is easily defined by `Σ`-induction, and then path induction twice.
The homotopies witnessing that this converse map is indeed a right inverse as well as a left inverse are similarly constructed by induction. ◻

<!-- rosetta-agda-block: proposition-10.3.3-equality-fiber-equivalence -->

```agda
  is-section-eq-Eq-fiber :
    {s t : fiber f b} →
    is-section (Eq-eq-fiber {s} {t}) (eq-Eq-fiber-uncurry {s} {t})
  is-section-eq-Eq-fiber (refl , refl) = refl

  is-retraction-eq-Eq-fiber :
    {s t : fiber f b} →
    is-retraction (Eq-eq-fiber {s} {t}) (eq-Eq-fiber-uncurry {s} {t})
  is-retraction-eq-Eq-fiber refl = refl

  abstract
    is-equiv-Eq-eq-fiber : {s t : fiber f b} → is-equiv (Eq-eq-fiber {s} {t})
    is-equiv-Eq-eq-fiber =
      is-equiv-is-invertible
        eq-Eq-fiber-uncurry
        is-section-eq-Eq-fiber
        is-retraction-eq-Eq-fiber

  equiv-Eq-eq-fiber : {s t : fiber f b} → (s ＝ t) ≃ Eq-fiber s t
  pr1 equiv-Eq-eq-fiber = Eq-eq-fiber
  pr2 equiv-Eq-eq-fiber = is-equiv-Eq-eq-fiber
```
<!-- rosetta-item-end: proposition-10.3.3 -->

Now we define at the notion of contractible map.

## Definition 10.3.4

<!-- rosetta-item: definition-10.3.4 -->

We say that a function `f:A→ B` is **contractible** if it comes equipped with an element of type
```text
is-contr(f)≔Π(b:B) is-contr(fib(f, b)).
```

<!-- rosetta-agda-block: definition-10.3.4-contractible-maps -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2}
  where

  is-contr-map : (A → B) → Type (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fiber f y)
```
<!-- rosetta-item-end: definition-10.3.4 -->

## Theorem 10.3.5

<!-- rosetta-item: theorem-10.3.5; latex-label: thm:equiv_contr -->

Any contractible map is an equivalence.

### Proof

<!-- rosetta-item: subheading-10.3-proof-2 -->

*Proof.* Let `f:A→ B` be a contractible map.
Using the center of contraction of each `fib(f, y)`, we obtain the dependent function
```text
λ y. (g(y),G(y)):Π(y:B) fib(f, y).
```
Thus, we get map `g:B→ A`, and a homotopy `G:Π(y:B) f(g(y))=y`.
In other words, we get a section of `f`.

It remains to construct a retraction of `f`.
Taking `g` as our retraction, we have to show that `Π(x:A) g(f(x))=x`.
Note that we get an identification `p:f(g(f(x)))=f(x)` since `g` is a section of `f`.
Therefore, it follows that `(g(f(x)),p):fib(f, f(x))`.
Moreover, since `fib(f, f(x))` is contractible we get an identification `q:(g(f(x)),p)=(x,refl)`.
The base path `ap_{pr 1}(q)` of this identification is an identification of type `g(f(x))=x`, as desired. ◻

<!-- rosetta-agda-block: theorem-10.3.5-contractible-map-is-equivalence -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (H : is-contr-map f)
  where

  map-inv-is-contr-map : B → A
  map-inv-is-contr-map y = pr1 (center (H y))

  is-section-map-inv-is-contr-map :
    is-section f map-inv-is-contr-map
  is-section-map-inv-is-contr-map y = pr2 (center (H y))

  is-retraction-map-inv-is-contr-map :
    is-retraction f map-inv-is-contr-map
  is-retraction-map-inv-is-contr-map x =
    ap
      ( pr1 {B = λ z → (f z ＝ f x)})
      ( ( inv
          ( contraction
            ( H (f x))
            ( ( map-inv-is-contr-map (f x)) ,
              ( is-section-map-inv-is-contr-map (f x))))) ∙
        ( contraction (H (f x)) (x , refl)))

  section-is-contr-map : section f
  section-is-contr-map =
    ( map-inv-is-contr-map , is-section-map-inv-is-contr-map)

  retraction-is-contr-map : retraction f
  retraction-is-contr-map =
    ( map-inv-is-contr-map , is-retraction-map-inv-is-contr-map)

  abstract
    is-equiv-is-contr-map : is-equiv f
    is-equiv-is-contr-map =
      is-equiv-is-invertible
        ( map-inv-is-contr-map)
        ( is-section-map-inv-is-contr-map)
        ( is-retraction-map-inv-is-contr-map)
```
<!-- rosetta-item-end: theorem-10.3.5 -->
