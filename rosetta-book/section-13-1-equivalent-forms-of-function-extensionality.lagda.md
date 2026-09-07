# Section 13.1 Equivalent forms of function extensionality

```agda
module section-13-1-equivalent-forms-of-function-extensionality where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-9-3-characterizing-the-identity-types-of-dependent-pair-types
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-4-general-truncation-levels
open import exercise-10-2-contractible-retracts
```

<!-- rosetta-item: section-13.1 -->

The function extensionality principle characterizes the identity type of an arbitrary dependent function type.
It asserts that the type `f=g` of identifications between two dependent functions is equivalent to the type of homotopies `f~ g`.
By Theorem 11.2.2 there are three equivalent ways of doing this.

## Proposition 13.1.1

<!-- rosetta-item: proposition-13.1.1; latex-label: prp:funext -->

Consider a dependent function `f:Π(x:A) B(x)`.
The following are equivalent:

1.  The **function extensionality principle** holds at `f`: for each `g:Π(x:A) B(x)`, the family of maps
```text
htpy-eq:(f=g)→ (f~ g)
```
    defined by `htpy-eq(refl):=refl-htpy_{f}` is a family of equivalences.

2.  The total space
```text
Σ(g:Π(x:A) B(x)) f~ g
```
    is contractible.

3.  The principle of **homotopy induction**: for any family of types `P(g,H)` indexed by `g:Π(x:A) B(x)` and `H:f~ g`, the evaluation function
```text
(Π(g:Π(x:A) B(x)) Π(H:f~ g) P(g,H))→ P(f,refl-htpy_f),
```
    given by `s↦ s(f,refl-htpy_f)`, has a section.

### Proof

<!-- rosetta-item: subheading-13.1-proof -->

*Proof.* This theorem follows directly from Theorem 11.2.2. ◻

<!-- rosetta-agda-block: proposition-13.1.1-identities-to-homotopies -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  htpy-eq : {f g : (x : A) → B x} → f ＝ g → f ~ g
  htpy-eq p a = ap (λ h → h a) p

  compute-htpy-eq-refl : {f : (x : A) → B x} → htpy-eq refl ＝ refl-htpy' f
  compute-htpy-eq-refl = refl
```

<!-- rosetta-agda-block: proposition-13.1.1-extensionality-instance -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  instance-function-extensionality : (f g : (x : A) → B x) → Type (l1 ⊔ l2)
  instance-function-extensionality f g = is-equiv (htpy-eq {f = f} {g})
```

<!-- rosetta-agda-block: proposition-13.1.1-based-extensionality -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  based-function-extensionality : (f : (x : A) → B x) → Type (l1 ⊔ l2)
  based-function-extensionality f =
    (g : (x : A) → B x) → instance-function-extensionality f g
```

<!-- rosetta-agda-block: proposition-13.1.1-homotopy-evaluation -->

```agda
module _
  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {f : (x : A) → B x}
  where

  ev-refl-htpy :
    (C : (g : (x : A) → B x) → f ~ g → Type l3) →
    ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
  ev-refl-htpy C φ = φ f refl-htpy
```

<!-- rosetta-agda-block: proposition-13.1.1-homotopy-induction-predicate -->

```agda
induction-principle-homotopies :
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  (f : (x : A) → B x) → Typeω
induction-principle-homotopies f =
  is-identity-system (f ~_) f (refl-htpy)
```

<!-- rosetta-agda-block: proposition-13.1.1-extensionality-and-contractibility -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (x : A) → B x)
  where

  abstract
    based-function-extensionality-is-contr-htpy :
      is-contr (Σ ((x : A) → B x) (λ g → f ~ g)) →
      based-function-extensionality f
    based-function-extensionality-is-contr-htpy H =
      fundamental-theorem-id H (λ g → htpy-eq {f = f} {g})

  abstract
    is-contr-htpy-based-function-extensionality :
      based-function-extensionality f →
      is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
    is-contr-htpy-based-function-extensionality =
      fundamental-theorem-id' (λ g → htpy-eq {f = f} {g})
```

<!-- rosetta-agda-block: proposition-13.1.1-induction-from-contractibility -->

```agda
abstract
  induction-principle-homotopies-is-contr-htpy :
    {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (x : A) → B x) →
    is-contr (Σ ((x : A) → B x) (λ g → f ~ g)) →
    induction-principle-homotopies f
  induction-principle-homotopies-is-contr-htpy f =
    is-identity-system-is-contr f refl-htpy
```

<!-- rosetta-agda-block: proposition-13.1.1-contractibility-from-induction -->

```agda
abstract
  is-contr-htpy-induction-principle-homotopies :
    {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (x : A) → B x) →
    induction-principle-homotopies f →
    is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-htpy-induction-principle-homotopies f =
    is-torsorial-is-identity-system f refl-htpy
```
<!-- rosetta-item-end: proposition-13.1.1 -->

There is, however, yet a fourth condition equivalent to the function extensionality principle: the *weak* function extensionality principle.
The weak function extensionality principle asserts that any dependent product of contractible types is again contractible.

The following theorem is stated with respect to an arbitrary universe `𝒰`, because we will use it in Theorem 17.3.2 to show that the univalence axiom implies function extensionality.

## Theorem 13.1.2

<!-- rosetta-item: theorem-13.1.2; latex-label: thm:funext_wkfunext -->

Consider a universe `𝒰`.
The following are equivalent:

1.  The function extensionality principle holds in `𝒰`: For every type family `B` over `A` in `𝒰` and any `f,g:Π(x:A) B(x)`, the map
```text
htpy-eq : (f=g)→ (f~ g)
```
    is an equivalence.

2.  The **weak function extensionality principle** holds in `𝒰`: For every type family `B` over `A` in `𝒰` one has
```text
(Π(x:A) is-contr(B(x)))→is-contr(Π(x:A) B(x)).
```

### Proof

<!-- rosetta-item: subheading-13.1-proof-2 -->

*Proof.* First, we show that function extensionality implies weak function extensionality, suppose that each `B(a)` is contractible with center of contraction `c(a)` and contraction `C_a:Π(y:B(a)) c(a)=y`.
Then we take `c≔ λ a. c(a)` to be the center of contraction of `Π(x:A) B(x)`.
To construct the contraction we have to define a term of type
```text
Π(f:Π(x:A) B(x)) c=f.
```
Let `f:Π(x:A) B(x)`.
By function extensionality we have a map `{(c~ f)}→ {(c=f)}`, so it suffices to construct a term of type `c~ f`.
Here we take `λ a.
C_a(f(a))`.
This completes the proof that function extensionality implies weak function extensionality.

It remains to show that weak function extensionality implies function extensionality.
By Proposition 13.1.1 it suffices to show that the type
```text
Σ(g:Π(x:A) B(x)) f~ g
```
is contractible for any `f:Π(x:A) B(x)`.
In order to do this, we first note that we have a section-retraction pair
```text
(Σ(g:Π(x:A) B(x)) f~ g)
⟶[i] (Π(x:A) Σ(b:B(x)) f(x)=b)
⟶[r] (Σ(g:Π(x:A) B(x)) f~ g)
```
Here we have the functions
```text
i ≔ λ (g,H). λ x. (g(x),H(x))
r ≔ λ p. (λ x. pr 1(p(x)),λ x. pr 2(p(x))).
```
Their composite is homotopic to the identity function by the computation rule for `Σ`-types and the `η`-rule for `Π`-types:
```text
r(i(g,H)) ≐ r(λ x. (g(x),H(x)))
≐ (λ x. g(x),λ x. H(x))
≐ (g,H).
```
Now we observe that the type `Π(x:A) Σ(b:B(x)) f(x)=b` is a product of contractible types, so it is contractible by our assumption of the weak function extensionality principle.
The claim now follows, because retracts of contractible types are contractible by Exercise 10.2. ◻

<!-- rosetta-agda-block: theorem-13.1.2-universe-extensionality -->

```agda
function-extensionality-Level : (l1 l2 : Level) → Type (lsuc l1 ⊔ lsuc l2)
function-extensionality-Level l1 l2 =
  {A : Type l1} {B : A → Type l2}
  (f : (x : A) → B x) → based-function-extensionality f
```

<!-- rosetta-agda-block: theorem-13.1.2-weak-extensionality -->

```agda
instance-weak-function-extensionality :
  {l1 l2 : Level} (A : Type l1) (B : A → Type l2) → Type (l1 ⊔ l2)
instance-weak-function-extensionality A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

weak-function-extensionality-Level : (l1 l2 : Level) → Type (lsuc l1 ⊔ lsuc l2)
weak-function-extensionality-Level l1 l2 =
  (A : Type l1) (B : A → Type l2) → instance-weak-function-extensionality A B

weak-function-extensionality : Typeω
weak-function-extensionality =
  {l1 l2 : Level} → weak-function-extensionality-Level l1 l2
```

<!-- rosetta-agda-block: theorem-13.1.2-weak-extensionality-equivalence -->

```agda
abstract
  weak-funext-funext :
    {l1 l2 : Level} →
    function-extensionality-Level l1 l2 →
    weak-function-extensionality-Level l1 l2
  pr1 (weak-funext-funext funext A B is-contr-B) x =
    center (is-contr-B x)
  pr2 (weak-funext-funext funext A B is-contr-B) f =
    map-section-is-equiv
      ( funext (λ x → center (is-contr-B x)) f)
      ( λ x → contraction (is-contr-B x) (f x))

abstract
  funext-weak-funext :
    {l1 l2 : Level} →
    weak-function-extensionality-Level l1 l2 →
    function-extensionality-Level l1 l2
  funext-weak-funext weak-funext {A = A} {B} f =
    fundamental-theorem-id
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → f x ＝ b))
        ( ( λ t x → (pr1 t x , pr2 t x)) ,
          ( λ t → (pr1 ∘ t , pr2 ∘ t)) ,
          ( λ t → eq-pair-eq-fiber refl))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → f x ＝ b))
          ( λ x → is-contr-Id (f x))))
      ( λ g → htpy-eq {g = g})
```
<!-- rosetta-item-end: theorem-13.1.2 -->

We will henceforth assume the function extensionality principle as an axiom.

## Axiom 13.1.3

<!-- rosetta-item: axiom-13.1.3; latex-label: axiom:funext -->

For any type family `B` over `A`, and any two dependent functions `f,g:Π(x:A) B(x)`, the map
```text
htpy-eq:(f=g)→ (f~ g)
```
is an equivalence.
We will write `eq-htpy` for its inverse.

<!-- rosetta-agda-block: axiom-13.1.3-extensionality-predicate -->

```agda
function-extensionality : Typeω
function-extensionality = {l1 l2 : Level} → function-extensionality-Level l1 l2
```

### Assumed function extensionality: the pinned coherent-inverse presentation

<!-- rosetta-agda-block: axiom-13.1.3-assumed-coherent-function-extensionality -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x}
  where

  postulate
    eq-htpy : f ~ g → f ＝ g

    is-section-eq-htpy : is-section htpy-eq eq-htpy

    is-retraction-eq-htpy' : is-retraction htpy-eq eq-htpy

    coh-eq-htpy' :
      coherence-is-coherently-invertible
        ( htpy-eq)
        ( eq-htpy)
        ( is-section-eq-htpy)
        ( is-retraction-eq-htpy')

funext : function-extensionality
funext f g =
  is-equiv-is-invertible eq-htpy is-section-eq-htpy is-retraction-eq-htpy'
```

<!-- rosetta-agda-block: axiom-13.1.3-extensionality-equivalences -->

```agda
module _
  {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
  where

  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext) = htpy-eq
  pr2 (equiv-funext {f} {g}) = funext f g

  is-equiv-eq-htpy :
    (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g})
  is-equiv-eq-htpy f g =
    is-equiv-is-invertible htpy-eq is-retraction-eq-htpy' is-section-eq-htpy

  abstract
    is-retraction-eq-htpy :
      {f g : (x : A) → B x} → is-retraction (htpy-eq {f = f} {g}) eq-htpy
    is-retraction-eq-htpy {f} {g} = is-retraction-map-section-is-equiv (funext f g)

  eq-htpy-refl-htpy :
    (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
  eq-htpy-refl-htpy f = is-retraction-eq-htpy refl

  equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
  pr1 (equiv-eq-htpy {f} {g}) = eq-htpy
  pr2 (equiv-eq-htpy {f} {g}) = is-equiv-eq-htpy f g
```
<!-- rosetta-item-end: axiom-13.1.3 -->

## Remark 13.1.4

<!-- rosetta-item: remark-13.1.4 -->

The function extensionality axiom is added to type theory by adding the rule

<!-- rosetta-proof-tree: 828a985f9fa9; review: pending -->

*Proof tree (automatic faithful draft).*

```text
Γ,x:A⊢ B(x) type   Γ⊢ f : Π(x:A) B(x)   Γ⊢ g : Π(x:A) B(x)
──────────────────────────────────────────────────────────
             Γ⊢funext:is-equiv(htpy-eq_{f,g})
```

<!-- rosetta-item-end: remark-13.1.4 -->

In the following theorem we extend the weak function extensionality principle to general truncation levels.

## Theorem 13.1.5

<!-- rosetta-item: theorem-13.1.5; latex-label: thm:trunc_pi -->

For any type family `B` over `A` one has
```text
(Π(x:A) is-trunc{k}(B(x)))→ is-trunc{k}(Π(x:A) B(x)).
```

### Proof

<!-- rosetta-item: subheading-13.1-proof-3 -->

*Proof.* The theorem is proven by induction on `k≥ -2`.
The base case is just the weak function extensionality principle, which was shown to follow from function extensionality in Theorem 13.1.2.

For the inductive step, assume that the `k`-truncated types are closed under `Π`-types, and consider a family `B` of `(k+1)`-truncated types.
To show that the type `Π(x:A) B(x)` is `(k+1)`-truncated, we have to show that the type `f=g` is `k`-truncated for every `f,g:Π(x:A)`.
By function extensionality, the type `f=g` is equivalent to `f~ g` for any two dependent functions `f,g:Π(x:A) B(x)`.
Now observe that `f~ g` is a dependent product of `k`-truncated types, and therefore it is `k`-truncated by the inductive hypothesis.
Since the `k`-truncated types are closed under equivalences by Proposition 12.4.5, it follows that the type `f=g` is `k`-truncated. ◻

<!-- rosetta-agda-block: theorem-13.1.5-contractible-dependent-products -->

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : Type l1} {B : A → Type l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  pr1 (is-contr-Π {A = A} {B = B} H) x = center (H x)
  pr2 (is-contr-Π {A = A} {B = B} H) f =
    eq-htpy (λ x → contraction (H x) (f x))
```

<!-- rosetta-agda-block: theorem-13.1.5-truncated-dependent-products -->

```agda
abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : Type l1} {B : A → Type l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k (f ~ g) htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))
```

<!-- rosetta-agda-block: theorem-13.1.5-proposition-valued-dependent-products -->

```agda
abstract
  is-prop-Π :
    {l1 l2 : Level} {A : Type l1} {B : A → Type l2} →
    ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
  is-prop-Π H =
    is-prop-is-proof-irrelevant
      ( λ f → is-contr-Π (λ x → is-proof-irrelevant-is-prop (H x) (f x)))
```
<!-- rosetta-item-end: theorem-13.1.5 -->

## Corollary 13.1.6

<!-- rosetta-item: corollary-13.1.6; latex-label: cor:funtype_trunc -->

Suppose `B` is a `k`-type.
Then `A→ B` is also a `k`-type, for any type `A`.

<!-- rosetta-agda-block: corollary-13.1.6-truncated-function-types -->

```agda
abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : Type l1} {B : Type l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)
```

<!-- rosetta-agda-block: corollary-13.1.6-proposition-valued-function-types -->

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : Type l1} {B : Type l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type H = is-prop-Π (λ _ → H)
```
<!-- rosetta-item-end: corollary-13.1.6 -->

## Remark 13.1.7

<!-- rosetta-item: remark-13.1.7 -->

It follows that `¬ A` is a proposition for each type `A`.
Note that it requires function extensionality even just to prove that `¬ P` is a proposition for any proposition `P`.

<!-- rosetta-agda-block: remark-13.1.7-negations-are-propositions -->

```agda
is-prop-neg : {l : Level} {A : Type l} → is-prop (¬ A)
is-prop-neg = is-prop-function-type is-prop-empty
```
<!-- rosetta-item-end: remark-13.1.7 -->
