# Section 12.4 General truncation levels

```agda
module section-12-4-general-truncation-levels where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-11-4-embeddings
open import section-11-6-the-structure-identity-principle
open import exercise-10-2-contractible-retracts
open import exercise-12-8-retracts-of-truncated-types
```

<!-- rosetta-item: section-12.4 -->

Consider a type `A` in a universe `𝒰`.
The conditions
```text
is-contr(A) ≔ Σ(a:A) Π(x:A) a=x
is-prop(A) ≔ Π(x,y:A) is-contr(x=y)
is-set(A) ≔ Π(x,y:A) is-prop(x=y)
```
define the first few layers of the hierarchy of truncation levels.
This hierarchy starts at the level of the contractible types, which we call level `-2`.
The next level is the level of propositions, and at level `0` we have the sets.

The indexing type of the truncation levels, which will be equivalent to the type `ℤ_{≥ -2}` of integers greater than `-2`, is an inductive type `𝕋` equipped with the constructors
```text
-2 : 𝕋
succT : 𝕋→𝕋.
```
The natural inclusion `i:ℕ→ 𝕋` is defined recursively by
```text
i(0) ≔ succT(succT(-2))
i(succ-ℕ(n)) ≔ succT(i(n)).
```
Of course, we will simply write `-2` for `-2` and `k+1` for `succT(k)`.

### Truncation indices and the natural-number inclusion

<!-- rosetta-agda-block: section-12.4-truncation-levels -->

```agda
data 𝕋 : Type lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋
```

<!-- rosetta-agda-block: section-12.4-truncation-level-aliases -->

```agda
neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 neg-two-𝕋

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 neg-one-𝕋
```

<!-- rosetta-agda-block: section-12.4-natural-number-inclusion -->

```agda
truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ n) =
  succ-𝕋 (truncation-level-minus-two-ℕ n)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ = succ-𝕋 ∘ truncation-level-minus-two-ℕ

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ = succ-𝕋 ∘ truncation-level-minus-one-ℕ
```

## Definition 12.4.1

<!-- rosetta-item: definition-12.4.1 -->

We define `is-trunc : 𝕋→𝒰→𝒰` recursively by
```text
is-trunc{-2}(A) ≔ is-contr(A)
is-trunc{k+1}(A) ≔ Π(x,y:A) is-trunc{k}(x = y).
```
For any type `A`, we say that `A` is **`k`-truncated**, or a **`k`-type**, if there is a term of type `is-trunc{k}(A)`.
We also say that a type `A` is a **proper `(k+1)`-type** if `A` is a `(k+1)`-type and not a `k`-type.

Given a universe `𝒰`, we define the universe `𝒰^{≤ k}` of `k`-truncated types by
```text
𝒰^{≤ k}≔Σ(X:𝒰) is-trunc{k}(X).
```

Furthermore, we say that a map `f:A→ B` is `k`-truncated if its fibers are `k`-truncated.

<!-- rosetta-agda-block: definition-12.4.1-truncated-types -->

```agda
is-trunc : {l : Level} (k : 𝕋) → Type l → Type l
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (x ＝ y)
```

<!-- rosetta-agda-block: definition-12.4.1-proper-successor-types -->

```agda
is-proper-succ-trunc : {l : Level} (k : 𝕋) → Type l → Type l
is-proper-succ-trunc k A =
  Σ (is-trunc (succ-𝕋 k) A) (λ _ → is-empty (is-trunc k A))
```

<!-- rosetta-agda-block: definition-12.4.1-universe-of-truncated-types -->

```agda
Truncated-Type : (l : Level) → 𝕋 → Type (lsuc l)
Truncated-Type l k = Σ (Type l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where

  type-Truncated-Type : Truncated-Type l k → Type l
  type-Truncated-Type = pr1

  is-trunc-type-Truncated-Type :
    (A : Truncated-Type l k) → is-trunc k (type-Truncated-Type A)
  is-trunc-type-Truncated-Type = pr2
```

<!-- rosetta-agda-block: definition-12.4.1-truncated-maps -->

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : Type l1} {B : Type l2} → (A → B) → Type (l1 ⊔ l2)
  is-trunc-map f = (y : _) → is-trunc k (fiber f y)

  trunc-map : (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
  trunc-map A B = Σ (A → B) is-trunc-map
```
<!-- rosetta-item-end: definition-12.4.1 -->

## Remark 12.4.2

<!-- rosetta-item: remark-12.4.2 -->

There is a subtlety in the definition of `is-trunc` regarding universes.
Note that the truncation levels are defined with respect to a universe `𝒰`.
To be completely precise, we should therefore write `is-trunc{k}^{𝒰}(A)` for the type `is-trunc{k}(A)` defined with respect to the universe `𝒰`.
If `A` is also contained in a second universe `𝒱`, then it is legitimate to ask whether
```text
is-trunc{k}^{𝒰}(A)↔is-trunc{k}^{𝒱}(A).
```
A simple inductive argument shows that this is indeed the case, where the base case follows from the judgmental equalities
```text
is-trunc{-2}^{𝒰}(A) ≐ Σ(x:A) Π(y:A) x=y
is-trunc{-2}^{𝒱}(A) ≐ Σ(x:A) Π(y:A) x=y.
```
We may therefore safely omit explicit reference to the universes when considering truncatedness of a type.

### Agda universe representation: equivalent lifted types

<!-- rosetta-agda-block: remark-12.4.2-universe-lift -->

```agda
data raise (l : Level) {l1 : Level} (A : Type l1) : Type (l1 ⊔ l) where
  map-raise : A → raise l A
```

<!-- rosetta-agda-block: remark-12.4.2-lift-equivalence -->

```agda
module _
  {l l1 : Level} {A : Type l1}
  where

  map-inv-raise : raise l A → A
  map-inv-raise (map-raise x) = x

  is-section-map-inv-raise : (map-raise ∘ map-inv-raise) ~ id
  is-section-map-inv-raise (map-raise x) = refl

  is-retraction-map-inv-raise : (map-inv-raise ∘ map-raise) ~ id
  is-retraction-map-inv-raise x = refl

  is-equiv-map-raise : is-equiv (map-raise {l} {l1} {A})
  is-equiv-map-raise =
    is-equiv-is-invertible
      map-inv-raise
      is-section-map-inv-raise
      is-retraction-map-inv-raise

compute-raise : (l : Level) {l1 : Level} (A : Type l1) → A ≃ raise l A
pr1 (compute-raise l A) = map-raise
pr2 (compute-raise l A) = is-equiv-map-raise
```
<!-- rosetta-item-end: remark-12.4.2 -->

We show in the following theorem that the truncation levels are successively contained in one another.

## Proposition 12.4.3

<!-- rosetta-item: proposition-12.4.3; latex-label: thm:istrunc_next -->

If `A` is a `k`-type, then `A` is also a `(k+1)`-type.

### Proof

<!-- rosetta-item: subheading-12.4-proof -->

*Proof.* We have seen in Example 12.1.2 that contractible types are propositions.
This proves the base case.
For the inductive step, note that if any `k`-type is also a `(k+1)`-type, then any `(k+1)`-type is a `(k+2)`-type, since its identity types are `k`-types and therefore `(k+1)`-types. ◻

<!-- rosetta-agda-block: proposition-12.4.3-successor-truncation -->

```agda
abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {l : Level} {A : Type l} → is-trunc k A → is-trunc (succ-𝕋 k) A
  pr1 (is-trunc-succ-is-trunc neg-two-𝕋 H x y) = eq-is-contr H
  pr2 (is-trunc-succ-is-trunc neg-two-𝕋 H x .x) refl = left-inv (pr2 H x)
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y = is-trunc-succ-is-trunc k (H x y)
```
<!-- rosetta-item-end: proposition-12.4.3 -->

It is immediate from the proof of Proposition 12.4.3 that the identity types of `k`-types are also `k`-types.

## Corollary 12.4.4

<!-- rosetta-item: corollary-12.4.4 -->

If `A` is a `k`-type, then its identity types are also `k`-types.`□`

<!-- rosetta-agda-block: corollary-12.4.4-truncated-identities -->

```agda
abstract
  is-trunc-Id :
    {l : Level} {k : 𝕋} {A : Type l} →
    is-trunc k A → (x y : A) → is-trunc k (x ＝ y)
  is-trunc-Id {l} {k} = is-trunc-succ-is-trunc k
```
<!-- rosetta-item-end: corollary-12.4.4 -->

## Proposition 12.4.5

<!-- rosetta-item: proposition-12.4.5; latex-label: thm:ktype_eqv -->

If `e:A ≃ B` is an equivalence, and `B` is a `k`-type, then so is `A`.

### Proof

<!-- rosetta-item: subheading-12.4-proof-2 -->

*Proof.* We have seen in Exercise 10.3 that if `B` is contractible and `e:A ≃ B` is an equivalence, then `A` is also contractible.
This proves the base case.

For the inductive step, assume that the `k`-types are stable under equivalences, and consider `e:A ≃ B` where `B` is a `(k+1)`-type.
In Theorem 11.4.2 we have seen that
```text
ap{e}:(x = y)→(e(x) = e(y))
```
is an equivalence for any `x,y`.
Note that `e(x) = e(y)` is a `k`-type, so by the induction hypothesis it follows that `x = y` is a `k`-type.
This proves that `A` is a `(k+1)`-type. ◻

### Upstream proof prerequisite: truncation of retracts (Exercise 12.8(b))

<!-- rosetta-agda-block: proposition-12.4.5-retract-prerequisite -->

```agda
module _
  {l1 l2 : Level}
  where

  is-trunc-retract-of :
    {k : 𝕋} {A : Type l1} {B : Type l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of {neg-two-𝕋} = is-contr-retract-of _
  is-trunc-retract-of {succ-𝕋 k} R H x y =
    is-trunc-retract-of (retract-eq R x y) (H (pr1 R x) (pr1 R y))
```

<!-- rosetta-agda-block: proposition-12.4.5-equivalence-invariance -->

```agda
abstract
  is-trunc-is-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : Type l1} (B : Type l2) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv k B f is-equiv-f =
    is-trunc-retract-of (f , (pr2 is-equiv-f))

abstract
  is-trunc-equiv :
    {l1 l2 : Level} (k : 𝕋) {A : Type l1} (B : Type l2) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (f , is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-trunc-is-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : Type l1) {B : Type l2} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-section-is-equiv is-equiv-f)
      ( is-equiv-map-section-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-trunc-equiv' :
    {l1 l2 : Level} (k : 𝕋) (A : Type l1) {B : Type l2} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (f , is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f
```

### Remark 12.4.2 revisited: truncation of lifted types

<!-- rosetta-agda-block: proposition-12.4.5-lifted-truncation -->

```agda
abstract
  is-trunc-raise :
    {l1 : Level} (l : Level) (k : 𝕋) (A : Type l1) →
    is-trunc k A → is-trunc k (raise l A)
  is-trunc-raise l k A = is-trunc-equiv' k A (compute-raise l A)
```

<!-- rosetta-agda-block: proposition-12.4.5-truncation-from-lift -->

```agda
abstract
  is-trunc-is-trunc-raise :
    {l1 : Level} (l : Level) (k : 𝕋) (A : Type l1) →
    is-trunc k (raise l A) → is-trunc k A
  is-trunc-is-trunc-raise l k A =
    is-trunc-equiv k (raise l A) (compute-raise l A)
```
<!-- rosetta-item-end: proposition-12.4.5 -->

## Corollary 12.4.6

<!-- rosetta-item: corollary-12.4.6; latex-label: cor:emb_into_ktype -->

If `f:A→ B` is an embedding, and `B` is a `(k+1)`-type, then so is `A`.

### Proof

<!-- rosetta-item: subheading-12.4-proof-3 -->

*Proof.* By the assumption that `f` is an embedding, the action on paths
```text
ap{f}:(x = y)→ (f(x) = f(y))
```
is an equivalence for every `x,y:A`.
Since `B` is assumed to be a `(k+1)`-type, it follows that `f(x)=f(y)` is a `k`-type for every `x,y:A`.
Therefore we conclude by Proposition 12.4.5 that `x = y` is a `k`-type for every `x,y:A`.
In other words, `A` is a `(k+1)`-type. ◻

<!-- rosetta-agda-block: corollary-12.4.6-truncation-through-embeddings -->

```agda
abstract
  is-trunc-is-emb :
    {l1 l2 : Level} (k : 𝕋) {A : Type l1} {B : Type l2} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (f x ＝ f y) (ap f {x} {y}) (Ef x y) (H (f x) (f y))
```
<!-- rosetta-item-end: corollary-12.4.6 -->

We end this section with a theorem that characterizes `(k+1)`-truncated maps.
Note that it generalizes Theorem 12.2.3, which asserts that a map is an embedding if and only if its fibers are propositions.

## Theorem 12.4.7

<!-- rosetta-item: theorem-12.4.7; latex-label: thm:trunc_ap -->

Let `f:A→ B` be a map.
The following are equivalent:

1.  The map `f` is `(k+1)`-truncated.

2.  For each `x,y:A`, the map
```text
ap{f} : (x=y)→ (f(x)=f(y))
```
    is `k`-truncated.

### Proof

<!-- rosetta-item: subheading-12.4-proof-4 -->

*Proof.* First we show that for any `s,t:fib(f, b)` there is an equivalence
```text
(s=t) ≃ fib(ap{f}, pr 2(s) ∙ pr 2(t)^{-1})
```
We do this by `Σ`-induction on `s` and `t`, and then we calculate
```text
((x,p)=(y,q)) ≃ Eq-fib_f((x,p),(y,q))
≐ Σ(α:x=y) p=ap_{f}(α) ∙ q
≃ Σ(α:x=y) ap_{f}(α) ∙ q=p
≃ Σ(α:x=y) ap_{f}(α)=p ∙ q^{-1}
≐ fib(ap{f}, p ∙ q^{-1}).
```
By these equivalences, it follows that if `ap{f}` is `k`-truncated, then for each `s,t:fib(f, b)` the identity type `s=t` is equivalent to a `k`-truncated type, and therefore we obtain by Proposition 12.4.5 that `f` is `(k+1)`-truncated.

For the converse, note that we have equivalences
```text
fib(ap{f}, p) ≃ ((x,p)=(y,refl)).
```
It follows that if `f` is `(k+1)`-truncated, then the identity type `(x,p)=(y,refl)` in `fib(f, f(y))` is `k`-truncated for any `p:f(x)=f(y)`.
We conclude by Proposition 12.4.5 that the fiber `fib(ap{f}, p)` is `k`-truncated. ◻

<!-- rosetta-agda-block: theorem-12.4.7-truncated-action-on-identities -->

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : Type l1} {B : Type l2} (f : A → B)
  where

  abstract
    is-trunc-map-succ-is-trunc-map-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-succ-is-trunc-map-ap is-trunc-map-ap-f b (x , p) (x' , p') =
      is-trunc-equiv k
        ( fiber (ap f) (p ∙ inv p'))
        ( equiv-fiber-ap-eq-fiber f (x , p) (x' , p'))
        ( is-trunc-map-ap-f x x' (p ∙ inv p'))

  abstract
    is-trunc-map-ap-is-trunc-map-succ :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-map-ap-is-trunc-map-succ is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( (x , p) ＝ (y , refl))
        ( eq-fiber-fiber-ap f x y p)
        ( is-equiv-eq-fiber-fiber-ap f x y p)
        ( is-trunc-map-f (f y) (x , p) (y , refl))
```
<!-- rosetta-item-end: theorem-12.4.7 -->
