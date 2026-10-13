# Section 18.2 The universal property of set quotients

```agda
module section-18-2-the-universal-property-of-set-quotients where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-5-4-transport
open import section-7-2-the-congruence-relations-on-natural-numbers
open import section-9-1-homotopies
open import section-9-2-bi-invertible-maps
open import exercise-9-1-groupoid-operations-equivalences
open import exercise-9-4-three-for-two-equivalences
open import section-10-1-contractible-types
open import section-10-3-contractible-maps
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-11-4-embeddings
open import section-11-6-the-structure-identity-principle
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-12-3-sets
open import section-12-4-general-truncation-levels
open import exercise-12-3-injective-maps-into-sets
open import exercise-12-6-truncated-sigma-types
open import exercise-12-8-retracts-of-truncated-types
open import section-13-1-equivalent-forms-of-function-extensionality
open import section-13-4-composing-with-equivalences
open import exercise-13-3-truncatedness-is-a-proposition
open import exercise-13-4-equivalence-structure-is-a-proposition
open import section-14-2-propositional-truncations-as-higher-inductive-types
open import section-14-3-logic-in-type-theory
open import section-15-1-the-image-of-a-map
open import section-15-2-surjective-maps
open import section-17-1-equivalent-forms-of-the-univalence-axiom
open import section-17-2-propositional-extensionality
open import section-18-1-equivalence-relations-and-the-replacement-axiom
```

The quotient `A/R` is constructed as the image of `R`, so we obtain a commuting triangle

```text
       q_R
  A --------> A/R
   \         /
    \       /
   R \     / i_R
      \   /
       ∨ ∨
    Prop_𝒰^A
```

and the embedding `i_R : A/R → Prop_𝒰^A` satisfies the universal property of the image of `R`.
This universal property is, however, not the usual universal property of the quotient.

## Definition 18.2.1

Consider a map `q : A → B` into a set `B` satisfying the property that

```text
  R(x,y) → (q(x) = q(y))
```

for all `x, y : A`.
We say that `q : A → B` **is a set quotient** of `R`, or that `q` satisfies the **universal property of the set quotient by `R`**, if for every map `f : A → X` into a set `X` such that `f(x) = f(y)` whenever `R(x,y)` holds, there is a unique extension

```text
     A
    | \
    |  \
  q |   \ f
    |    \
    ∨     ∨
    B ---> X
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  reflects-equivalence-relation :
    {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ l2 ⊔ l3)
  reflects-equivalence-relation f =
    {x y : A} → sim-equivalence-relation R x y → (f x ＝ f y)

  reflecting-map-equivalence-relation : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  reflecting-map-equivalence-relation B =
    Σ (A → B) reflects-equivalence-relation

  map-reflecting-map-equivalence-relation :
    {l3 : Level} {B : UU l3} → reflecting-map-equivalence-relation B → A → B
  map-reflecting-map-equivalence-relation = pr1

  reflects-map-reflecting-map-equivalence-relation :
    {l3 : Level} {B : UU l3} (f : reflecting-map-equivalence-relation B) →
    reflects-equivalence-relation (map-reflecting-map-equivalence-relation f)
  reflects-map-reflecting-map-equivalence-relation = pr2

  is-prop-reflects-equivalence-relation :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) →
    is-prop (reflects-equivalence-relation f)
  is-prop-reflects-equivalence-relation B f =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ y →
            is-prop-function-type (is-set-type-Set B (f x) (f y))))

  reflects-prop-equivalence-relation :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) → Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (reflects-prop-equivalence-relation B f) = reflects-equivalence-relation f
  pr2 (reflects-prop-equivalence-relation B f) =
    is-prop-reflects-equivalence-relation B f

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  htpy-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) → UU (l1 ⊔ l3)
  htpy-reflecting-map-equivalence-relation g =
    pr1 f ~ pr1 g

  refl-htpy-reflecting-map-equivalence-relation :
    htpy-reflecting-map-equivalence-relation f
  refl-htpy-reflecting-map-equivalence-relation = refl-htpy

  htpy-eq-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    f ＝ g → htpy-reflecting-map-equivalence-relation g
  htpy-eq-reflecting-map-equivalence-relation .f refl =
    refl-htpy-reflecting-map-equivalence-relation

  is-torsorial-htpy-reflecting-map-equivalence-relation :
    is-torsorial (htpy-reflecting-map-equivalence-relation)
  is-torsorial-htpy-reflecting-map-equivalence-relation =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (pr1 f))
      ( is-prop-reflects-equivalence-relation R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-equivalence-relation g)
  is-equiv-htpy-eq-reflecting-map-equivalence-relation =
    fundamental-theorem-id
      is-torsorial-htpy-reflecting-map-equivalence-relation
      htpy-eq-reflecting-map-equivalence-relation

  extensionality-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    (f ＝ g) ≃ htpy-reflecting-map-equivalence-relation g
  pr1 (extensionality-reflecting-map-equivalence-relation g) =
    htpy-eq-reflecting-map-equivalence-relation g
  pr2 (extensionality-reflecting-map-equivalence-relation g) =
    is-equiv-htpy-eq-reflecting-map-equivalence-relation g

  eq-htpy-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    htpy-reflecting-map-equivalence-relation g → f ＝ g
  eq-htpy-reflecting-map-equivalence-relation g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-equivalence-relation g)

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-Set-Quotient :
    {l : Level} (X : Set l) →
    (hom-Set B X) → reflecting-map-equivalence-relation R (type-Set X)
  pr1 (precomp-Set-Quotient X g) =
    g ∘ (map-reflecting-map-equivalence-relation R f)
  pr2 (precomp-Set-Quotient X g) r =
    ap g (reflects-map-reflecting-map-equivalence-relation R f r)

is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B)) → UUω
is-set-quotient R B f =
  {l : Level} (X : Set l) → is-equiv (precomp-Set-Quotient R B f X)

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient : UUω
  universal-property-set-quotient =
    {l : Level} (X : Set l)
    (g : reflecting-map-equivalence-relation R (type-Set X)) →
    is-contr
      ( Σ ( hom-Set B X)
          ( λ h →
            ( h ∘ map-reflecting-map-equivalence-relation R f) ~
            ( map-reflecting-map-equivalence-relation R g)))
```

## Remark 18.2.2

Formally, we express the universal property of the quotient by `R` as follows.
Consider a map `q : A → B` that satisfies the property that

```text
  H : Π(x, y : A) R(x,y) → (f(x) = f(y)).
```

Then there is for any set `X` a map

```text
  q^⋆ : (B → X) → (Σ(f : A → X) Π(x, y : A) R(x,y) → (f(x) = f(y))).
```

This map takes a function `h : B → X` to the pair

```text
  q^⋆(h) ≔ (h ∘ q, λ x. λ y. λ r. ap_{h}(H_{x,y}(r))).
```

The universal property of the set quotient of `R` asserts that the map `q^⋆` is an equivalence for every set `X`.
It is important to note that the universal property of set quotients is formulated with respect to sets.

## Theorem 18.2.3

Consider a type `A` and a universe `𝒰` containing `A`.
Furthermore, let `R : A → (A → Prop_𝒰)` be an equivalence relation, and consider a map `q : A → B` into a set `B`, not necessarily in `𝒰`.
Then the following are equivalent.

1. The map `q` satisfies the property that

   ```text
     q(x) = q(y)
   ```

   for every `x, y : A` for which `R(x,y)` holds, and moreover `q` satisfies the universal property of the set quotient of `R`.

2. The map `q` is surjective and **effective**, which means that for each `x, y : A` we have an equivalence

   ```text
     (q(x) = q(y)) ≃ R(x,y).
   ```

3. The map `R : A → (A → Prop_𝒰)` extends along `q` to an embedding

   ```text
            q_R
       A --------> A/R
        \         /
         \       /
        R \     / i_R
           \   /
            ∨ ∨
         Prop_𝒰^A
   ```

   and the embedding `i` satisfies the universal property of the image inclusion of `R`.

In Theorem 18.2.3 we don’t assume that `B` is in the same universe as `A` and `R`, because we want to apply it to `B ≔ im(R)`.
As we will see below, this extra generality only affects the proof that (2) implies (3).

### Proof

We first show that (2) is equivalent to (3), since this is the easiest part.
After that, we will show that (1) is equivalent to (2).

Assume that (3) holds.
Then `q` is surjective by Theorem 15.2.5.
Moreover, we have

```text
  R(x,y) ≃ R(x) = R(y)
         ≃ i(q(x))=i(q(y))
         ≃ q(x)=q(y)
```

In this calculation, the first equivalence holds by Corollary 18.1.4; the second equivalence holds since we have a homotopy `R ~ i ∘ q`; and the third equivalence holds since `i` is an embedding.
This completes the proof that (3) implies (2).

Next, we show that (2) implies (3).
First, we want to define a map

```text
  i : B → Prop_𝒰^A.
```

We would like to define `i(b,a) ≔ (b = q(a))`.
This direct definition does not go through, however, because the type `B` is not assumed to be in `𝒰`.
Nevertheless, observe that by the assumption that `q` is surjective and effective, the type `B` is locally `𝒰`-small.
To see this, first note that `is-small_U(X)` is a proposition for any type `X` by Proposition 17.1.5.
Using the assumption that `q` is surjective, it follows from Proposition 15.2.3 that it suffices to show that `q(a) = q(a')` is `𝒰`-small for each `a, a' : A`.
This follows by the assumption that `q` is effective.
In particular, the identity type `b=q(a)` is a `𝒰`-small proposition, for every `b : B` and `a : A`.
Let us write `s(b,a)` for the element of type `is-small_𝒰(b = q(a))`.

Now consider a universe `𝒱` containing `B`.
Then we can define a map

```text
  j : B → (A → Σ(P : Prop_𝒱) is-small_𝒰(P))
```

by `j(b,a) ≔ (b = q(a),s(b,a))`, and now we obtain `i` from `j` by defining

```text
  i(b,a) := pr 1(s(b,a)).
```

Note that we have an equivalence `i(b,a)≃ (b = q(a))` for every `b : B` and `a : A`.
Then the triangle

```text
        q
  A --------> A/R
   \         /
    \       /
   R \     / i
      \   /
       ∨ ∨
    Prop_𝒰^A
```

commutes, since we have an equivalence

```text
  i(q(a),a') ≃ (q(a) = q(a')) ≃ R(a,a')
```

for each `a, a' : A`.
To show that `i` is an embedding, recall from Exercise 12.3 that it suffices to show that `i` is injective, i.e., that

```text
  Π(b, b' : B) (i(b) = i(b')) → (b = b'),
```

since the codomain of `i` is a set by Theorem 17.2.3.
Note that injectivity of a map into a set is a property, and that `q` is assumed to be surjective.
Hence by Proposition 15.2.3 it is sufficient to show that

```text
  Π(a, a' : A) (i(q(a)) = i(q(a'))) → (q(a) = q(a')).
```

Since `R ~ i ∘ q`, and `q(a) = q(a')` is assumed to be equivalent to `R(a,a')`, it suffices to show that

```text
  Π(a, a' : A) (R(a) = R(a')) → R(a,a'),
```

which follows directly from Corollary 18.1.4.
Thus we have shown that the factorization `R ~ i ∘ q` factors `R` as a surjective map followed by an embedding.
We conclude by Theorem 15.2.5 that the embedding `i` satisfies the universal property of the image factorization of `R`, which finishes the proof that (2) implies (3).

Now we show that (1) implies (2).
To see that `q` is surjective if it satisfies the assumptions in (1), consider the image factorization

```text
      q_q
  A --------> im(q)
   \         /
    \       /
   q \     / i_q
      \   /
       ∨ ∨
        B
```

We claim that the map `i_q` has a section.
To see this, we first note that we have

```text
  q_q(x) = q_q(y)
```

for any `x, y : A` satisfying `R(x,y)`, because if `R(x,y)` holds, then `q(x) = q(y)` and hence `i_q(q_q(x)) = i_q(q_q(y))` holds and `i_q` is an embedding.
Since `im(q)` is a set, we may apply the universal property of `q` and we obtain a unique extension of `q_q` along `q`

```text
     A
    | \
    |  \
  q |   \ q_q
    |    \
    ∨     ∨
    B ---> im(q)
       h
```

Now we observe that the composite `i_q ∘ h` is an extension of `q` along `q`, so it must be the identity function by uniqueness.
Thus we have established that `h` is a section of `i_q`.
Since `i_q` is an embedding with a section, it follows that `i_q` is an equivalence.
We conclude that `q` is surjective, because `q` is the composite `i_q ∘ q_q` of a surjective map followed by an equivalence.

Now we have to show that the map `q` is effective, i.e., that `q(x) = q(y)` is equivalent to `R(x,y)` for every `x, y : A`.
We first apply the universal property of `q` to obtain for each `x : A` an extension of `R(x)` along `q`

```text
     A
    | \
    |  \
  q |   \ R(x)
    |    \
    ∨     ∨
    B ---> Prop_𝒰
      R̃(x)
```

Since the triangle commutes, we have an equivalence `R̃(x,q(x')) ≃ R(x,x')` for each `x' : A`.
Now we apply Theorem 11.2.2 to see that the canonical family of maps

```text
  Π(y : B) (q(x) = y) → R̃(x,y)
```

is a family of equivalences.
Thus, we need to show that the type `Σ(y : B) R̃(x,y)` is contractible.
For the center of contraction, note that we have `q(x) : B`, and the type `R̃(x,q(x))` is equivalent to the type `R(x,x)`, which is inhabited by reflexivity of `R`.
To construct the contraction, it suffices to show that

```text
  Π(y : B) R̃(x,y) → (q(x) = y).
```

Since this is a property, and since we have already shown that `q` is a surjective map, we may apply Proposition 15.2.3, by which it suffices to show that

```text
  Π(x' : A) R̃(x,q(x')) → (q(x) = q(x')).
```

Since `R̃(x,q(x')) ≃ R(x,x')`, this is immediate from our assumption on `q`.
Thus we obtain the contraction, and we conclude that we have an equivalence `R̃(x,y) ≃ (q(x) = y)` for each `y : B`.
It follows that we have an equivalence

```text
  R(x,y) ≃ (q(x) = q(y))
```

for each `x, y : A`, which completes the proof that (1) implies (2).

It remains to show that (2) implies (1).
Assume (2), and let `f : A → X` be a map into a set `X`, satisfying the property that

```text
  Π(a, a' : A) R(a,a') → (f(a) = f(a')).
```

Our goal is to show that the type of extensions of `f` along `q` is contractible.
By Exercise 17.5 it follows that there is at most one such an extension, so it suffices to construct one.

In order to construct an extension, we will construct for every `b : B` a term `x : X` satisfying the property

```text
  P(x) ≔ ∃_{(a : A)} (f(a) = x)∧ (q(a) = b).
```

Before we make this construction, we first observe that there is at most one such `x`, i.e., that the type of `x : X` satisfying `P(x)` is in fact a proposition.
To see this, we need to show that `x = x'` for any `x, x' : X` satisfying `P(x)` and `P(x')`.
Since `X` is assumed to be a set, our goal of showing that `x = x'` is a property.
Therefore we may assume that we have `a, a' : A` satisfying

```text
   f(a) = x
   q(a) = b
  f(a') = x'
  q(a') = b.
```

It follows from these assumptions that `q(a) = q(a')`, and hence that `R(a,a')` holds.
This in turn implies that `f(a) = f(a')`, and hence that `x = x'`.

Now let `b : B`.
Our goal is to construct an `x : X` that satisfies the property

```text
  ∃_{(a : A)}(f(a) = x) ∧ (q(a) = b).
```

Since `q` is assumed to be surjective, we have `‖fib(q, b)‖`.
Moreover, since we have shown that at most one `x : X` exists with the asserted property, we get to assume that we have `a : A` satisfying `q(a) = b`.
Now we see that `x ≔ f(a)` satisfies the desired property.

Thus, we obtain a function `h : B → X` satisfying the property that for all `b : B` there exists an `a : A` such that

```text
  f(a) = h(b)    and    q(a) = b.
```

In particular, it follows that `h(q(a)) = f(a)` for all `a : A`, which completes the proof that (2) implies (1). ◻

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient-is-set-quotient :
    is-set-quotient R B f → universal-property-set-quotient R B f
  universal-property-set-quotient-is-set-quotient Q X g =
    is-contr-equiv'
      ( fiber (precomp-Set-Quotient R B f X) g)
      ( equiv-tot
        ( λ h →
          extensionality-reflecting-map-equivalence-relation R X
            ( precomp-Set-Quotient R B f X h)
            ( g)))
      ( is-contr-map-is-equiv (Q X) g)

  map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    type-Set B → type-Set C
  map-universal-property-set-quotient-is-set-quotient Uf C g =
    pr1 (center (universal-property-set-quotient-is-set-quotient Uf C g))

  triangle-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-set-quotient-is-set-quotient Uf C g) ∘
      ( map-reflecting-map-equivalence-relation R f)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-set-quotient-is-set-quotient Uf C g =
    ( pr2 (center (universal-property-set-quotient-is-set-quotient Uf C g)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  is-set-quotient-universal-property-set-quotient :
    universal-property-set-quotient R B f → is-set-quotient R B f
  is-set-quotient-universal-property-set-quotient Uf X =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv
          ( Σ ( hom-Set B X)
              ( λ h →
                ( h ∘ map-reflecting-map-equivalence-relation R f) ~
                ( map-reflecting-map-equivalence-relation R g)))
          ( equiv-tot
            ( λ h →
              extensionality-reflecting-map-equivalence-relation R X
                ( precomp-Set-Quotient R B f X h)
                ( g)))
          ( Uf X g))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  is-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-effective R q
  is-effective-is-image i T H x y =
    ( is-effective-class R x y) ∘e
    ( ( inv-equiv (equiv-ap-emb (emb-equivalence-class R))) ∘e
      ( ( inv-equiv (convert-eq-values T x y)) ∘e
        ( equiv-ap-emb i)))

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-surjective-and-effective R q
  pr1 (is-surjective-and-effective-is-image i T H) =
    is-surjective-is-image (prop-equivalence-relation R) i (pair q T) H
  pr2 (is-surjective-and-effective-is-image i T H) =
    is-effective-is-image i T H

  is-locally-small-is-surjective-and-effective :
    is-surjective-and-effective R q → is-locally-small l2 (type-Set B)
  is-locally-small-is-surjective-and-effective e x y =
    apply-twice-universal-property-trunc-Prop
      ( pr1 e x)
      ( pr1 e y)
      ( is-small-Prop l2 (x ＝ y))
      ( α)
    where
    α : fiber q x → fiber q y → is-small l2 (x ＝ y)
    pr1 (α (pair a refl) (pair b refl)) = sim-equivalence-relation R a b
    pr2 (α (pair a refl) (pair b refl)) = pr2 e a b

  large-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l3
  large-map-emb-is-surjective-and-effective H b a = Id-Prop B b (q a)

  small-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A →
    Σ (Prop l3) (λ P → is-small l2 (type-Prop P))
  pr1 (small-map-emb-is-surjective-and-effective H b a) =
    large-map-emb-is-surjective-and-effective H b a
  pr2 (small-map-emb-is-surjective-and-effective H b a) =
    is-locally-small-is-surjective-and-effective H b (q a)

  map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l2
  pr1 (map-emb-is-surjective-and-effective H b a) =
    pr1 (pr2 (small-map-emb-is-surjective-and-effective H b a))
  pr2 (map-emb-is-surjective-and-effective H b a) =
    is-prop-equiv'
      ( pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
      ( is-prop-type-Prop
        ( large-map-emb-is-surjective-and-effective H b a))

  compute-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) (b : type-Set B) (a : A) →
    type-Prop (large-map-emb-is-surjective-and-effective H b a) ≃
    type-Prop (map-emb-is-surjective-and-effective H b a)
  compute-map-emb-is-surjective-and-effective H b a =
    pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a))

  triangle-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    prop-equivalence-relation R ~ (map-emb-is-surjective-and-effective H ∘ q)
  triangle-emb-is-surjective-and-effective H a =
    eq-htpy
      ( λ x →
        eq-equiv-Prop
          ( ( compute-map-emb-is-surjective-and-effective H (q a) x) ∘e
            ( inv-equiv (pr2 H a x))))

  is-emb-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    is-emb (map-emb-is-surjective-and-effective H)
  is-emb-map-emb-is-surjective-and-effective H =
    is-emb-is-injective
      ( is-set-function-type is-set-type-Prop)
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 H y)
          ( Id-Prop B x y)
          ( α p))
    where
    α :
      {x y : type-Set B}
      (p :
        ( map-emb-is-surjective-and-effective H x) ＝
        ( map-emb-is-surjective-and-effective H y)) →
      fiber q y →
      type-Prop (Id-Prop B x y)
    α {x} p (pair a refl) =
      map-inv-equiv
        ( ( inv-equiv
            ( pr2
              ( is-locally-small-is-surjective-and-effective
                H (q a) (q a)))) ∘e
          ( ( equiv-eq (ap pr1 (htpy-eq p a))) ∘e
            ( pr2
              ( is-locally-small-is-surjective-and-effective H x (q a)))))
        ( refl)

  emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    type-Set B ↪ (A → Prop l2)
  pr1 (emb-is-surjective-and-effective H) =
    map-emb-is-surjective-and-effective H
  pr2 (emb-is-surjective-and-effective H) =
    is-emb-map-emb-is-surjective-and-effective H

  is-emb-large-map-emb-is-surjective-and-effective :
    (e : is-surjective-and-effective R q) →
    is-emb (large-map-emb-is-surjective-and-effective e)
  is-emb-large-map-emb-is-surjective-and-effective e =
    is-emb-is-injective
      ( is-set-function-type is-set-type-Prop)
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( Id-Prop B x y)
          ( α p))
    where
    α :
      {x y : type-Set B}
      (p :
        ( large-map-emb-is-surjective-and-effective e x) ＝
        ( large-map-emb-is-surjective-and-effective e y)) →
      fiber q y →
      type-Prop (Id-Prop B x y)
    α p (pair a refl) = map-inv-equiv (equiv-eq (ap pr1 (htpy-eq p a))) refl

  large-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B ↪ (A → Prop l3)
  pr1 (large-emb-is-surjective-and-effective e) =
    large-map-emb-is-surjective-and-effective e
  pr2 (large-emb-is-surjective-and-effective e) =
    is-emb-large-map-emb-is-surjective-and-effective e

  is-image-is-surjective-and-effective :
    ( H : is-surjective-and-effective R q) →
    is-image
      ( prop-equivalence-relation R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
  is-image-is-surjective-and-effective H =
    is-image-is-surjective
      ( prop-equivalence-relation R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
      ( pr1 H)

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-surjective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective (map-reflecting-map-equivalence-relation R q)
  is-surjective-is-set-quotient q Q b =
    tr
      ( λ y →
        type-trunc-Prop (fiber (map-reflecting-map-equivalence-relation R q) y))
      ( htpy-eq
        ( ap pr1
          ( eq-is-contr
            ( universal-property-set-quotient-is-set-quotient R B q Q B q)
            { inclusion-im (map-reflecting-map-equivalence-relation R q) ∘ β ,
              δ}
            { id , refl-htpy}))
        ( b))
      ( pr2 (β b))
    where
    α :
      reflects-equivalence-relation R
        ( map-unit-im (map-reflecting-map-equivalence-relation R q))
    α {x} {y} r =
      is-injective-is-emb
        ( is-emb-inclusion-im (map-reflecting-map-equivalence-relation R q))
        ( map-equiv
          ( convert-eq-values
            ( triangle-unit-im (map-reflecting-map-equivalence-relation R q))
            ( x)
            ( y))
          ( reflects-map-reflecting-map-equivalence-relation R q r))
    β : type-Set B → im (map-reflecting-map-equivalence-relation R q)
    β = map-inv-is-equiv
        ( Q ( pair
              ( im (map-reflecting-map-equivalence-relation R q))
                ( is-set-im
                  ( map-reflecting-map-equivalence-relation R q)
                  ( is-set-type-Set B))))
          ( pair (map-unit-im (map-reflecting-map-equivalence-relation R q)) α)
    γ :
      ( β ∘ (map-reflecting-map-equivalence-relation R q)) ~
      ( map-unit-im (map-reflecting-map-equivalence-relation R q))
    γ =
      htpy-eq
        ( ap
            ( pr1)
            ( is-section-map-inv-is-equiv
              ( Q ( pair
                    ( im (map-reflecting-map-equivalence-relation R q))
                    ( is-set-im
                      ( map-reflecting-map-equivalence-relation R q)
                      ( is-set-type-Set B))))
              ( map-unit-im (map-reflecting-map-equivalence-relation R q) , α)))
    δ :
      ( ( inclusion-im (map-reflecting-map-equivalence-relation R q) ∘ β) ∘
        ( map-reflecting-map-equivalence-relation R q)) ~
      ( map-reflecting-map-equivalence-relation R q)
    δ =
      ( inclusion-im (map-reflecting-map-equivalence-relation R q) ·l γ) ∙h
      ( triangle-unit-im (map-reflecting-map-equivalence-relation R q))

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-effective R (map-reflecting-map-equivalence-relation R q)
  is-effective-is-set-quotient q Q x y =
    inv-equiv (compute-P y) ∘e δ (map-reflecting-map-equivalence-relation R q y)
    where
    α : Σ (A → Prop l2) (reflects-equivalence-relation R)
    α = pair
        ( prop-equivalence-relation R x)
        ( λ r →
          eq-iff
            ( transitive-equivalence-relation R _ _ _ r)
            ( transitive-equivalence-relation R _ _ _
              ( symmetric-equivalence-relation R _ _ r)))
    P : type-Set B → Prop l2
    P = map-inv-is-equiv (Q (Prop-Set l2)) α
    compute-P :
      (a : A) →
      sim-equivalence-relation R x a ≃
      type-Prop (P (map-reflecting-map-equivalence-relation R q a))
    compute-P a =
      equiv-eq
        ( ap pr1
          ( htpy-eq
            ( ap pr1
              ( inv (is-section-map-inv-is-equiv (Q (Prop-Set l2)) α)))
            ( a)))
    point-P : type-Prop (P (map-reflecting-map-equivalence-relation R q x))
    point-P = map-equiv (compute-P x) (refl-equivalence-relation R x)
    center-total-P : Σ (type-Set B) (λ b → type-Prop (P b))
    center-total-P =
      pair (map-reflecting-map-equivalence-relation R q x) point-P
    contraction-total-P :
      (u : Σ (type-Set B) (λ b → type-Prop (P b))) → center-total-P ＝ u
    contraction-total-P (pair b p) =
      eq-type-subtype P
        ( apply-universal-property-trunc-Prop
          ( is-surjective-is-set-quotient R B q Q b)
          ( Id-Prop B (map-reflecting-map-equivalence-relation R q x) b)
          ( λ v →
            ( reflects-map-reflecting-map-equivalence-relation R q
              ( map-inv-equiv
                ( compute-P (pr1 v))
                ( inv-tr (type-Prop ∘ P) (pr2 v) p))) ∙
            ( pr2 v)))
    is-torsorial-P : is-torsorial (λ b → type-Prop (P b))
    is-torsorial-P = pair center-total-P contraction-total-P
    β :
      (b : type-Set B) →
      map-reflecting-map-equivalence-relation R q x ＝ b → type-Prop (P b)
    β .(map-reflecting-map-equivalence-relation R q x) refl = point-P
    γ : (b : type-Set B) → is-equiv (β b)
    γ = fundamental-theorem-id is-torsorial-P β
    δ :
      (b : type-Set B) →
      (map-reflecting-map-equivalence-relation R q x ＝ b) ≃ type-Prop (P b)
    δ b = pair (β b) (γ b)

  apply-effectiveness-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} →
    ( map-reflecting-map-equivalence-relation R q x ＝
      map-reflecting-map-equivalence-relation R q y) →
    sim-equivalence-relation R x y
  apply-effectiveness-is-set-quotient q H {x} {y} =
    map-equiv (is-effective-is-set-quotient q H x y)

  apply-effectiveness-is-set-quotient' :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} → sim-equivalence-relation R x y →
    map-reflecting-map-equivalence-relation R q x ＝
    map-reflecting-map-equivalence-relation R q y
  apply-effectiveness-is-set-quotient' q H {x} {y} =
    map-inv-equiv (is-effective-is-set-quotient q H x y)

  is-surjective-and-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective-and-effective R (map-reflecting-map-equivalence-relation R q)
  pr1 (is-surjective-and-effective-is-set-quotient q Q) =
    is-surjective-is-set-quotient R B q Q
  pr2 (is-surjective-and-effective-is-set-quotient q Q) =
    is-effective-is-set-quotient q Q

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set B))
  where

  private
    module _
      ( E :
        is-surjective-and-effective R
          ( map-reflecting-map-equivalence-relation R q))
      { l : Level}
      ( X : Set l)
      ( f : reflecting-map-equivalence-relation R (type-Set X))
      where

      P-Prop : (b : type-Set B) (x : type-Set X) → Prop (l1 ⊔ l3 ⊔ l)
      P-Prop b x =
        exists-structure-Prop A
          ( λ a →
            ( map-reflecting-map-equivalence-relation R f a ＝ x) ×
            ( map-reflecting-map-equivalence-relation R q a ＝ b))

      P : (b : type-Set B) (x : type-Set X) → UU (l1 ⊔ l3 ⊔ l)
      P b x = type-Prop (P-Prop b x)

      all-elements-equal-total-P :
        (b : type-Set B) → all-elements-equal (Σ (type-Set X) (P b))
      all-elements-equal-total-P b x y =
        eq-type-subtype
          ( P-Prop b)
          ( apply-twice-universal-property-trunc-Prop
            ( pr2 x)
            ( pr2 y)
            ( Id-Prop X (pr1 x) (pr1 y))
            ( λ u v →
              ( inv (pr1 (pr2 u))) ∙
              ( ( pr2 f
                  ( map-equiv
                    ( pr2 E (pr1 u) (pr1 v))
                    ( (pr2 (pr2 u)) ∙ (inv (pr2 (pr2 v)))))) ∙
                ( pr1 (pr2 v)))))

      is-prop-total-P : (b : type-Set B) → is-prop (Σ (type-Set X) (P b))
      is-prop-total-P b =
        is-prop-all-elements-equal (all-elements-equal-total-P b)

      α : (b : type-Set B) → Σ (type-Set X) (P b)
      α =
        map-inv-is-equiv
          ( dependent-universal-property-surjection-is-surjective
            ( map-reflecting-map-equivalence-relation R q)
            ( pr1 E)
            ( λ b →
              pair
                ( Σ (type-Set X) (P b))
                ( is-prop-total-P b)))
          ( λ a → pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl))))

      β :
        (a : A) →
        ( α (map-reflecting-map-equivalence-relation R q a)) ＝
        ( pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl))))
      β = htpy-eq
            ( is-section-map-inv-is-equiv
              ( dependent-universal-property-surjection-is-surjective
                ( map-reflecting-map-equivalence-relation R q)
                ( pr1 E)
                ( λ b → pair (Σ (type-Set X) (P b)) (is-prop-total-P b)))
              ( λ a →
                pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl)))))

  is-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    is-set-quotient R B q
  is-set-quotient-is-surjective-and-effective E X =
    is-equiv-is-contr-map
      ( λ f →
        is-proof-irrelevant-is-prop
        ( is-prop-equiv
          ( equiv-tot
            ( λ _ →
              equiv-ap-inclusion-subtype
                ( reflects-prop-equivalence-relation R X)))
          ( is-prop-map-is-emb
            ( is-epimorphism-is-surjective-Set (pr1 E) X)
            ( pr1 f)))
        ( pair
          ( λ b → pr1 (α E X f b))
          ( eq-type-subtype
            ( reflects-prop-equivalence-relation R X)
            ( eq-htpy (λ a → ap pr1 (β E X f a))))))

  universal-property-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    universal-property-set-quotient R B q
  universal-property-set-quotient-is-surjective-and-effective E =
    universal-property-set-quotient-is-set-quotient R B q
      ( is-set-quotient-is-surjective-and-effective E)

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  quotient-reflecting-map-equivalence-class :
    reflecting-map-equivalence-relation R (equivalence-class R)
  pr1 quotient-reflecting-map-equivalence-class =
    class R
  pr2 quotient-reflecting-map-equivalence-class =
    apply-effectiveness-class' R

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-surjective-and-effective-class :
    is-surjective-and-effective R (class R)
  pr1 is-surjective-and-effective-class =
    is-surjective-class R
  pr2 is-surjective-and-effective-class =
    is-effective-class R

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  universal-property-equivalence-class :
    universal-property-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  universal-property-equivalence-class =
    universal-property-set-quotient-is-surjective-and-effective R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
      ( is-surjective-and-effective-class R)

  is-set-quotient-equivalence-class :
    is-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  is-set-quotient-equivalence-class =
    is-set-quotient-universal-property-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
      ( universal-property-equivalence-class)

  map-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    equivalence-class R → type-Set C
  map-universal-property-equivalence-class C g =
    pr1 (center (universal-property-equivalence-class C g))

  triangle-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-equivalence-class C g) ∘
      ( class R)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-equivalence-class C g =
    pr2 (center (universal-property-equivalence-class C g))
```

## Corollary 18.2.4

Consider an equivalence relation `R` over a type `A`.
Then the quotient map

```text
  q : A → A/R
```

is surjective and effective, and it satisfies the universal property of the set quotient.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  abstract
    is-effective-quotient-map : is-effective R (quotient-map R)
    is-effective-quotient-map x y =
      equivalence-reasoning
        ( quotient-map R x ＝ quotient-map R y)
        ≃ ( equivalence-class-set-quotient R (quotient-map R x) ＝
            equivalence-class-set-quotient R (quotient-map R y))
          by equiv-ap-emb (emb-equivalence-class-set-quotient R)
        ≃ ( class R x ＝ equivalence-class-set-quotient R (quotient-map R y))
          by
          ( equiv-concat
            ( inv ( is-retraction-equivalence-class-set-quotient R (class R x)))
            ( equivalence-class-set-quotient R (quotient-map R y)))
        ≃ ( class R x ＝ class R y)
          by
          ( equiv-concat'
            ( class R x)
            ( is-retraction-equivalence-class-set-quotient R (class R y)))
        ≃ ( sim-equivalence-relation R x y)
          by
          ( is-effective-class R x y)

  apply-effectiveness-quotient-map :
    {x y : A} → quotient-map R x ＝ quotient-map R y →
    sim-equivalence-relation R x y
  apply-effectiveness-quotient-map {x} {y} =
    map-equiv (is-effective-quotient-map x y)

  apply-effectiveness-quotient-map' :
    {x y : A} → sim-equivalence-relation R x y →
    quotient-map R x ＝ quotient-map R y
  apply-effectiveness-quotient-map' {x} {y} =
    map-inv-equiv (is-effective-quotient-map x y)

  is-surjective-and-effective-quotient-map :
    is-surjective-and-effective R (quotient-map R)
  pr1 is-surjective-and-effective-quotient-map = is-surjective-quotient-map R
  pr2 is-surjective-and-effective-quotient-map = is-effective-quotient-map

  reflecting-map-quotient-map :
    reflecting-map-equivalence-relation R (set-quotient R)
  pr1 reflecting-map-quotient-map = quotient-map R
  pr2 reflecting-map-quotient-map = apply-effectiveness-quotient-map'

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-set-quotient-set-quotient :
    is-set-quotient R (quotient-Set R) (reflecting-map-quotient-map R)
  is-set-quotient-set-quotient =
    is-set-quotient-is-surjective-and-effective R
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( is-surjective-and-effective-quotient-map R)

  inv-precomp-set-quotient :
    {l : Level} (X : Set l) →
    reflecting-map-equivalence-relation R (type-Set X) →
    hom-Set (quotient-Set R) X
  inv-precomp-set-quotient X =
    pr1 (pr1 (is-set-quotient-set-quotient X))

  abstract
    is-section-inv-precomp-set-quotient :
      {l : Level} (X : Set l) →
      (f : reflecting-map-equivalence-relation R (type-Set X)) →
      (a : A) →
      inv-precomp-set-quotient X f (quotient-map R a) ＝
        map-reflecting-map-equivalence-relation R f a
    is-section-inv-precomp-set-quotient X f =
      htpy-eq
        ( ap
          ( map-reflecting-map-equivalence-relation R)
          ( is-section-map-inv-is-equiv
            ( is-set-quotient-set-quotient X)
            ( f)))

    is-retraction-inv-precomp-set-quotient :
      {l : Level} (X : Set l) (f : hom-Set (quotient-Set R) X) →
      inv-precomp-set-quotient X
        ( precomp-Set-Quotient R
          ( quotient-Set R)
          ( reflecting-map-quotient-map R)
          ( X)
          ( f)) ＝
      f
    is-retraction-inv-precomp-set-quotient X f =
      is-retraction-map-inv-is-equiv (is-set-quotient-set-quotient X) f
```

Theorem 18.2.3 can be used to show that the type of equivalence relations is equivalent to the type of sets `X` equipped with a surjective map `A ↠ X`.
This may seem remarkable if you haven’t tried Exercise 17.18 yet, because at first glance one might think that the type of sets `X` equipped with a surjective map `A ↠ X` is a `1`-type, while the type of equivalence relations on `A` is a set.

## Theorem 18.2.5

For any type `A` and any universe `𝒰` containing `A`, we have an equivalence

```text
  Eq-Rel_𝒰(A) ≃ Σ(X : Set_𝒰) A ↠ X.
```

### Proof

Given an equivalence relation `R : A → (A → Prop_𝒰)` on `A` we first use the replacement axiom, by which the set quotient `A/R` is `𝒰`-small, to obtain a set `Q(R) : Set_𝒰`, an equivalence `e : Q(R) ≃ A/R`, and a surjective map `f : A → Q(R)` such that the triangle

_Triangle-shaped diagram (automatic draft)._

```text
           A
          / \
         /   \
      f /     \ q
       /       \
      ∨         ∨
  Q(R) --------> A/R
           e
```

commutes.
This defines a map

```text
  Q_A : Eq-Rel_𝒰(A) → Σ(X : Set_𝒰) A ↠ X.
```

The map `K_A : (Σ(X : Set_𝒰) A ↠ X) → Eq-Rel_𝒰(A)` is given by

```text
  K_A(X,f,x,y) ≔ K_f(x,y) ≔ (f(x) = f(y)).
```

Note that `K_f` is valued in propositions because `X` is assumed to be a set, and obviously it is an equivalence relation.

To see that `K_A(Q_A(R)) = R` note that by function extensionality and propositional extensionality it follows that two equivalence relations `R` and `S` on `A` are equal if and only if `R(x,y) ↔ S(x,y)` for all `x, y : A`.
Note that `K_A(Q_A(R))(x,y) ↔ R(x,y)` holds for all `x, y : A` if and only if `(q_R(x) = q_R(y)) ↔ R(x,y)` holds for all `x, y : A`.
This follows from Corollary 18.1.4.

It remains to show that `Q_A(K_A(X,f)) = (X,f)`.
Note that the type of identifications `(Y,g) = (X,f)` is by the univalence axiom equivalent to the type

```text
  Σ(e : Y ≃ X) e ∘ g ~ f.
```

Therefore it suffices to construct a commuting triangle

```text
             A
            / \
           /   \
  q_{K_f} /     \ f
         /       \
        ∨         ∨
   A/K_f --------> X
```

We obtain such an equivalence by combining Theorem 18.2.3 and Theorem 15.1.8. ◻

```agda
Surjection : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection l2 A = Σ (UU l2) (A ↠_)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  type-Surjection : UU l2
  type-Surjection = pr1 f

  surjection-Surjection : A ↠ type-Surjection
  surjection-Surjection = pr2 f

  map-Surjection : A → type-Surjection
  map-Surjection = map-surjection surjection-Surjection

  is-surjective-map-Surjection : is-surjective map-Surjection
  is-surjective-map-Surjection =
    is-surjective-map-surjection surjection-Surjection

emb-type-Truncated-Type : (l : Level) (k : 𝕋) → Truncated-Type l k ↪ UU l
emb-type-Truncated-Type l k = emb-subtype (is-trunc-Prop k)

Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Truncated-Type l2 k A =
  Σ (Truncated-Type l2 k) (λ X → A ↠ type-Truncated-Type X)

emb-inclusion-Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) →
  Surjection-Into-Truncated-Type l2 k A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Truncated-Type l2 k A =
  emb-Σ (λ X → A ↠ X) (emb-type-Truncated-Type l2 k) (λ X → id-emb)

inclusion-Surjection-Into-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A → Surjection l2 A
inclusion-Surjection-Into-Truncated-Type {l1} {l2} {k} {A} =
  map-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  truncated-type-Surjection-Into-Truncated-Type : Truncated-Type l2 k
  truncated-type-Surjection-Into-Truncated-Type = pr1 f

  type-Surjection-Into-Truncated-Type : UU l2
  type-Surjection-Into-Truncated-Type =
    type-Truncated-Type truncated-type-Surjection-Into-Truncated-Type

  is-trunc-type-Surjection-Into-Truncated-Type :
    is-trunc k type-Surjection-Into-Truncated-Type
  is-trunc-type-Surjection-Into-Truncated-Type =
    is-trunc-type-Truncated-Type
      truncated-type-Surjection-Into-Truncated-Type

  surjection-Surjection-Into-Truncated-Type :
    A ↠ type-Surjection-Into-Truncated-Type
  surjection-Surjection-Into-Truncated-Type = pr2 f

  map-Surjection-Into-Truncated-Type :
    A → type-Surjection-Into-Truncated-Type
  map-Surjection-Into-Truncated-Type =
    map-surjection surjection-Surjection-Into-Truncated-Type

  is-surjective-Surjection-Into-Truncated-Type :
    is-surjective map-Surjection-Into-Truncated-Type
  is-surjective-Surjection-Into-Truncated-Type =
    is-surjective-map-surjection surjection-Surjection-Into-Truncated-Type

Surjection-Into-Set :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Set l2 A = Surjection-Into-Truncated-Type l2 zero-𝕋 A

emb-inclusion-Surjection-Into-Set :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  Surjection-Into-Set l2 A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Set l2 A =
  emb-inclusion-Surjection-Into-Truncated-Type l2 zero-𝕋 A

inclusion-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → Surjection l2 A
inclusion-Surjection-Into-Set {l1} {l2} {A} =
  inclusion-Surjection-Into-Truncated-Type

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A)
  where

  set-Surjection-Into-Set : Set l2
  set-Surjection-Into-Set = truncated-type-Surjection-Into-Truncated-Type f

  type-Surjection-Into-Set : UU l2
  type-Surjection-Into-Set = type-Surjection-Into-Truncated-Type f

  is-set-type-Surjection-Into-Set : is-set type-Surjection-Into-Set
  is-set-type-Surjection-Into-Set =
    is-trunc-type-Surjection-Into-Truncated-Type f

  surjection-Surjection-Into-Set : A ↠ type-Surjection-Into-Set
  surjection-Surjection-Into-Set = surjection-Surjection-Into-Truncated-Type f

  map-Surjection-Into-Set : A → type-Surjection-Into-Set
  map-Surjection-Into-Set = map-Surjection-Into-Truncated-Type f

  is-surjective-Surjection-Into-Set : is-surjective map-Surjection-Into-Set
  is-surjective-Surjection-Into-Set =
    is-surjective-Surjection-Into-Truncated-Type f

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  surjection-into-set-equivalence-relation :
    Surjection-Into-Set (l1 ⊔ l2) A
  pr1 surjection-into-set-equivalence-relation = quotient-Set R
  pr2 surjection-into-set-equivalence-relation = surjection-quotient-map R

module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  rel-map-into-set : Relation-Prop l2 A
  rel-map-into-set x y = Id-Prop X (f x) (f y)

  sim-map-into-set : Relation l2 A
  sim-map-into-set x y = type-Prop (rel-map-into-set x y)

  refl-sim-map-into-set : is-reflexive sim-map-into-set
  refl-sim-map-into-set x = refl

  symmetric-sim-map-into-set : is-symmetric sim-map-into-set
  symmetric-sim-map-into-set x y H = inv H

  transitive-sim-map-into-set : is-transitive sim-map-into-set
  transitive-sim-map-into-set x y z H K = K ∙ H

  equivalence-relation-map-into-set : equivalence-relation l2 A
  pr1 equivalence-relation-map-into-set = rel-map-into-set
  pr1 (pr2 equivalence-relation-map-into-set) x = refl-sim-map-into-set x
  pr1 (pr2 (pr2 equivalence-relation-map-into-set)) x y =
    symmetric-sim-map-into-set x y
  pr2 (pr2 (pr2 equivalence-relation-map-into-set)) x y z =
    transitive-sim-map-into-set x y z

  is-effective-map-into-set :
    is-effective equivalence-relation-map-into-set f
  is-effective-map-into-set x y = id-equiv

equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → equivalence-relation l2 A
equivalence-relation-Surjection-Into-Set f =
  equivalence-relation-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)

is-effective-map-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  is-effective
    ( equivalence-relation-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
is-effective-map-Surjection-Into-Set f =
  is-effective-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set
        ( surjection-into-set-equivalence-relation R))
      ( R)
  relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation
    x y =
    iff-equiv (is-effective-quotient-map R x y)

is-retraction-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation (l1 ⊔ l2) A) →
  equivalence-relation-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation R) ＝
  R
is-retraction-equivalence-relation-Surjection-Into-Set R =
  eq-relate-same-elements-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set
      ( surjection-into-set-equivalence-relation R))
    ( R)
    ( relate-same-elements-equivalence-relation-surjection-into-set-equivalence-relation
      R)

equiv-Surjection :
  {l1 l2 l3 : Level} {A : UU l1} →
  Surjection l2 A → Surjection l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection f g =
  Σ ( type-Surjection f ≃ type-Surjection g)
    ( λ e → map-equiv e ∘ map-Surjection f ~ map-Surjection g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  id-equiv-Surjection : equiv-Surjection f f
  pr1 id-equiv-Surjection = id-equiv
  pr2 id-equiv-Surjection = refl-htpy

  is-torsorial-equiv-Surjection :
    is-torsorial (equiv-Surjection f)
  is-torsorial-equiv-Surjection =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Surjection f))
      ( type-Surjection f , id-equiv)
      ( is-torsorial-htpy-surjection (surjection-Surjection f))

  equiv-eq-Surjection :
    (g : Surjection l2 A) → (f ＝ g) → equiv-Surjection f g
  equiv-eq-Surjection .f refl = id-equiv-Surjection

  is-equiv-equiv-eq-Surjection :
    (g : Surjection l2 A) → is-equiv (equiv-eq-Surjection g)
  is-equiv-equiv-eq-Surjection =
    fundamental-theorem-id
      is-torsorial-equiv-Surjection
      equiv-eq-Surjection

  extensionality-Surjection :
    (g : Surjection l2 A) → (f ＝ g) ≃ equiv-Surjection f g
  pr1 (extensionality-Surjection g) = equiv-eq-Surjection g
  pr2 (extensionality-Surjection g) = is-equiv-equiv-eq-Surjection g

  eq-equiv-Surjection :
    (g : Surjection l2 A) → equiv-Surjection f g → f ＝ g
  eq-equiv-Surjection g = map-inv-equiv (extensionality-Surjection g)

equiv-Surjection-Into-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A →
  Surjection-Into-Truncated-Type l3 k A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Truncated-Type f g =
  equiv-Surjection
    ( inclusion-Surjection-Into-Truncated-Type f)
    ( inclusion-Surjection-Into-Truncated-Type g)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  id-equiv-Surjection-Into-Truncated-Type :
    equiv-Surjection-Into-Truncated-Type f f
  id-equiv-Surjection-Into-Truncated-Type =
    id-equiv-Surjection (inclusion-Surjection-Into-Truncated-Type f)

  extensionality-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) ≃ equiv-Surjection-Into-Truncated-Type f g
  extensionality-Surjection-Into-Truncated-Type g =
    ( extensionality-Surjection
      ( inclusion-Surjection-Into-Truncated-Type f)
      ( inclusion-Surjection-Into-Truncated-Type g)) ∘e
    ( equiv-ap-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A))

  equiv-eq-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) → equiv-Surjection-Into-Truncated-Type f g
  equiv-eq-Surjection-Into-Truncated-Type g =
    map-equiv (extensionality-Surjection-Into-Truncated-Type g)

  refl-equiv-eq-Surjection-Into-Truncated-Type :
    equiv-eq-Surjection-Into-Truncated-Type f refl ＝
    id-equiv-Surjection-Into-Truncated-Type
  refl-equiv-eq-Surjection-Into-Truncated-Type = refl

  eq-equiv-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    equiv-Surjection-Into-Truncated-Type f g → f ＝ g
  eq-equiv-Surjection-Into-Truncated-Type g =
    map-inv-equiv (extensionality-Surjection-Into-Truncated-Type g)

equiv-Surjection-Into-Set :
  {l1 l2 l3 : Level} {A : UU l1} → Surjection-Into-Set l2 A →
  Surjection-Into-Set l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Set = equiv-Surjection-Into-Truncated-Type

id-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f f
id-equiv-Surjection-Into-Set = id-equiv-Surjection-Into-Truncated-Type

extensionality-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) ≃ equiv-Surjection-Into-Set f g
extensionality-Surjection-Into-Set =
  extensionality-Surjection-Into-Truncated-Type

equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) → equiv-Surjection-Into-Set f g
equiv-eq-Surjection-Into-Set = equiv-eq-Surjection-Into-Truncated-Type

refl-equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-eq-Surjection-Into-Set f f refl ＝
  id-equiv-Surjection-Into-Set f
refl-equiv-eq-Surjection-Into-Set = refl-equiv-eq-Surjection-Into-Truncated-Type

eq-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f g → f ＝ g
eq-equiv-Surjection-Into-Set = eq-equiv-Surjection-Into-Truncated-Type

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-id-Set-Quotient : precomp-Set-Quotient R B f B id ＝ f
  precomp-id-Set-Quotient =
    eq-htpy-reflecting-map-equivalence-relation R B
      ( precomp-Set-Quotient R B f B id)
      ( f)
      ( refl-htpy)

precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : hom-Set B C)
  (D : Set l5) (h : hom-Set C D) →
  ( precomp-Set-Quotient R B f D (h ∘ g)) ＝
  ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-equivalence-relation R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  {h : type-Set B → type-Set C}
  (H :
    (h ∘ map-reflecting-map-equivalence-relation R f) ~
    map-reflecting-map-equivalence-relation R g)
  where

  map-inv-is-equiv-is-set-quotient-is-set-quotient :
    is-set-quotient R B f →
    is-set-quotient R C g →
    type-Set C → type-Set B
  map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    map-universal-property-set-quotient-is-set-quotient R C g Ug B f

  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : is-set-quotient R B f) →
    ( Ug : is-set-quotient R C g) →
    ( h ∘ map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug) ~ id
  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    htpy-eq
      ( is-injective-is-equiv
      ( Ug C)
      { h ∘ map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug}
      { id}
      ( ( precomp-comp-Set-Quotient R C g B
          ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
          ( C)
          ( h)) ∙
        ( ( ap
            ( λ t → precomp-Set-Quotient R B t C h)
            ( eq-htpy-reflecting-map-equivalence-relation R B
              ( precomp-Set-Quotient R C g B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
              ( f)
              ( triangle-universal-property-set-quotient-is-set-quotient
                R C g Ug B f))) ∙
          ( ( eq-htpy-reflecting-map-equivalence-relation R C
              ( precomp-Set-Quotient R B f C h) g H) ∙
            ( inv (precomp-id-Set-Quotient R C g))))))

  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : is-set-quotient R B f) →
    ( Ug : is-set-quotient R C g) →
    ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug ∘ h) ~ id
  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    htpy-eq
      ( is-injective-is-equiv
      ( Uf B)
      { map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug ∘ h}
      { id}
      ( ( precomp-comp-Set-Quotient R B f C h B
          ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)) ∙
        ( ( ap
            ( λ t →
              precomp-Set-Quotient R C t B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
            ( eq-htpy-reflecting-map-equivalence-relation R C
              ( precomp-Set-Quotient R B f C h)
              ( g)
              ( H))) ∙
          ( ( eq-htpy-reflecting-map-equivalence-relation R B
              ( precomp-Set-Quotient R C g B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
              ( f)
              ( triangle-universal-property-set-quotient-is-set-quotient
                R C g Ug B f)) ∙
            ( inv (precomp-id-Set-Quotient R B f))))))

  is-equiv-is-set-quotient-is-set-quotient :
    is-set-quotient R B f →
    is-set-quotient R C g →
    is-equiv h
  is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    is-equiv-is-invertible
      ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
      ( is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
      ( is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)

  is-set-quotient-is-set-quotient-is-equiv :
    is-equiv h → is-set-quotient R B f → is-set-quotient R C g
  is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
    is-equiv-left-map-triangle
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-equivalence-relation R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( is-equiv-precomp-is-equiv h E (type-Set X))
      ( Uf X)

  is-set-quotient-is-equiv-is-set-quotient :
    is-set-quotient R C g → is-equiv h → is-set-quotient R B f
  is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
    is-equiv-right-map-triangle
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-equivalence-relation R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( Ug X)
      ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (Uf : is-set-quotient R B f)
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  (Ug : is-set-quotient R C g)
  where

  uniqueness-set-quotient :
    is-contr
      ( Σ ( type-Set B ≃ type-Set C)
          ( λ e →
            ( map-equiv e ∘ map-reflecting-map-equivalence-relation R f) ~
            ( map-reflecting-map-equivalence-relation R g)))
  uniqueness-set-quotient =
    is-torsorial-Eq-subtype
      ( universal-property-set-quotient-is-set-quotient R B f Uf C g)
      ( is-property-is-equiv)
      ( map-universal-property-set-quotient-is-set-quotient R B f Uf C g)
      ( triangle-universal-property-set-quotient-is-set-quotient R B f Uf C g)
      ( is-equiv-is-set-quotient-is-set-quotient R B f C g
        ( triangle-universal-property-set-quotient-is-set-quotient
          R B f Uf C g)
        ( Uf)
        ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient = map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘
      map-reflecting-map-equivalence-relation R f) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)

equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set f))
    ( f)
equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set f =
  center
    ( uniqueness-set-quotient
      ( equivalence-relation-Surjection-Into-Set f)
      ( quotient-Set (equivalence-relation-Surjection-Into-Set f))
      ( reflecting-map-quotient-map
        ( equivalence-relation-Surjection-Into-Set f))
      ( is-set-quotient-set-quotient
        ( equivalence-relation-Surjection-Into-Set f))
      ( set-Surjection-Into-Set f)
      ( pair
        ( map-Surjection-Into-Set f)
        ( λ H → H))
      ( is-set-quotient-is-surjective-and-effective
        ( equivalence-relation-Surjection-Into-Set f)
        ( set-Surjection-Into-Set f)
        ( pr1 (pr2 f) , (λ {x} {y} z → z))
        ( pair
          ( is-surjective-Surjection-Into-Set f)
          ( is-effective-map-Surjection-Into-Set f))))

is-section-equivalence-relation-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set (l1 ⊔ l2) A) →
  surjection-into-set-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set f) ＝
  f
is-section-equivalence-relation-Surjection-Into-Set f =
  eq-equiv-Surjection-Into-Set
    ( surjection-into-set-equivalence-relation
      ( equivalence-relation-Surjection-Into-Set f))
    ( f)
    ( equiv-surjection-into-set-equivalence-relation-Surjection-Into-Set f)

is-equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} {A : UU l1} →
  is-equiv (surjection-into-set-equivalence-relation {l1} {l1} {A})
is-equiv-surjection-into-set-equivalence-relation {l1} {A} =
  is-equiv-is-invertible
    ( equivalence-relation-Surjection-Into-Set {l1} {l1} {A})
    ( is-section-equivalence-relation-Surjection-Into-Set {l1} {l1} {A})
    ( is-retraction-equivalence-relation-Surjection-Into-Set {l1} {l1} {A})

equiv-surjection-into-set-equivalence-relation :
  {l1 : Level} (A : UU l1) →
  equivalence-relation l1 A ≃ Surjection-Into-Set l1 A
pr1 (equiv-surjection-into-set-equivalence-relation A) =
  surjection-into-set-equivalence-relation
pr2 (equiv-surjection-into-set-equivalence-relation A) =
  is-equiv-surjection-into-set-equivalence-relation
```

## Supplement

### Any map into a set reflects mere equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  reflects-mere-eq :
    reflects-equivalence-relation (mere-eq-equivalence-relation A) f
  reflects-mere-eq {x} {y} r =
    apply-universal-property-trunc-Prop r
      ( Id-Prop X (f x) (f y))
      ( ap f)

  reflecting-map-mere-eq :
    reflecting-map-equivalence-relation
      ( mere-eq-equivalence-relation A)
      ( type-Set X)
  reflecting-map-mere-eq = (f , reflects-mere-eq)
```
