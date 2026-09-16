# Section 12.1 Propositions

```agda
module section-12-1-propositions where

open import universe-levels
open import section-2-2-ordinary-function-types
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-4-6-dependent-pair-types
open import section-5-1-the-inductive-definition-of-identity-types
open import section-5-2-the-groupoidal-structure-of-types
open import section-5-3-the-action-on-identifications-of-functions
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-11-4-embeddings
open import exercise-4-3-double-negation-logic
open import exercise-10-1-identity-types-contractible
open import exercise-10-3-contractible-equivalences
```

## Definition 12.1.1

A type `A` is said to be a **proposition** if its identity types are contractible, i.e., if it comes equipped with a term of type

```text
  is-prop(A) ≔ Π(x, y : A) is-contr(x = y).
```

Given a universe `𝒰`, we define `Prop_𝒰` to be the type of all small propositions, i.e.,

```text
  Prop_𝒰 ≔ Σ(X : 𝒰) is-prop(X).
```

```agda
is-prop : {l : Level} (A : UU l) → UU l
is-prop A = (x y : A) → is-contr (x ＝ y)

Prop :
  (l : Level) → UU (lsuc l)
Prop l = Σ (UU l) is-prop

module _
  {l : Level} (P : Prop l)
  where

  type-Prop : UU l
  type-Prop = pr1 P

  abstract
    is-prop-type-Prop : is-prop type-Prop
    is-prop-type-Prop = pr2 P
```

## Example 12.1.2

Any contractible type is a proposition by Exercise 10.1.
In particular, the unit type is a proposition.

```agda
abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : Prop lzero
unit-Prop = unit , is-prop-unit
```

The empty type is also a proposition, since we have

```text
  Π(x, y : empty) is-contr(x = y)
```

by the induction principle of the empty type.

```agda
abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty
```

There are many conditions on a type `A` that are equivalent to the condition that `A` is a proposition.
In the following proposition we state four such conditions.

## Proposition 12.1.3

Let `A` be a type.
Then the following are equivalent:

1. The type `A` is a proposition.

2. Any two terms of type `A` can be identified, i.e., there is a dependent function of type

   ```text
     is-prop'(A) ≔ Π(x, y : A) x = y.
   ```

3. The type `A` is contractible as soon as it is inhabited, i.e., there is a function of type

   ```text
     A → is-contr(A).
   ```

4. The map `const_⋆ : A → unit` is an embedding.

### Proof

If `A` is a proposition, then we can use the center of contraction of the identity types of `A` to identify any two terms in `A`.
This shows that (i) implies (ii).

To show that (ii) implies (iii), suppose that `A` comes equipped with `p : Π(x, y : A) x = y`.
Then for any `x : A` the dependent function `p(x) : Π(y : A) x = y` is a contraction of `A`.
Thus we obtain the function

```text
λ x. (x,p(x)) : A → is-contr(A).
```

To show that (iii) implies (iv), suppose that `A → is-contr(A)`.
We first make the simple observation that

```text
  (X → is-emb(f)) → is-emb(f)
```

for any map `f : X → Y`, so it suffices to show that `A → is-emb(const_⋆)`.
However, assuming we have `x : A`, it follows by assumption that `A` is contractible.
Therefore, it follows by Exercise 10.3 that the map `const_⋆ : A → unit` is an equivalence, and any equivalence is an embedding by Theorem 11.4.2.

To show that (iv) implies (i), note that if `A → unit` is an embedding, then the identity types of `A` are equivalent to contractible types and therefore they must be contractible. ◻

```agda
module _
  {l : Level} (A : UU l)
  where

  all-elements-equal : UU l
  all-elements-equal = (x y : A) → x ＝ y

  is-proof-irrelevant : UU l
  is-proof-irrelevant = A → is-contr A

  is-subterminal : UU l
  is-subterminal = is-emb (λ (_ : A) → star)

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → x ＝ y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant = eq-is-prop' ∘ is-prop-is-proof-irrelevant

  abstract
    is-subterminal-is-proof-irrelevant :
      is-proof-irrelevant A → is-subterminal A
    is-subterminal-is-proof-irrelevant H =
      is-emb-is-emb
        ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

  abstract
    is-subterminal-all-elements-equal : all-elements-equal A → is-subterminal A
    is-subterminal-all-elements-equal =
      is-subterminal-is-proof-irrelevant ∘
      is-proof-irrelevant-all-elements-equal

  abstract
    is-subterminal-is-prop : is-prop A → is-subterminal A
    is-subterminal-is-prop = is-subterminal-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-subterminal : is-subterminal A → is-prop A
    is-prop-is-subterminal H x y =
      is-contr-is-equiv
        ( star ＝ star)
        ( ap (λ (_ : A) → star))
        ( H x y)
        ( is-prop-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)

abstract
  eq-type-Prop : {l : Level} (P : Prop l) → {x y : type-Prop P} → x ＝ y
  eq-type-Prop P = eq-is-prop (is-prop-type-Prop P)

abstract
  is-proof-irrelevant-type-Prop :
    {l : Level} (P : Prop l) → is-proof-irrelevant (type-Prop P)
  is-proof-irrelevant-type-Prop P =
    is-proof-irrelevant-is-prop (is-prop-type-Prop P)
```

One useful feature of propositions, is that in order to construct an equivalence `e : P ≃ Q` between propositions, it suffices to construct maps back and forth between them.

## Proposition 12.1.4

A map `f : P → Q` between two propositions `P` and `Q` is an equivalence if and only if there is a map `g : Q → P`.
Consequently, we have for any two propositions `P` and `Q` that

```text
(P ≃ Q) ↔ (P ↔ Q).
```

### Proof

Of course, if we have an equivalence `e : P ≃ Q`, then we get maps back and forth between `P` and `Q`.
Therefore it remains to show that

```text
  (P ↔ Q) → (P ≃ Q).
```

Suppose we have `f : P → Q` and `g : Q → P`.
Then we obtain the homotopies `f ∘ g ~ id` and `g ∘ f ~ id` by the fact that any two elements in `P` and `Q` can be identified.
Therefore `f` is an equivalence with inverse `g`. ◻

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-has-converse-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-has-converse-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-is-invertible
        ( g)
        ( λ y → eq-is-prop is-prop-B)
        ( λ x → eq-is-prop is-prop-A)

  abstract
    equiv-iff-is-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-iff-is-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-iff-is-prop is-prop-A is-prop-B f g) =
      is-equiv-has-converse-is-prop is-prop-A is-prop-B g

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  abstract
    is-equiv-has-converse :
      {f : type-Prop P → type-Prop Q} → (type-Prop Q → type-Prop P) → is-equiv f
    is-equiv-has-converse =
      is-equiv-has-converse-is-prop
        ( is-prop-type-Prop P)
        ( is-prop-type-Prop Q)

  equiv-iff' : (type-Prop P ↔ type-Prop Q) → (type-Prop P ≃ type-Prop Q)
  pr1 (equiv-iff' t) = forward-implication t
  pr2 (equiv-iff' t) =
    is-equiv-has-converse-is-prop
      ( is-prop-type-Prop P)
      ( is-prop-type-Prop Q)
      ( backward-implication t)

  equiv-iff :
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) →
    type-Prop P ≃ type-Prop Q
  equiv-iff f g = equiv-iff' (f , g)
```
