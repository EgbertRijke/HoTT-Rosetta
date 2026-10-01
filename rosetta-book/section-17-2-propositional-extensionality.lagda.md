# Section 17.2 Propositional extensionality

```agda
module section-17-2-propositional-extensionality where

open import universe-levels
open import section-4-6-dependent-pair-types
open import exercise-4-3-double-negation-logic
open import section-5-1-the-inductive-definition-of-identity-types
open import section-9-2-bi-invertible-maps
open import section-10-1-contractible-types
open import section-10-4-equivalences-are-contractible-maps
open import exercise-10-3-contractible-equivalences
open import section-11-1-families-of-equivalences
open import section-11-2-the-fundamental-theorem
open import section-12-1-propositions
open import section-12-2-subtypes
open import section-13-1-equivalent-forms-of-function-extensionality
open import exercise-13-3-truncatedness-is-a-proposition
open import section-14-3-logic-in-type-theory
open import section-15-3-cantors-diagonal-argument
open import section-17-1-equivalent-forms-of-the-univalence-axiom
```

An important direct consequence of the univalence axiom is the principle of propositional extensionality.
This principle asserts that any two logically equivalent propositions `P` and `Q` can be identified.
Propositional extensionality is an important principle on its own, which is sometimes assumed in formal systems without the univalence axiom.

In order to prove propositional extensionality, we first observe that the univalence axiom also characterizes the identity type of any subuniverse.

## Proposition 17.2.1

Consider a universe `𝒰`, and let `P` be a family of propositions over `𝒰`.
Then the family of maps

```text
  equiv-eq : (A = B) → (pr1(A) ≃ pr1(B))
```

indexed by `A, B : Σ(X : 𝒰) P(X)`, given by `equiv-eq(refl) ≔ id` is an equivalence.

### Proof

Since `P` is a subuniverse, it follows from Corollary 12.2.4 that the projection map is an embedding.
Therefore we see that the asserted map is the composite of the equivalences

```text
          ap_pr1                      equiv-eq
  (A = B)--------> (pr1(A) = pr1(B)) ----------> (pr1(A) ≃ pr1(B)) ◻
```

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-iff-Prop P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv)

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P ↔ type-Prop Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q

module _
  {l1 : Level}
  where

  abstract
    is-torsorial-iff :
      (P : Prop l1) → is-torsorial (λ (Q : Prop l1) → type-Prop P ↔ type-Prop Q)
    is-torsorial-iff P =
      is-contr-equiv
        ( Σ (Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
        ( equiv-tot (equiv-equiv-iff P))
        ( is-torsorial-Eq-subtype
          ( is-torsorial-equiv (type-Prop P))
          ( is-property-is-prop)
          ( type-Prop P)
          ( id-equiv)
          ( is-prop-type-Prop P))

  abstract
    is-equiv-iff-eq : (P Q : Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
    is-equiv-iff-eq P =
      fundamental-theorem-id (is-torsorial-iff P) (λ Q → iff-eq {P = P} {Q})

  propositional-extensionality :
    (P Q : Prop l1) → (P ＝ Q) ≃ (type-Prop P ↔ type-Prop Q)
  pr1 (propositional-extensionality P Q) = iff-eq
  pr2 (propositional-extensionality P Q) = is-equiv-iff-eq P Q

  eq-iff' : (P Q : Prop l1) → type-Prop P ↔ type-Prop Q → P ＝ Q
  eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

  eq-iff :
    {P Q : Prop l1} →
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → P ＝ Q
  eq-iff {P} {Q} f g = eq-iff' P Q (pair f g)

  eq-equiv-Prop :
    {P Q : Prop l1} → type-Prop P ≃ type-Prop Q → P ＝ Q
  eq-equiv-Prop e =
    eq-iff (map-equiv e) (map-inv-equiv e)

  equiv-eq-Prop :
    {P Q : Prop l1} → P ＝ Q → type-Prop P ≃ type-Prop Q
  equiv-eq-Prop {P} refl = id-equiv

  is-torsorial-equiv-Prop :
    (P : Prop l1) → is-torsorial (λ Q → type-Prop P ≃ type-Prop Q)
  is-torsorial-equiv-Prop P =
    is-contr-equiv'
      ( Σ (Prop l1) (λ Q → type-Prop P ↔ type-Prop Q))
      ( equiv-tot (equiv-equiv-iff P))
      ( is-torsorial-iff P)
```

## Remark 17.2.2

Often, when `P` is a subuniverse, i.e., a subtype of the a universe `𝒰`, we will also write `A` for the type `pr1(A)` if `A : Σ(X : 𝒰) P(X)`.
Using this shorthand notation, the equivalence in Proposition 17.2.1 is displayed as

```text
  (A = B) ≃ (A ≃ B).
```

Important examples of subuniverses include the subuniverse `Prop_𝒰` of propositions in `𝒰`, the subuniverse `Set_𝒰` of sets in `𝒰`, and the subuniverse `𝒰^{≤ k}` of `k`-truncated types in `𝒰`.
The subuniverse `𝔽` of finite types in `𝒰₀`, and the subuniverses `BS_k` of `k`-element types are further important subuniverses to which Proposition 17.2.1 applies.
Note that by the univalence axiom, any subuniverse is automatically closed under equivalences.
Indeed, if we have `X ≃ Y`, then we have `P(X) → P(Y)` by transporting along the equality `X = Y` induced by univalence.

## Theorem 17.2.3

Propositions satisfy **propositional extensionality**: For any two propositions `P` and `Q`, the canonical map

```text
  iff-eq : (P = Q) → (P ⇔ Q)
```

defined by `iff-eq(refl) ≔ (id,id)` is an equivalence.
It follows that the type `Prop_𝒰` of propositions in `𝒰` is a set.

### Proof

Recall from Exercise 13.3 that `is-prop(X)` is a proposition for any type `X`.
Proposition 17.2.1 therefore applies, which gives

```text
  (P = Q) ≃ (P ≃ Q) ≃ (P ↔ Q).
```

The last equivalence follows from Proposition 12.1.4, using the fact that `P ≃ Q` is a proposition by Exercise 13.4. ◻

## Corollary 17.2.4

The type

```text
  decidable-Prop_𝒰 ≔ Σ(P : Prop_𝒰) is-decidable(P)
```

of decidable propositions in any universe `𝒰` is equivalent to `bool`.

### Proof

Note that `Σ` distributes from the left over coproducts, so we have an equivalence

```text
  (Σ(P : Prop_𝒰) P + ¬ P) ≃ (Σ(P : Prop_𝒰) P) + (Σ(Q : Prop_𝒰) ¬ Q).
```

Therefore it suffices to show that both `Σ(P : Prop_𝒰) P` and `Σ(Q : Prop_𝒰) ¬ Q` are contractible.
At the centers of contraction we have `(unit,⋆)` and `(empty,id)`, respectively.
For the contractions, note that both types are subtypes of the types of propositions.
Therefore it suffices to show that `unit = P` for any proposition `P` equipped with `p : P`, and that `empty = Q` for any proposition `Q` equipped with `q : ¬ Q`.
Both identifications are obtained immediately from propositional extensionality. ◻

