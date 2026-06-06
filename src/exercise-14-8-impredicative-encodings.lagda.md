# Exercise 14.8 Impredicative encodings

```agda
module exercise-14-8-impredicative-encodings where
```

## Problem statement

Consider a universe `𝒰`, let `P_1` and `P_2` be propositions in `𝒰`, and
furthermore, let `P` be a family of propositions in `𝒰` over a type `A` in
`𝒰`.
Construct the following equivalences:

```text
  ⊤                    ≃ Π(Q : Prop_𝒰) Q → Q
  ⊥                    ≃ Π(Q : Prop_𝒰) Q
  ∥ A ∥                ≃ Π(Q : Prop_𝒰) (A → Q) → Q
  P_1 ∨ P_2            ≃ Π(Q : Prop_𝒰) (P_1 → Q) → ((P_2 → Q) → Q)
  P_1 ∧ P_2            ≃ Π(Q : Prop_𝒰) (P_1 → (P_2 → Q)) → Q
  P_1 ⇒ P_2            ≃ Π(Q : Prop_𝒰) P_1 → ((P_2 → Q) → Q)
  ¬ A                  ≃ Π(Q : Prop_𝒰) A → Q
  ∃(x : A), P(x)       ≃ Π(Q : Prop_𝒰) (Π(x : A) P(x) → Q) → Q
  ∀(x : A), P(x)       ≃ Π(Q : Prop_𝒰) Π(x : A) (P(x) → Q) → Q
  ∥ a = x ∥            ≃ Π(Q : A → Prop_𝒰) Q(a) → Q(x).
```

These are the **impredicative encodings** of the logical operators.
Note: It has the appearance that we could have defined `∥ A ∥` by its
impredicative encoding.
There is, however, a subtle issue if we take this as a definition: The map

```text
  A → Π(Q : Prop_𝒰) (A → Q) → Q
```

only satisfies the universal property of the propositional truncation with
respect to propositions that are equivalent to propositions in `𝒰`.

## Solution
