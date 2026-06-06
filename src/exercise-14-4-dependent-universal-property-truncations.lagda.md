# Exercise 14.4 Dependent universal property truncations

```agda
module exercise-14-4-dependent-universal-property-truncations where
```

## Problem statement

Consider a map `f : A → P` into a proposition `P`.
We say that `f` satisfies the **dependent universal property of the
propositional truncation** of `A`, if for any family `Q` of propositions over
`P`, the precomposition function

```text
  _ ∘ f : (Π(p : P) Q(p)) → (Π(x : A) Q(f(x)))
```

is an equivalence.
Show that the following are equivalent:

1. The map `f` is a propositional truncation.
2. The map `f` satisfies the dependent universal property of the propositional
   truncation.

## Solution
