# Exercise 15.5

```agda
module exercise-15-5-lawveres-fixed-point-theorem where

```

## Problem statement

Prove **Lawvere’s fixed point theorem**: For any two types `A` and `B`, if there is a surjective map `f : A → Bᴬ`, then for any `h : B → B` there exists an `x : B` such that `h(x) = x`, i.e., show that

```text
  (∃_{(f : A → (A → B))} is-surj(f)) → (∀_{(h : B → B)} ∃_{(b : B)} h(b) = b).
```

## Solution
