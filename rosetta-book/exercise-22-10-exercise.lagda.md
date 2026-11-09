# Exercise 22.10

```agda
module exercise-22-10-exercise where

```

## Problem statement

In this exercise we give an alternative proof that the total space of `E_{S¹}` is contractible.

### Exercise 22.10(a)

Construct a function

```text
h : Π(k : ℤ) (base,0_E) = (base,k_E)
```

equipped with a homotopy

```text
H : Π(k : ℤ) h(succ-ℤ(k)) = h(k) ∙ segment-helix(k).
```

### Exercise 22.10(b)

Show that the total space `Σ(t : S¹) E_{S¹}(t)` of the universal cover of the circle is contractible.

## Solution

Both parts are formalized in the proof of [Theorem 22.4.1](section-22-4-the-fundamental-group-of-the-circle.lagda.md#theorem-2241). For (a), `Contraction-universal-cover-circle` supplies the paths and their successor law. For (b), `is-torsorial-universal-cover-circle` uses these data to contract the total space.

```agda
open import section-22-4-the-fundamental-group-of-the-circle
  using
    ( Contraction-universal-cover-circle
    ; is-torsorial-universal-cover-circle)
```
