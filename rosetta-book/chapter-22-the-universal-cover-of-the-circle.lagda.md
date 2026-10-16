# Chapter 22 The universal cover of the circle

```agda
module chapter-22-the-universal-cover-of-the-circle where

open import section-22-1-the-universal-cover-of-the-circle
open import section-22-2-working-with-descent-data
open import section-22-3-the-dependent-universal-property-of-the-integers
open import section-22-4-the-fundamental-group-of-the-circle
open import exercise-22-1-exercise
open import exercise-22-2-exercise
open import exercise-22-3-exercise
open import exercise-22-4-exercise
open import exercise-22-5-exercise
open import exercise-22-6-exercise
open import exercise-22-7-exercise
open import exercise-22-8-exercise
open import exercise-22-9-exercise
open import exercise-22-10-exercise
open import exercise-22-11-exercise
```

In this section we use the univalence axiom to construct the *universal cover* of the circle and show that the loop space of the circle is equivalent to `ℤ`.
The universal cover of the circle is a family of sets over the circle with contractible total space.
Classically, the universal cover is described as a map `ℝ → S^1` that winds the real line around the circle.
In homotopy type theory the universal cover is constructed as a map `S^1 → Set` into the univalent type of all sets, and we will use the dependent universal property of the circle to show that its total space is contractible.
