# Chapter 15 Image factorizations

```agda
module chapter-15-image-factorizations where
```

The image of a map `f : A → X` can be thought of as the least subtype of `X`
that contains all the values of `f`.
More precisely, the image of `f` is an embedding `i : im(f) ↪ X` that fits in
a commuting triangle

```text
      q
  A ----> im(f)
   \      /
  f \    / i
     X
```

and satisfies the *universal property* of the image of `f`, which states that
if a subtype `B ↪ X` contains all the values of `f`, then it contains the image
of `f`.

```agda
open import section-15-1-the-image-of-a-map
open import section-15-2-surjective-maps
open import section-15-3-cantor-s-diagonal-argument
open import exercise-15-1-image-universal-property-triangles
open import exercise-15-2-subtypes-of-the-unit-type
open import exercise-15-3-equivalences-are-surjective-embeddings
open import exercise-15-4-surjective-triangles
open import exercise-15-5-lawveres-fixed-point-theorem
```
