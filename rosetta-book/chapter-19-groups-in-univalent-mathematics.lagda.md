# Chapter 19 Groups in univalent mathematics

```agda
module chapter-19-groups-in-univalent-mathematics where

open import section-19-1-the-type-of-all-groups
open import section-19-2-group-homomorphisms
open import section-19-3-isomorphic-groups-are-equal
open import section-19-4-homotopy-groups-of-types
open import section-19-5-the-eckmann-hilton-argument
open import section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics
open import exercise-19-1-exercise
open import exercise-19-2-exercise
open import exercise-19-3-exercise
open import exercise-19-4-exercise
open import exercise-19-5-exercise
open import exercise-19-6-exercise
open import exercise-19-7-exercise
open import exercise-19-8-exercise
open import exercise-19-9-exercise
open import exercise-19-10-exercise
open import exercise-19-11-exercise
open import exercise-19-12-exercise
open import exercise-19-13-exercise
open import exercise-19-14-exercise
open import exercise-19-15-exercise
open import exercise-19-16-exercise
open import exercise-19-17-exercise
```

In this section we demonstrate a very common way to use the univalence axiom, showing that isomorphic groups can be identified.
When you introduce a certain kind of structure in type theory, such as groups or rings, you automatically obtain the type of all such structures.
In other words, we define what a group is by defining the type of all groups, we define what a ring is by defining the type of all rings, and so on.
The elements of the type of all groups are of course groups, such as the group of integers, integers modulo `k`, automorphism groups, and so on.
The next important question is how two elements in the type of groups can be identified.
This question is answered with the help of the univalence axiom: isomorphic groups can be identified.
This is an instance of the *structure identity principle*, which we covered in Section 11.6.

Identifying isomorphic groups is a common *informal* practice in classical mathematics.
For example, by the third isomorphism theorem we have an isomorphism
```text
(G/N)/(K/N) ≅ (G/K)
```
for any sequence `N ⊴ K ⊴ G` of normal subgroups of `G`, and it is common to simply write `(G/N)/(K/N) = G/K`.
Of course, classical mathematicians know that this convention is incompatible with the axioms of Zermelo-Fraenkel set theory, but that does not stop them from applying this useful abuse of notation.
In univalent mathematics we make this informal practice precise and formal.
