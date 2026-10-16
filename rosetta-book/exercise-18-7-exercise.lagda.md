# Exercise 18.7

```agda
module exercise-18-7-exercise where

```

## Problem statement

Consider a map `f : A → B`.

Show that the type of maps `‖f‖₀ : ‖A‖₀ → ‖B‖₀` equipped with a homotopy witnessing that the square

```text
    A ---------f----------> B
    |                       |
  η |                       | η
    ∨                       ∨
  ‖A‖₀ ------‖f‖₀-------> ‖B‖₀
```
commutes is contractible.

Show that if `f` is injective, then `‖f‖₀ : ‖A‖₀ → ‖B‖₀` is injective.

Show that the following are equivalent

1. The map `f` is surjective.

2. the map `‖f‖₀ : ‖A‖₀ → ‖B‖₀` is surjective.

Construct a map `h : im(f) → im‖f‖₀` such that the squares

```text
    A --------q_f---------> im(f) --------i_f---------> B
    |                         |                         |
  η |                       h |                         | η
    ∨                         ∨                         ∨
  ‖A‖₀ -----q_{‖f‖₀}-----> im‖f‖₀ -----i_{‖f‖₀}-----> ‖B‖₀

Arrows:
- A --q_f--> im(f)
- A --η--> ‖A‖₀
- im(f) --h--> im‖f‖₀
- im(f) --i_f--> B
- B --η--> ‖B‖₀
- ‖A‖₀ --q_{‖f‖₀}--> im‖f‖₀
- im‖f‖₀ --i_{‖f‖₀}--> ‖B‖₀
```
commute, and show that `h` is a set truncation of `im(f)`.

## Solution

No formalization has been curated yet.
