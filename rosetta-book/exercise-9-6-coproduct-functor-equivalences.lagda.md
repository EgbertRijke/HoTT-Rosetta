# Exercise 9.6

```agda
module exercise-9-6-coproduct-functor-equivalences where

```

## Problem statement

Recall from Remark 4.4.2 that coproducts have a **functorial action**, i.e., that for every `f:A→ A'` and every `g:B→ B'` we have a map
```text
f+g:(A+B)→ (A'+B').
```

Show that `id[A]+id[B]~ id[A+B]`.

Show that for any two pairs of composable functions

```text
 [A] --f--> [A']--{f'}-->[A'']
```
there is a homotopy `(f'∘ f)+(g'∘ g) ~ (f'+g')∘ (f+g)`.

Show that if `H:f~ f'` and `K:g~ g'`, then there is a homotopy
```text
H+K:(f+g)~ (f'+g').
```

Show that if both `f` and `g` are equivalences, then so is `f+g`. (The converse of this statement also holds, see Exercise 11.7.)

## Solution

BENCHMARK PROBLEM
