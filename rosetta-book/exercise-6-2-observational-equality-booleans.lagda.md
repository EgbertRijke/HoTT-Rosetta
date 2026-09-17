# Exercise 6.2

```agda
module exercise-6-2-observational-equality-booleans where

open import universe-levels
open import exercise-4-2-boolean-operations
open import section-4-2-the-unit-type
open import section-4-3-the-empty-type
open import section-5-1-the-inductive-definition-of-identity-types
```

## Problem statement

Define observational equality `Eq-bool` by induction on the booleans.

Show that
```text
(x=y)↔ Eq-bool(x,y)
```
for any `x,y:bool`.

Show that `b≠neg-bool(b)` for any `b:bool`.
Conclude that `false≠true`.

## Solution

```agda
Eq-bool : bool → bool → UU lzero
Eq-bool true true = unit
Eq-bool true false = empty
Eq-bool false true = empty
Eq-bool false false = unit
```

```agda
refl-Eq-bool : (x : bool) → Eq-bool x x
refl-Eq-bool true = star
refl-Eq-bool false = star

Eq-eq-bool :
  {x y : bool} → x ＝ y → Eq-bool x y
Eq-eq-bool {x = x} refl = refl-Eq-bool x

eq-Eq-bool :
  {x y : bool} → Eq-bool x y → x ＝ y
eq-Eq-bool {true} {true} star = refl
eq-Eq-bool {false} {false} star = refl

neq-false-true-bool : ¬ (false ＝ true)
neq-false-true-bool ()

neq-true-false-bool : ¬ (true ＝ false)
neq-true-false-bool ()
```

```agda
neq-neg-bool : (b : bool) → ¬ (b ＝ neg-bool b)
neq-neg-bool true ()
neq-neg-bool false ()
```
