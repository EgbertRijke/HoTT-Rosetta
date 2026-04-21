# Exercise 3.6 Division by two 

```agda
module exercise-3-6-division-by-two where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
```

## Problem statement

Define division by two rounded down as a function `ℕ → ℕ` by pattern matching.

## Solution 

```agda
division-by-two : ℕ → ℕ 
division-by-two zero-ℕ = 0
division-by-two (succ-ℕ zero-ℕ) = 0
division-by-two (succ-ℕ (succ-ℕ n)) = succ-ℕ (division-by-two n)

```

## Problem statement

Define division by two rounded down as a function `ℕ → ℕ` directly by the induction principle of `ℕ`.

## Solution 

```agda
division-by-two' : ℕ → ℕ
division-by-two' = ind-ℕ 0 (ind-ℕ {!   !} {!   !})
```


## Agda-unimath sources

- 
