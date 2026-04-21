# Exercise 3.5 Fibonacci sequence

```agda
module exercise-3-5-fibonacci-sequence where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers 
```

## Problem statement

Use the induction principle of `ℕ` to define the **Fibonacci sequence** as a function `F : ℕ → ℕ` that satisfies the equations

```text 
                F(0) ≐ 0 
                F(1) ≐ 1 
F(succ-ℕ(succ-ℕ(n))) ≐ F(succ-ℕ(n)) + F(n)
```

## Solution 

It is possible to use Agda's pattern matching to define the Fibonacci sequence as follows:

```agda
Fibonacci-ℕ : ℕ → ℕ
Fibonacci-ℕ 0 = 0
Fibonacci-ℕ (succ-ℕ 0) = 1
Fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = (Fibonacci-ℕ (succ-ℕ n)) +ℕ (Fibonacci-ℕ n)
```

However, the exercise asks instead to give a definition of the Fibonacci sequence
in terms of `ind-ℕ`.

The problem with defining the Fibonacci sequence using `ind-ℕ`, is that `ind-ℕ`
doesn't give us a way to refer to both `(F n)` and `(F (succ-ℕ n))`. So, we have
to give a workaround, where we store two values in the Fibonacci sequence at
once.

The basic idea is that we define a sequence of pairs of integers, which will be
consecutive Fibonacci numbers. This would be a function of type `ℕ → ℕ × ℕ`.

Such a function is easy to give with induction, using the map `ℕ × ℕ → ℕ × ℕ` that
takes a pair `(m,n)` to the pair `(n,n+m)`. Starting the iteration with `(0,1)`
we obtain the Fibonacci sequence by taking the first projection.

However, we haven't defined cartesian products or booleans yet. Therefore we
mimic the above idea, using `ℕ → ℕ` instead of `ℕ × ℕ`, storing an ordered pair of natural numbers
as the values of our function at 0 and at 1.

```agda
shift-one : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f = ind-ℕ n (λ x y → f x)

shift-two : ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f = shift-one m (shift-one n f)

Fibo-zero-ℕ : ℕ → ℕ
Fibo-zero-ℕ = shift-two 0 1 (λ x → 0)

Fibo-succ-ℕ : (ℕ → ℕ) → (ℕ → ℕ)
Fibo-succ-ℕ f = shift-two (f 1) ((f 1) +ℕ (f 0)) (λ x → 0)

Fibo-function : ℕ → ℕ → ℕ
Fibo-function =
  ind-ℕ
    ( Fibo-zero-ℕ)
    ( λ n → Fibo-succ-ℕ)

Fibo : ℕ → ℕ
Fibo k = Fibo-function k 0
```

## Agda-unimath sources

- The definition of the Fibonacci sequence is implemented in `elementary-number-theory.fibonacci-sequence`.
