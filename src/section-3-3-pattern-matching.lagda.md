# 3.3 Pattern matching

```agda
module section-3-3-pattern-matching where

open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
```

Note that in definition 3.2.1 we stated that `add-ℕ` is a function of type `ℕ → (ℕ → ℕ)` satisfying the specification

```text
          add-ℕ(m,0) ≐ m
  add-ℕ(m,succ-ℕ(n)) ≐ succ-ℕ(add-ℕ(m,n)).
```

Such a specification is enough to characterize the function `add-ℕ(m)` entirely, because it postulates the behaviour of `add-ℕ(m)` at the constructors of `ℕ`.
It is therefore convenient to present the definition of `add-ℕ` recursively in the following way:

```text
          add-ℕ(m,0) ≔ m
  add-ℕ(m,succ-ℕ(n)) ≔ succ-ℕ(add-ℕ(m,n)).
```

More generally, if we want to define a dependent function `f : Π(n : ℕ) P(n)` by induction on `n`, using

```text
  p_0 : P(0)
  p_S : Π(n : ℕ)  P(n) → P(succ-ℕ(n)),
```

we can present that definition by writing

```text
          f(0) ≔ p_0
  f(succ-ℕ(n)) ≔ p_S(n,f(n)). 
```

When the definition of `f` is presented in this way, we say that `f` is defined by **pattern matching** on the variable `n`.
To see that `f` is fully specified when it is defined by pattern matching, we have to recover the dependent function

```text
  p_S : Π(n : ℕ) P(n) → P(succ-ℕ(n))
```

from the expression `p_S(n,f(n))` that was used in the definition of `f`.
This can of course be done by replacing all occurrences of the term `f(n)` in the expression `p_S(n,f(n))` with a fresh variable `x : P(n)`.
In other words, when a subexpression of `p_S(n,f(n))` *matches* `f(n)`, we replace that subexpression by `x`.
This is where the name *pattern matching* comes from.
Many computer proof assistants have the pattern matching mechanism built in, because it is a concise way of presenting a recursive definition.
Another advantage of presenting definitions by pattern matching is that the judgmental equalities by which the object is defined are immediately displayed.
Those judgmental equalities are all that is known about the defined object, and often proving things about it amounts to finding a way to apply those judgmental equalities.

Pattern matching can also be used in more complicated situations, such as defining a function by pattern matching on multiple variables, or by iterated pattern matching.
For example, an alternative definition of addition on $ℕ$ could be given by pattern matching on both variables:

```text
                  add-ℕ'(0,0) ≔ 0
          add-ℕ'(0,succ-ℕ(n)) ≔ succ-ℕ(n) 
          add-ℕ'(succ-ℕ(m),0) ≔ succ-ℕ(m)
  add-ℕ'(succ-ℕ(m),succ-ℕ(n)) ≔ succ-ℕ(succ-ℕ(add-ℕ'(m,n)).
```

An example of a definition by iterated pattern matching is the **Fibonacci function** `F : ℕ → ℕ`.
This function is defined by

```text
                  F(0) ≔ 0
                  F(1) ≔ 1
  F(succ-ℕ(succ-ℕ(n))) ≔ F(succ-ℕ(n)) + F(n).
```

```agda
fibonacci-ℕ : ℕ → ℕ
fibonacci-ℕ 0 = 0
fibonacci-ℕ (succ-ℕ 0) = 1
fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = fibonacci-ℕ (succ-ℕ n) +ℕ fibonacci-ℕ n
```

However, since `F(succ-ℕ(succ-ℕ(n)))` is defined using both `F(succ-ℕ(n))` and `F(n)`, it is not immediately clear how to present `F` by the usual induction principle of `ℕ`.
It is a nice puzzle, which we leave as Exercise 3.5, to find a definition of the Fibonacci sequence with the usual induction principle of `ℕ`. 

## Agda-unimath sources

- The Fibonacci sequence is defined in `elementary-number-theory.fibonacci-sequence`.
