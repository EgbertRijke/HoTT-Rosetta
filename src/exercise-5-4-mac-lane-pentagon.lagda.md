# Exercise 5.4 Mac Lane pentagon

```agda
module exercise-5-4-mac-lane-pentagon where
```

## Problem statement

Consider four consecutive identifications

```text
      p       q       r       s
  a ===== b ===== c ===== d ===== e
```

in a type `A`.
In this exercise we will show that the **Mac Lane pentagon** for identifications
commutes.

## Problem 5.4(a)

Construct the five identifications `α₁, …, α₅` in the pentagon

```text
              α₄
  ((p ∙ q) ∙ r) ∙ s  =====  (p ∙ q) ∙ (r ∙ s)
          || α₁                         || α₅
          \/                            \/
  (p ∙ (q ∙ r)) ∙ s           p ∙ (q ∙ (r ∙ s))
          \\
           \\ α₂
            \\
             p ∙ ((q ∙ r) ∙ s)
                    ||
                    || α₃
                    \/
             p ∙ (q ∙ (r ∙ s)).
```

Here `α₁`, `α₂`, and `α₃` run counter-clockwise.
The identifications `α₄` and `α₅` run clockwise.

## Problem 5.4(b)

Show that
```text
  (α₁ ∙ α₂) ∙ α₃ = α₄ ∙ α₅.
```


## Solution
