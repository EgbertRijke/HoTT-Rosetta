# Exercise 5.5 Semiring laws for natural numbers

```agda
module exercise-5-5-semiring-laws-natural-numbers where
```

## Problem statement

In this exercise we show that the operations of addition and multiplication on
the natural numbers satisfy the laws of a commutative **semiring**.

1. Show that multiplication satisfies the following laws:

```text
  m · 0 = 0
  m · 1 = m
  m · succ-ℕ(n) = m + m · n
  0 · m = 0
  1 · m = m
  succ-ℕ(m) · n = m · n + n.
```

2. Show that multiplication on `ℕ` is commutative:

```text
  m · n = n · m.
```

3. Show that multiplication on `ℕ` distributes over addition from the left and
   from the right, i.e., show that we have identifications

```text
  m · (n + k) = m · n + m · k
  (m + n) · k = m · k + n · k.
```

4. Show that multiplication on `ℕ` is associative:

```text
  (m · n) · k = m · (n · k).
```


## Solution
