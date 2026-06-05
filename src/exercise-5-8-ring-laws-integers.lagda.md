# Exercise 5.8 Ring laws for integers

```agda
module exercise-5-8-ring-laws-integers where
```

## Problem statement

In this exercise we will show that `ℤ` satisfies the axioms of a **ring**,
using multiplication on the integers.

1. Show that multiplication on `ℤ` satisfies the following laws for `0` and
   `1`:

```text
  0 · x = 0
  1 · x = x
  x · 0 = 0
  x · 1 = x.
```

2. Show that multiplication on `ℤ` satisfies the predecessor and successor
   laws:

```text
  pred-ℤ(x) · y = x · y - y
  succ-ℤ(x) · y = x · y + y
  x · pred-ℤ(y) = x · y - x
  x · succ-ℤ(y) = x · y + x.
```

3. Show that multiplication on `ℤ` distributes over addition, both from the
   left and from the right:

```text
  x · (y + z) = x · y + x · z
  (x + y) · z = x · z + y · z.
```

4. Show that multiplication on `ℤ` is associative and commutative:

```text
  (x · y) · z = x · (y · z)
  x · y = y · x.
```

## Solution
