# Exercise 5.7 Group laws for integers

```agda
module exercise-5-7-group-laws-integers where
```

## Problem statement

In this exercise we will show that the laws for abelian groups hold for addition
on the integers, using the group operations on `ℤ`.

1. Show that addition satisfies the left and right unit laws, i.e., show that

```text
  0 + x = x
  x + 0 = x.
```

2. Show that the following successor and predecessor laws hold for addition on
   `ℤ`.

```text
  pred-ℤ(x) + y = pred-ℤ(x + y)
  succ-ℤ(x) + y = succ-ℤ(x + y)
  x + pred-ℤ(y) = pred-ℤ(x + y)
  x + succ-ℤ(y) = succ-ℤ(x + y).
```

3. Use part 2 to show that addition on the integers is associative and
   commutative:

```text
  (x + y) + z = x + (y + z)
  x + y = y + x.
```

4. Show that addition satisfies the left and right inverse laws:

```text
  (-x) + x = 0
  x + (-x) = 0.
```


## Solution
