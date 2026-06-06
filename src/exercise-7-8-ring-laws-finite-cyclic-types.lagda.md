# Exercise 7.8 Ring laws for finite cyclic types

```agda
module exercise-7-8-ring-laws-finite-cyclic-types where
```

## Problem statement

The multiplication operation `x, y ↦ xy` on `ℤ/(k + 1)` is defined by

```text
  xy := [nat-Fin(x) nat-Fin(y)]_(k + 1).
```

Show that `nat-Fin(xy) ≡ nat-Fin(x) nat-Fin(y) mod k + 1` for each
`x, y : ℤ/(k + 1)`.

## Solution

## Problem statement

Show that

```text
  xy ≡ x'y' mod k
```

for any `x, y, x', y' : ℕ` such that `x ≡ x'` and `y ≡ y' mod k`.

## Solution

## Problem statement

Show that multiplication on `ℤ/(k + 1)` satisfies the laws of a commutative
ring:

```text
  (xy)z = x(yz)       xy = yx
  1x   = x            x1 = x
  x(y + z) = xy + xz  (x + y)z = xz + yz.
```

## Solution
