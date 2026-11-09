# Exercise 21.6

```agda
module exercise-21-6-exercise where

```

## Problem statement

### Exercise 21.6(a)

For the multiplication `mul_{S¹}` on the circle, construct an inverse operation

```text
inv : S¹ → S¹
```

and construct identifications

```text
left-inv_{S¹} : mul_{S¹}(inv(x),x) = base
right-inv_{S¹} : mul_{S¹}(x,inv(x)) = base.
```

### Exercise 21.6(b)

Moreover, show that the square

```text
          inv(base) ============== mul_{S¹}(base,inv(base))
              ||                               ||
  mul_{S¹}(inv(base),base) ================= base
```

commutes.

## Solution

BENCHMARK PROBLEM
