# Exercise 22.7

```agda
module exercise-22-7-exercise where

```

## Problem statement

Show that the multiplicative operation on the circle is associative, i.e. construct an identification
```text
assoc_{S¹}(x,y,z) :
mul_(S¹)(mul_(S¹)(x,y),z) = mul_(S¹)(x,mul_(S¹)(y,z))
```
for any `x,y,z : S¹`.

Show that the associator satisfies unit laws, in the sense that the following triangles commute:

```text
[mul_(S¹)(mul_(S¹)(base,x),y)] ----> [mul_(S¹)(base,mul_(S¹)(x,y))]
               \                                    /
                   \                            /
                      \                     /
                          V             V
                          [mul_(S¹)(x,y)]
```

```text
[mul_(S¹)(mul_(S¹)(x,base),y)] ----> [mul_(S¹)(x,mul_(S¹)(base,y))]
               \                                    /
                   \                            /
                      \                     /
                          V             V
                          [mul_(S¹)(x,y)]
```

```text
[mul_(S¹)(mul_(S¹)(x,y),base)] ----> [mul_(S¹)(x,mul_(S¹)(y,base))]
               \                                    /
                   \                            /
                      \                     /
                          V             V
                          [mul_(S¹)(x,y)]
```

State the laws that compute
```text
assoc_{S¹}(base,base,x)
assoc_{S¹}(base,x,base)
assoc_{S¹}(x,base,base)
assoc_{S¹}(base,base,base).
```
Note: the first three laws should be `3`-cells and the last law should be a `4`-cell.
The laws are automatically satisfied, since the circle is a `1`-type.

## Solution

BENCHMARK PROBLEM
