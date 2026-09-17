# Exercise 22.7

```agda
module exercise-22-7-exercise where

```

## Problem statement

Show that the multiplicative operation on the circle is associative, i.e. construct an identification
```text
assoc_{S^1}(x,y,z) :
mul_(S^1)(mul_(S^1)(x,y),z)=mul_(S^1)(x,mul_(S^1)(y,z))
```
for any `x,y,z:S^1`.

Show that the associator satisfies unit laws, in the sense that the following triangles commute:

*Triangle-shaped diagram (automatic draft).*

```text
[mul_(S^1)(mul_(S^1)(base,x),y)]                          [mul_(S^1)(base,mul_(S^1)(x,y))]

                                     [mul_(S^1)(x,y)]

Arrows:
- mul_(S^1)(mul_(S^1)(base,x),y) --unlabeled--> mul_(S^1)(base,mul_(S^1)(x,y))
- mul_(S^1)(mul_(S^1)(base,x),y) --unlabeled--> mul_(S^1)(x,y)
- mul_(S^1)(base,mul_(S^1)(x,y)) --unlabeled--> mul_(S^1)(x,y)
```

*Triangle-shaped diagram (automatic draft).*

```text
[mul_(S^1)(mul_(S^1)(x,base),y)]                          [mul_(S^1)(x,mul_(S^1)(base,y))]

                                     [mul_(S^1)(x,y)]

Arrows:
- mul_(S^1)(mul_(S^1)(x,base),y) --unlabeled--> mul_(S^1)(x,mul_(S^1)(base,y))
- mul_(S^1)(mul_(S^1)(x,base),y) --unlabeled--> mul_(S^1)(x,y)
- mul_(S^1)(x,mul_(S^1)(base,y)) --unlabeled--> mul_(S^1)(x,y)
```

*Triangle-shaped diagram (automatic draft).*

```text
[mul_(S^1)(mul_(S^1)(x,y),base)]                          [mul_(S^1)(x,mul_(S^1)(y,base))]

                                     [mul_(S^1)(x,y)]

Arrows:
- mul_(S^1)(mul_(S^1)(x,y),base) --unlabeled--> mul_(S^1)(x,mul_(S^1)(y,base))
- mul_(S^1)(mul_(S^1)(x,y),base) --unlabeled--> mul_(S^1)(x,y)
- mul_(S^1)(x,mul_(S^1)(y,base)) --unlabeled--> mul_(S^1)(x,y)
```

State the laws that compute
```text
assoc_{S^1}(base,base,x)
assoc_{S^1}(base,x,base)
assoc_{S^1}(x,base,base)
assoc_{S^1}(base,base,base).
```
Note: the first three laws should be `3`-cells and the last law should be a `4`-cell.
The laws are automatically satisfied, since the circle is a `1`-type.

## Solution

No formalization has been curated yet.
