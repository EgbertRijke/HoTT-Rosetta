# Section 4.1 The idea of general inductive types

```agda
module section-4-1-the-idea-of-general-inductive-types where
```

Just like the type of natural numbers, other inductive types are also
specified by their *constructors*, an *induction principle*, and their
*computation rules*:

1. The constructors tell what structure the inductive type comes equipped with.
   There may be any finite number of constructors, even no constructors at all,
   in the specification of an inductive type.
2. The induction principle specifies the data that should be provided in order
   to construct a section of an arbitrary type family over the inductive type.
   The idea of the induction principle is always the same: in order to define a
   dependent function `f : Π(x : A) B(x)`, one has to specify the behavior of
   `f` at the constructors of `A`.
3. The computation rules assert that the inductively defined section agrees on
   the constructors with the data that was used to define the section.
   Thus, there is a computation rule for every constructor.

Since any inductively defined function is entirely determined by its behavior
on the constructors, we can again present such inductive definitions by pattern
matching.
Therefore, we will also specify for each inductive type how to give definitions
by pattern matching.
