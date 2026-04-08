# Chapter 3 The natural numbers

```agda
module chapter-3-the-natural-numbers where
```

The set of natural numbers is the most important object in mathematics. We quote Bishop, from his Constructivist Manifesto, the first chapter in Foundations of Constructive Analysis [Bishop1967], where he gives a colorful illustration of its importance to mathematics.

> The primary concern of mathematics is number, and this means the positive integers.
> We feel about number the way Kant felt about space.
> The positive integers and their arithmetic are presupposed by the very nature of our intelligence and, we are tempted to believe, by the very nature of intelligence in general.
> The development of the theory of the positive integers from the primitive concept of the unit, the concept of adjoining a unit, and the process of mathematical induction carries complete conviction.
> In the words of Kronecker, the positive integers were created by God.
> Kronecker would have expressed it even better if he had said that the positive integers were created by God for the benefit of man (and other finite beings).
> Mathematics belongs to man, not to God.
> We are not interested in properties of the positive integers that have no descriptive meaning for finite man.
> When a man proves a positive integer to exist, he should show how to find it.
> If God has mathematics of his own that needs to be done, let him do it himself.

A bit later in the same chapter, he continues:

> Building on the positive integers, weaving a web of ever more sets and ever more functions, we get the basic structures of mathematics: the rational number system, the real number system, the euclidean spaces, the complex number system, the algebraic number fields, Hilbert space, the classical groups, and so forth.
> Within the framework of these structures, most mathematics is done.
> Everything attaches itself to number, and every mathematical statement ultimately expresses the fact that if we perform certain computations within the set of positive integers, we shall get certain results.

```agda
open import section-3-1-the-formal-specification-of-the-type-of-natural-numbers
open import section-3-2-addition-on-the-natural-numbers
open import section-3-3-pattern-matching
```
