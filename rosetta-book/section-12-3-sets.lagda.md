# Section 12.3 Sets

```agda
module section-12-3-sets where
```

<!-- rosetta-item: section-12.3 -->

## Definition 12.3.1

<!-- rosetta-item: definition-12.3.1 -->

A type `A` is said to be a **set** if its identity types are propositions, i.e., if it comes equipped with a term of type
```text
is-set(A)≔ Π(x,y:A) is-prop(x = y).
```

<!-- rosetta-item-end: definition-12.3.1 -->

## Example 12.3.2

<!-- rosetta-item: example-12.3.2; latex-label: eg:is-set-nat -->

The type of natural numbers is a set.
To see this, recall from Theorem 11.3.1 that we have an equivalence
```text
(m=n)≃ Eq-ℕ(m,n)
```
for every `m,n:ℕ`.
Therefore it suffices to show that each `Eq-ℕ(m,n)` is a proposition.
This follows easily by induction on both `m` and `n`.

<!-- rosetta-item-end: example-12.3.2 -->

## Proposition 12.3.3

<!-- rosetta-item: proposition-12.3.3 -->

Consider a type `A`.
The following are equivalent:

1.  The type `A` is a set.

2.  The type `A` satisfies **axiom K**, i.e., if and only if it comes equipped with a term of type
```text
axiom-K(A)≔Π(x:A) Π(p:x = x) refl = p.
```

### Proof

<!-- rosetta-item: subheading-12.3-proof -->

*Proof.* If `A` is a set, then `x = x` is a proposition, so any two of its elements are equal.
This implies axiom `K`.

For the converse, if `A` satisfies axiom `K`, then for any `p,q:x = y` we have `p ∙ q^{-1} = refl`, and hence `p = q`.
This shows that `x = y` is a proposition, and hence that `A` is a set. ◻

<!-- rosetta-item-end: proposition-12.3.3 -->

## Theorem 12.3.4

<!-- rosetta-item: theorem-12.3.4; latex-label: lem:prop_to_id -->

Let `A` be a type, and let `R:A→ A→𝒰` be a binary relation on `A` satisfying

1.  Each `R(x,y)` is a proposition,

2.  `R` is reflexive, as witnessed by `ρ:Π(x:A) R(x,x)`,

3.  There is a map
```text
R(x,y)→ (x=y)
```
    for each `x,y:A`.

Then any family of maps
```text
Π(x,y:A) (x = y)→ R(x,y)
```
is a family of equivalences.
Consequently, the type `A` is a set.

### Proof

<!-- rosetta-item: subheading-12.3-proof-2 -->

*Proof.* Let `f:Π(x,y:A) R(x,y)→(x = y)`.
Since `R` is assumed to be reflexive, we also have a family of maps
```text
path-ind_x(ρ(x)):Π(y:A) (x = y)→ R(x,y).
```
Since each `R(x,y)` is assumed to be a proposition, it therefore follows that each `R(x,y)` is a retract of `x = y`.
Therefore it follows that `Σ(y:A) R(x,y)` is a retract of `Σ(y:A) x=y`, which is contractible.
We conclude that `Σ(y:A) R(x,y)` is contractible, and therefore that any family of maps
```text
Π(y:A) (x=y)→ R(x,y)
```
is a family of equivalences.

Now it also follows that `A` is a set, since its identity types are equivalent to propositions, and therefore they are propositions by Lemma 12.2.2. ◻

<!-- rosetta-item-end: theorem-12.3.4 -->

## Theorem 12.3.5

<!-- rosetta-item: theorem-12.3.5; latex-label: thm:hedberg -->

Any type with decidable equality is a set.

### Proof

<!-- rosetta-item: subheading-12.3-proof-3 -->

*Proof.* Let `A` be a type, and let `d:Π(x,y:A) (x = y)+ (x≠ y)` be the witness that `A` has decidable equality.
Furthermore, let `𝒰` be a universe containing the type `A`.
We will prove that `A` is a set by applying Theorem 12.3.4.

For every `x,y:A`, we first define a type family `R'(x,y):((x = y)+{(x≠ y)})→𝒰` by
```text
R'(x,y,inl(p)) ≔ unit
R'(x,y,inr(p)) ≔ empty.
```
Note that `R'(x,y,q)` is a proposition for each `x,y:A` and `q:(x = y)+(x≠ y)`.
Now we define `R(x,y)≔ R'(x,y,d(x,y))`.
Then `R` is a reflexive binary relation on `A`, and furthermore each `R(x,y)` is a proposition.
In order to apply Theorem 12.3.4, it therefore it remains to show that `R` implies identity.

Since `R` is defined as an instance of `R'`, it suffices to construct a function
```text
f(q) : R'(q)→ (x = y).
```
for each `q:(x = y)+(x≠ y)`.
Such a function is defined by
```text
f(inl(p),r) := p
f(inr(p),r) := ex-falso(r).
```
 ◻

<!-- rosetta-item-end: theorem-12.3.5 -->
