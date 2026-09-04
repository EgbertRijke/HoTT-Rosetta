# Section 20.4 The elementhood relation on W-types

```agda
module section-20-4-the-elementhood-relation-on-w-types where
```

<!-- rosetta-item: section-20.4 -->

The elements of a W-type `W(A,B)` are constructed out of families of elements of `W(A,B)` indexed by a type `B(x)` for some `x:A`.
More precisely, for each `tree(x,α):W(A,B)` we have a family of elements
```text
α(y):W(A,B)
```
indexed by `y:B(x)`.
Thus, we could say that `α(y)` is in `tree(x,α)`, for each `y:B(x)`.
More abstractly, we can define an elementhood relation on `W(A,B)`.

## Definition 20.4.1

<!-- rosetta-item: definition-20.4.1 -->

Given a W-type `W(A,B)` and a universe `𝒰` containing both `A` and each type in the family `B`, we define a type-valued relation
```text
{∈}:W(A,B)→W(A,B)→ 𝒰
```
by `(x∈ tree(a,α))≔ Σ(y:B(a)) α(y)=x`.

<!-- rosetta-item-end: definition-20.4.1 -->

Using the elementhood relation on `W(A,B)`, we can reformulate the induction principle to, perhaps, a more recognizable form:

## Theorem 20.4.2

<!-- rosetta-item: theorem-20.4.2 -->

For any family `P` of types over `W(A,B)`, there is a function
```text
i : (Π(x:W(A,B)) (Π(y:W(A,B)) (y∈ x)→ P(y))→ P(x))→ (Π(x:X) P(x))
```
that comes equipped with an identification
```text
i(h,x)=h(x,λ y. λ e. i(h,y))
```
for every `h:Π(x:W(A,B)) (Π(y:W(A,B)) (y∈ x)→ P(y))→ P(x)`, and every `x:W(A,B)`.

### Proof

<!-- rosetta-item: subheading-20.4-proof -->

*Proof.* For any type family `P` over `W(A,B)`, we first define a new type family `□ P` over `W(A,B)` given by
```text
□ P(x):=Π(y:W(A,B)) (y∈ x)→ P(y).
```
The family `□ P(x)` comes equipped with a map
```text
η : (Π(x:W(A,B)) P(x))→ (Π(x:W(A,B)) □ P(x))
```
given by `η(f,x,y,e)≔ f(y)`.
Conversely, there is a map
```text
ε(h) : (Π(y:W(A,B)) □ P(y)) → (Π(x:W(A,B)) P(x))
```
for every `h:Π(y:W(A,B)) □ P (y)→ P(y)`, given by `ε(h,g,x)≔ h(x,g(x))`.
Note that the induction principle can now be stated as
```text
i : (Π(y:W(A,B)) □ P (y)→ P(y))→(Π(x:W(A,B)) P(x)),
```
and the computation rule states that
```text
i(h,x)=h(x,η(i(h),x)).
```
Before we prove the induction principle, we prove the intermediate claim that there is a function
```text
i' : (Π(y:W(A,B)) □ P (y)→ P(y)) → (Π(x:W(A,B)) □ P(x))
```
equipped with an identification
```text
j'(h,x,y,e) : i'(h,x,y,e) = h(y,i'(h,y))
```
for every `h:Π(y:W(A,B)) □ P(y)→ P(y)` and every `x,y:W(A,B)` equipped with `e:y∈ x`.
Both `i'` and `j'` are defined by pattern matching:
```text
i'(h,tree(a,f),f(b),(b,refl)) := h(f(b),i'(h,f(b)))
j'(h,tree(a,f),f(b),(b,refl)) := refl.
```
Now we define `i(h):=ε(h,i'(h))`.
Note that we have the judgmental equalities
```text
i(h,x) ≐ ε(h,i'(h),x)
≐ h(x,i'(h,x)),
```

and

```text
h(x,λ y. λ e. i(h,y))
≐ h(x,λ y. λ e. ε(h,i'(h),y))
≐ h(x,λ y. λ e. h(y,i'(h,y))).
```
The computation rule is therefore satisfied by the identification
<!-- rosetta-diagram: 4831940baace; review: pending -->

*Linear diagram (automatic draft).*

```text
[h(x,i'(h,x))]---->[h(x,λ y. λ e. h(y,i'(h,y)))]

Arrows:
- h(x,i'(h,x)) --ap_{h(x)}(eq-htpy(λ y. eq-htpy(j'(h,x,y))))--> h(x,λ y. λ e. h(y,i'(h,y)))
```
 ◻

<!-- rosetta-item-end: theorem-20.4.2 -->
