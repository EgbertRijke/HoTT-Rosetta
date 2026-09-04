# Section 12.4 General truncation levels

```agda
module section-12-4-general-truncation-levels where
```

<!-- rosetta-item: section-12.4 -->

Consider a type `A` in a universe `𝒰`.
The conditions
```text
is-contr(A) ≔ Σ(a:A) Π(x:A) a=x
is-prop(A) ≔ Π(x,y:A) is-contr(x=y)
is-set(A) ≔ Π(x,y:A) is-prop(x=y)
```
define the first few layers of the hierarchy of truncation levels.
This hierarchy starts at the level of the contractible types, which we call level `-2`.
The next level is the level of propositions, and at level `0` we have the sets.

The indexing type of the truncation levels, which will be equivalent to the type `ℤ_{≥ -2}` of integers greater than `-2`, is an inductive type `𝕋` equipped with the constructors
```text
-2 : 𝕋
succT : 𝕋→𝕋.
```
The natural inclusion `i:ℕ→ 𝕋` is defined recursively by
```text
i(0) ≔ succT(succT(-2))
i(succ-ℕ(n)) ≔ succT(i(n)).
```
Of course, we will simply write `-2` for `-2` and `k+1` for `succT(k)`.

## Definition 12.4.1

<!-- rosetta-item: definition-12.4.1 -->

We define `is-trunc : 𝕋→𝒰→𝒰` recursively by
```text
is-trunc{-2}(A) ≔ is-contr(A)
is-trunc{k+1}(A) ≔ Π(x,y:A) is-trunc{k}(x = y).
```
For any type `A`, we say that `A` is **`k`-truncated**, or a **`k`-type**, if there is a term of type `is-trunc{k}(A)`.
We also say that a type `A` is a **proper `(k+1)`-type** if `A` is a `(k+1)`-type and not a `k`-type.

Given a universe `𝒰`, we define the universe `𝒰^{≤ k}` of `k`-truncated types by
```text
𝒰^{≤ k}≔Σ(X:𝒰) is-trunc{k}(X).
```

Furthermore, we say that a map `f:A→ B` is `k`-truncated if its fibers are `k`-truncated.

<!-- rosetta-item-end: definition-12.4.1 -->

## Remark 12.4.2

<!-- rosetta-item: remark-12.4.2 -->

There is a subtlety in the definition of `is-trunc` regarding universes.
Note that the truncation levels are defined with respect to a universe `𝒰`.
To be completely precise, we should therefore write `is-trunc{k}^{𝒰}(A)` for the type `is-trunc{k}(A)` defined with respect to the universe `𝒰`.
If `A` is also contained in a second universe `𝒱`, then it is legitimate to ask whether
```text
is-trunc{k}^{𝒰}(A)↔is-trunc{k}^{𝒱}(A).
```
A simple inductive argument shows that this is indeed the case, where the base case follows from the judgmental equalities
```text
is-trunc{-2}^{𝒰}(A) ≐ Σ(x:A) Π(y:A) x=y
is-trunc{-2}^{𝒱}(A) ≐ Σ(x:A) Π(y:A) x=y.
```
We may therefore safely omit explicit reference to the universes when considering truncatedness of a type.

<!-- rosetta-item-end: remark-12.4.2 -->

We show in the following theorem that the truncation levels are successively contained in one another.

## Proposition 12.4.3

<!-- rosetta-item: proposition-12.4.3; latex-label: thm:istrunc_next -->

If `A` is a `k`-type, then `A` is also a `(k+1)`-type.

### Proof

<!-- rosetta-item: subheading-12.4-proof -->

*Proof.* We have seen in Example 12.1.2 that contractible types are propositions.
This proves the base case.
For the inductive step, note that if any `k`-type is also a `(k+1)`-type, then any `(k+1)`-type is a `(k+2)`-type, since its identity types are `k`-types and therefore `(k+1)`-types. ◻

<!-- rosetta-item-end: proposition-12.4.3 -->

It is immediate from the proof of Proposition 12.4.3 that the identity types of `k`-types are also `k`-types.

## Corollary 12.4.4

<!-- rosetta-item: corollary-12.4.4 -->

If `A` is a `k`-type, then its identity types are also `k`-types.`□`

<!-- rosetta-item-end: corollary-12.4.4 -->

## Proposition 12.4.5

<!-- rosetta-item: proposition-12.4.5; latex-label: thm:ktype_eqv -->

If `e:A ≃ B` is an equivalence, and `B` is a `k`-type, then so is `A`.

### Proof

<!-- rosetta-item: subheading-12.4-proof-2 -->

*Proof.* We have seen in Exercise 10.3 that if `B` is contractible and `e:A ≃ B` is an equivalence, then `A` is also contractible.
This proves the base case.

For the inductive step, assume that the `k`-types are stable under equivalences, and consider `e:A ≃ B` where `B` is a `(k+1)`-type.
In Theorem 11.4.2 we have seen that
```text
ap{e}:(x = y)→(e(x) = e(y))
```
is an equivalence for any `x,y`.
Note that `e(x) = e(y)` is a `k`-type, so by the induction hypothesis it follows that `x = y` is a `k`-type.
This proves that `A` is a `(k+1)`-type. ◻

<!-- rosetta-item-end: proposition-12.4.5 -->

## Corollary 12.4.6

<!-- rosetta-item: corollary-12.4.6; latex-label: cor:emb_into_ktype -->

If `f:A→ B` is an embedding, and `B` is a `(k+1)`-type, then so is `A`.

### Proof

<!-- rosetta-item: subheading-12.4-proof-3 -->

*Proof.* By the assumption that `f` is an embedding, the action on paths
```text
ap{f}:(x = y)→ (f(x) = f(y))
```
is an equivalence for every `x,y:A`.
Since `B` is assumed to be a `(k+1)`-type, it follows that `f(x)=f(y)` is a `k`-type for every `x,y:A`.
Therefore we conclude by Proposition 12.4.5 that `x = y` is a `k`-type for every `x,y:A`.
In other words, `A` is a `(k+1)`-type. ◻

<!-- rosetta-item-end: corollary-12.4.6 -->

We end this section with a theorem that characterizes `(k+1)`-truncated maps.
Note that it generalizes Theorem 12.2.3, which asserts that a map is an embedding if and only if its fibers are propositions.

## Theorem 12.4.7

<!-- rosetta-item: theorem-12.4.7; latex-label: thm:trunc_ap -->

Let `f:A→ B` be a map.
The following are equivalent:

1.  The map `f` is `(k+1)`-truncated.

2.  For each `x,y:A`, the map
```text
ap{f} : (x=y)→ (f(x)=f(y))
```
    is `k`-truncated.

### Proof

<!-- rosetta-item: subheading-12.4-proof-4 -->

*Proof.* First we show that for any `s,t:fib(f, b)` there is an equivalence
```text
(s=t) ≃ fib(ap{f}, pr 2(s) ∙ pr 2(t)^{-1})
```
We do this by `Σ`-induction on `s` and `t`, and then we calculate
```text
((x,p)=(y,q)) ≃ Eq-fib_f((x,p),(y,q))
≐ Σ(α:x=y) p=ap_{f}(α) ∙ q
≃ Σ(α:x=y) ap_{f}(α) ∙ q=p
≃ Σ(α:x=y) ap_{f}(α)=p ∙ q^{-1}
≐ fib(ap{f}, p ∙ q^{-1}).
```
By these equivalences, it follows that if `ap{f}` is `k`-truncated, then for each `s,t:fib(f, b)` the identity type `s=t` is equivalent to a `k`-truncated type, and therefore we obtain by Proposition 12.4.5 that `f` is `(k+1)`-truncated.

For the converse, note that we have equivalences
```text
fib(ap{f}, p) ≃ ((x,p)=(y,refl)).
```
It follows that if `f` is `(k+1)`-truncated, then the identity type `(x,p)=(y,refl)` in `fib(f, f(y))` is `k`-truncated for any `p:f(x)=f(y)`.
We conclude by Proposition 12.4.5 that the fiber `fib(ap{f}, p)` is `k`-truncated. ◻

<!-- rosetta-item-end: theorem-12.4.7 -->
