# Section 18.4 Unique representatives of equivalence classes

```agda
module section-18-4-unique-representatives-of-equivalence-classes where
```

<!-- rosetta-item: section-18.4 -->

A common way to construct set quotients is by showing that the equivalence classes of an equivalence relation have a choice of unique representatives.
In this section we show that if there is a choice of unique representatives, then the set quotient can be constructed as the type of those representatives.
An important reason to define set quotients as the type of canonical representatives, if that is possible, is that the universe level of the set quotient can be kept as low as possible without needing to appeal to the replacement axiom.

## Definition 18.4.1

<!-- rosetta-item: definition-18.4.1 -->

Consider an equivalence relation `R` on a type `A`, and consider a family of types `C(x)` indexed by `x:A`.
We say that `C` is a **choice of (unique) representatives** of the equivalence classes of `R` if `C` comes equipped with an element of type
```text
is-choice-of-reps(C) ≔ Π(x:A) is-contr(Σ(y:A) C(y)× R(x,y)).
```

<!-- rosetta-item-end: definition-18.4.1 -->

## Theorem 18.4.2

<!-- rosetta-item: theorem-18.4.2; latex-label: thm:choice-of-representatives -->

Consider an equivalence relation `R` on a type `A`, and let `C` be a choice of representatives of the equivalence classes of `R`, with `(h(x),c(x),r(x))` at the center of contraction of `Σ(y:A) C(y)× R(x,y)`.
Then the map
```text
q:A→Σ(x:A) C(x)
```
given by `q(x)≔(h(x),c(x))` is a map into a set such that `q(x)=q(y)` for every `x,y:A` such that `R(x,y)` holds, and moreover `q` satisfies the universal property of the set quotient of `A` by `R`.

### Proof

<!-- rosetta-item: subheading-18.4-proof -->

*Proof.* First, we will use Theorem 12.3.4 to show that the type `Σ(y:A) C(y)` is a set, such that
```text
((x,c)=(y,d))≃ R(x,y)
```
for any `(x,c)` and `(y,d)` in `Σ(y:A) C(y)`.
Note that we have a function
```text
R(x,y)→ ((x,c)=(y,d)),
```
since for any `r:R(x,y)` both `(x,c,r)` and `(y,d,r)` are elements of the contractible type `{Σ(y:A) C(y)× R(x,y)}`.
Since `R` is a reflexive relation valued in propositions, the claim follows.
In particular, it follows that
```text
(q(x)=q(y))≃ R(x,y)
```
for any `x,y:A`, i.e., `q` is effective.

To prove the universal property of set quotients, note that by characterization (2) in Theorem 18.2.3 it suffices to show that `q` is surjective and effective.
We have already shown above that `q` is effective, so it remains to show that `q` is surjective.
In fact, we will prove the stronger claim that the projection map
```text
pr 1:Σ(x:A) C(x)→ A
```
is a section of `q`.
Let `x:A` and `c:C(x)`.
Then `(x,c,ρ(x))` is an element of the type
```text
Σ(y:A) C(y)× R(x,y),
```
which is contractible with center of contraction `(h(x),c(x),r(x))`.
Therefore it follows that `q(x)≐ (h(x),c(x))=(x,c)`.
In particular, we see that `q(pr 1(x,c))=(x,c)`, i.e., that `pr 1` is a section of `q`. ◻

<!-- rosetta-item-end: theorem-18.4.2 -->

## Example 18.4.3

<!-- rosetta-item: example-18.4.3 -->

In Proposition 7.2.4 we constructed the congruence relations `x≡ y mod k` on the natural numbers for every natural number `k`, and in Theorems 7.4.7 and 7.4.8 we showed that the map
```text
x↦ [x]_{k+1}:ℕ→Fin{k+1}
```
is effective and split surjective.
By Theorem 18.2.3 it follows that the map
```text
x↦ [x]_{k+1}:ℕ→Fin{k+1}
```
satisfies the universal property of the set quotient of the equivalence relation `x,y↦ x≡ ymod k+1`.

We also claim that there is a choice of representatives of the congruence relations.
We define our choice of representatives by
```text
C(y)≔ fib(nat-Fin, y),
```
where `nat-Fin:Fin{k+1}→ℕ` is the inclusion of `Fin{k+1}` into `ℕ` constructed in Definition 7.3.4.
To see that `C` is a choice of representatives, we have to prove that
```text
Σ(y:ℕ) C(y)× (x≡ ymod k+1)
```
is contractible for each `x:ℕ`.
At the center of contraction we have the triple `(nat-Fin([x]_{k+1}),([x]_{k+1},refl),p)` where `p:x≡nat-Fin([x]_{k+1})mod k+1` is the proof obtained via Theorems 7.4.7 and 7.4.8.
In order to construct the contraction, note that both `C(y)` and `x≡ ymod k+1` are propositions for each `y:ℕ`.
Therefore it suffices to prove that for any `y:ℕ` such that `C(y)` and `x≡ ymod k+1` hold, we have
```text
nat-Fin([x]_{k+1})=y.
```
Since `C(y)` holds, we see that `y=nat-Fin([y]_{k+1})`.
Therefore it suffices to prove that `[x]_{k+1}=[y]_{k+1}`.
This follows from Theorem 7.4.7, since we assumed `x≡ ymod k+1`.

<!-- rosetta-item-end: example-18.4.3 -->

## Example 18.4.4

<!-- rosetta-item: example-18.4.4 -->

Consider the type of **(integer) fractions**
```text
Q≔ ℤ×Σ(y:ℤ) y≠ 0.
```
We define an equivalence relation on `Q` by
```text
((x,y)~ (x',y'))≔ (xy'=x'y).
```
This equivalence relation has a choice of representatives defined by
```text
C(x,y)≔ (y>0)∧ (gcd(x,y)=1).
```
In other words, we say that `(x,y)` is a **reduced fraction** if `y>0` and `x` and `y` are coprime.

To see that `C` defines a choice of unique representatives, we first need to construct the center of contraction of
```text
Σ(q:Q) C(q)× ((x,y)~ q).
```
Note that if `y<0` then `(x,y)~ (-x,-y)`, and we have `-y>0`.
It is therefore safe to assume that `y>0`.
We claim that
```text
(x/gcd(x,y),y/gcd(x,y)):Q
```
satisfies `C` and is equivalent to `(x,y)`.
It is immediate that `y/gcd(x,y)>0` and that `(x,y)~(x/gcd(x,y),y/gcd(x,y))`.
The fact that `x/gcd(x,y)` and `y/gcd(x,y)` are coprime follows from the fact that
```text
gcd(x/d,y/d)=gcd(x,y)/d
```
for any common divisor `d` of `x` and `y`.

To construct a contraction, let `(x',y'):Q` such that `C(x',y')` and `(x,y)~ (x',y')`.
Since `C(q)` and `(x,y)~ q` are propositions for every `q:Q` it suffices to show that
```text
x'=x/gcd(x,y) and y'=y/gcd(x,y).
```
Since `x'` and `y'` are assumed to be coprime, it follows from the equation
```text
x'y/gcd(x,y)=xy'/gcd(x,y)
```
that `x'` divides `x/gcd(x,y)`.
Similarly `x/gcd(x,y)` and `y/gcd(x,y)` are coprime, it follows from the same equation that `x/gcd(x,y)` divides `x'`, so we conclude that `ux'=x/gcd(x,y)` for some `u=± 1`.
The fact that `vy'=y/gcd(x,y)` for some `v=± 1` is proven similarly.
However, since both `y` and `y'` are positive, and the `gcd(x,y)` of any two integers is positive, it follows that `v=1`.
Using the assumption that `x'y/gcd(x,y)=xy'/gcd(x,y)`, this allows us to deduce that also `u=1`.

We define the type of **rational numbers** by
```text
ℚ≔ Σ((x,y):Q) (y>0)∧ gcd(x,y)=1,
```
and we define the quotient map `(x,y)↦ x/y:Q→ ℚ` to be the quotient map `q` in Theorem 18.4.2.
By Theorem 18.4.2 it also follows that `(x,y)↦ x/y` satisfies the universal property of the set quotient of the equivalence relation `~` on `Q`.

<!-- rosetta-item-end: example-18.4.4 -->
