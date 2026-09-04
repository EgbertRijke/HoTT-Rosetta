# Section 11.1 Families of equivalences

```agda
module section-11-1-families-of-equivalences where
```

<!-- rosetta-item: section-11.1 -->

## Definition 11.1.1

<!-- rosetta-item: definition-11.1.1 -->

Consider a family of maps
```text
f : Π(x:A) B(x)→ C(x).
```
We define the map
```text
tot(f):Σ(x:A) B(x)→Σ(x:A) C(x)
```
by `λ (x,y). (x,f(x,y))`.

<!-- rosetta-item-end: definition-11.1.1 -->

## Lemma 11.1.2

<!-- rosetta-item: lemma-11.1.2; latex-label: lem:fib_total -->

For any family of maps `f:Π(x:A) B(x)→ C(x)` and any `t:Σ(x:A) C(x)`, there is an equivalence
```text
fib(tot(f), t) ≃ fib(f(pr 1(t)), pr 2(t)).
```

### Proof

<!-- rosetta-item: subheading-11.1-proof -->

*Proof.* We first define
```text
φ : Π(t:Σ(x:A) C(x)) fib(tot(f), t)→fib(f(pr 1(t)), pr 2(t))
```
by pattern matching by
```text
φ((x,f(x,y)),((x,y),refl))≔(y,refl).
```

For the proof that `φ(t)` is an equivalence, for each `t:Σ(x:A) C(x)`, we construct a map
```text
ψ(t) : fib(f(pr 1(t)), pr 2(t))→fib(tot(f), t)
```
equipped with homotopies `G(t):φ(t)∘ψ(t)~id` and `H(t):ψ(t)∘φ(t)~id`.
Each of these definitions is given by pattern matching, as follows:
```text
ψ((x,f(x,y)),(y,refl)) ≔ ((x,y),refl)
G((x,f(x,y)),(y,refl)) ≔ refl
H((x,f(x,y)),((x,y),refl)) ≔ refl.
```
 ◻

<!-- rosetta-item-end: lemma-11.1.2 -->

## Theorem 11.1.3

<!-- rosetta-item: theorem-11.1.3; latex-label: thm:fib_equiv -->

Let `f:Π(x:A) B(x)→ C(x)` be a family of maps.
The following are equivalent:

1.  For each `x:A`, the map `f(x)` is an equivalence.
In this case we say that `f` is a **family of equivalences**.

2.  The map `tot(f):Σ(x:A) B(x)→Σ(x:A) C(x)` is an equivalence.

### Proof

<!-- rosetta-item: subheading-11.1-proof-2 -->

*Proof.* By Theorems 10.3.5 and 10.4.6 it suffices to show that `f(x)` is a contractible map for each `x:A`, if and only if `tot(f)` is a contractible map.
Thus, we will show that `fib(f(x), c)` is contractible if and only if `fib(tot(f), x,c)` is contractible, for each `x:A` and `c:C(x)`.
However, by Lemma 11.1.2 these types are equivalent, so the result follows by Exercise 10.3. ◻

<!-- rosetta-item-end: theorem-11.1.3 -->

Now consider the situation where we have a map `f:A→ B`, and a family `C` over `B`.
Then we have the map
```text
λ (x,z). (f(x),z):Σ(x:A) C(f(x))→Σ(y:B) C(y).
```
We claim that this map is an equivalence when `f` is an equivalence.
The technique to prove this claim is the same as the technique we used in Theorem 11.1.3: first we note that the fibers are equivalent to the fibers of `f`, and then we use the fact that a map is an equivalence if and only if its fibers are contractible to finish the proof.

The converse of the following lemma does not hold.
Why not?

## Lemma 11.1.4

<!-- rosetta-item: lemma-11.1.4; latex-label: lem:total-equiv-base-equiv -->

Consider a map `f:A→ B`, and let `C` be a type family over `B`.
If `f` is an equivalence, then the map
```text
σ_f(C) ≔λ (x,z). (f(x),z):Σ(x:A) C(f(x))→Σ(y:B) C(y)
```
is an equivalence.

### Proof

<!-- rosetta-item: subheading-11.1-proof-3 -->

*Proof.* We claim that for each `t:Σ(y:B) C(y)` there is an equivalence
```text
fib(σ_f(C), t)≃ fib(f, pr 1(t)).
```
We obtain such an equivalence by constructing the following functions and homotopies:
```text
φ(t) : fib(σ_f(C), t)→fib(f, pr 1 (t)) φ((f(x),z),((x,z),refl)) ≔ (x,refl)
ψ(t) : fib(f, pr 1(t)) →fib(σ_f(C), t) ψ((f(x),z),(x,refl)) ≔ ((x,z),refl)
G(t) : φ(t)∘ψ(t)~id G((f(x),z),(x,refl)) ≔ refl
H(t) : ψ(t)∘φ(t)~id H((f(x),z),((x,z),refl)) ≔ refl.
```
Now the claim follows, since we see that `φ` is a contractible map if and only if `f` is a contractible map. ◻

<!-- rosetta-item-end: lemma-11.1.4 -->

Now we use Lemma 11.1.4 to obtain a generalization of Theorem 11.1.3.

## Definition 11.1.5

<!-- rosetta-item: definition-11.1.5; latex-label: defn:toto -->

Consider a map `f:A→ B` and a family of maps
```text
g:Π(x:A) C(x)→ D(f(x)),
```
where `C` is a type family over `A`, and `D` is a type family over `B`.
In this situation we also say that `g` is a **family of maps over `f`**.
Then we define
```text
tot([f]{g}:Σ(x:A) C(x)→Σ(y:B) D(y)
```
by `tot([f]{g}(x,z)≔ (f(x),g(x,z))`.

<!-- rosetta-item-end: definition-11.1.5 -->

## Theorem 11.1.6

<!-- rosetta-item: theorem-11.1.6; latex-label: thm:equiv-toto -->

Suppose that `g` is a family of maps over `f` as in Definition 11.1.5, and suppose that `f` is an equivalence.
Then the following are equivalent:

1.  The family of maps `g` over `f` is a family of equivalences.

2.  The map `tot([f]{g}` is an equivalence.

### Proof

<!-- rosetta-item: subheading-11.1-proof-4 -->

*Proof.* Note that we have a commuting triangle
<!-- rosetta-diagram: 7fd1a4418fd2; review: pending -->

*Triangle-shaped diagram (automatic draft).*

```text
[Σ(x:A) C(x)]                          [Σ(y:B) D(y)]

                  [Σ(x:A) D(f(x))]

Arrows:
- Σ(x:A) C(x) --{tot([f]{g}}--> Σ(y:B) D(y)
- Σ(x:A) C(x) --tot(g)--> Σ(x:A) D(f(x))
- Σ(x:A) D(f(x)) --{λ (x,z). (f(x),z)}--> Σ(y:B) D(y)
```
By the assumption that `f` is an equivalence, it follows that the map
```text
Σ(x:A) D(f(x))→ Σ(y:B) D(y)
```
is an equivalence.
Therefore it follows that `tot([f]{g}` is an equivalence if and only if `tot(g)` is an equivalence.
Now the claim follows, since `tot(g)` is an equivalence if and only if `g` if a family of equivalences. ◻

<!-- rosetta-item-end: theorem-11.1.6 -->
