# Section 20.3 Functoriality of W-types

```agda
module section-20-3-functoriality-of-w-types where
```

<!-- rosetta-item: section-20.3 -->

## Definition 20.3.1

<!-- rosetta-item: definition-20.3.1 -->

Consider a type family `B` over `A`, and a type family `B'` over `A'`.
Furthermore, consider a map `f:A'→ A` and a family of equivalences
```text
e_x:B'(x)≃ B(f(x))
```
indexed by `x:A'`.
Then we define the map `W(f,e):W(A',B')→W(A,B)` of W-types inductively by
```text
W(f,e)(tree(x,α))≔tree(f(x),W(f,g)∘ α∘ e_x^{-1}).
```

<!-- rosetta-item-end: definition-20.3.1 -->

## Lemma 20.3.2

<!-- rosetta-item: lemma-20.3.2; latex-label: lem:fib-W -->

For any morphism `W(f,e):W(A',B')→W(A,B)` of W-types and any `tree(x,α):W(A,B)`, there is an equivalence
```text
fib(W(f,e), tree(x,α)) ≃ fib(f, x)×Π(b:B(x)) fib(W(f,e), α(b)).
```

### Proof

<!-- rosetta-item: subheading-20.3-proof -->

*Proof.* First, note that by the characterization in Theorem 20.2.3 of the identity type of `W(A,B)`, there is an equivalence between the fiber `fib(W(f,e), tree(x,α))` and the type
```text
Σ(x':A') Σ(α':B'(x')→W(A',B')) Σ(p:f(x')=x)
Σ(x':A') Π(b:B(f(x'))) W(f,e)(α'(e_{x'}^{-1}(b)))=α(tr_{B}(p,b)).
```

By rearranging the `Σ`-type, we see that this type is equivalent to the type

```text
Σ((x',p):fib(f, x)) Σ(α':B'(x')→W(A',B'))
Σ(x':A') Π(b:B(f(x'))) W(f,e)(α'(e_{x'}^{-1}(b)))=α(tr_{B}(p,b)).
```
Therefore, it suffices to show for each `(x',p):fib(f, x)`, that the type
```text
Σ(α':B'(x')→W(A',B')) Π(b:B(f(x'))) W(f,e)(α'(e_{x'}^{-1}(b)))=α(tr_{B}(p,b))
```
is equivalent to the type `Π(b:B(x)) fib(W(f,e), α(b))`.
Since we have an identification `p:f(x')=x` and an equivalence `e_{x'}:B'(x')≃ B(f(x'))`, it follows that the type above is equivalent to the type
```text
Σ(α':B(x)→W(A',B')) Π(b:B(x)) W(f,e)(α'(b))=α(b).
```
By distributivity of `Π` over `Σ`, i.e., by Theorem 13.2.1, this type is equivalent to the type
```text
Π(b:B(x)) Σ(w:W(A',B')) W(f,e)(w)=α(b),
```
completing the proof. ◻

<!-- rosetta-item-end: lemma-20.3.2 -->

## Theorem 20.3.3

<!-- rosetta-item: theorem-20.3.3 -->

Consider a morphism `W(f,e):W(A,B)→W(A',B')` of W-types.
If the map `f:A→ A'` is `k`-truncated, then so is the map `W(f,e)`.
In particular, if `f` is an equivalence or an embedding, then so is `W(f,e)`.

### Proof

<!-- rosetta-item: subheading-20.3-proof-2 -->

*Proof.* Suppose that the map `f` is `k`-truncated.
We will prove recursively that the fibers of the morphism `W(f,e)` on W-types is `k`-truncated.
We saw in Lemma 20.3.2 that there is an equivalence
```text
fib(W(f,e), tree(x,α))≃ fib(f, x)×Π(b:B(x)) fib(W(f,e), α(b)).
```
The type `fib(f, x)` is `k`-truncated by assumption, and each of the types
```text
fib(W(f,e), α(b))
```
is `k`-truncated by the inductive hypothesis, so the claim follows. ◻

<!-- rosetta-item-end: theorem-20.3.3 -->
