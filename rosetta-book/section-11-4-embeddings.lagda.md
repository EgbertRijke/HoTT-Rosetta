# Section 11.4 Embeddings

```agda
module section-11-4-embeddings where
```

<!-- rosetta-item: section-11.4 -->

In our second application of the fundamental theorem we show that equivalences are embeddings.
The notion of embedding is the homotopical analogue of the set theoretic notion of injective map.

## Definition 11.4.1

<!-- rosetta-item: definition-11.4.1 -->

An **embedding** is a map `f:A→ B` that satisfies the property that
```text
ap{f}:(x = y)→(f(x) = f(y))
```
is an equivalence, for every `x,y:A`.
We write `is-emb(f)` for the type of witnesses that `f` is an embedding, and we define
```text
A↪ B≔ Σ(f:A→ B) is-emb(f).
```

<!-- rosetta-item-end: definition-11.4.1 -->

Another way of phrasing the following statement is that equivalent types have equivalent identity types.

## Theorem 11.4.2

<!-- rosetta-item: theorem-11.4.2; latex-label: cor:emb_equiv -->

Any equivalence is an embedding.

### Proof

<!-- rosetta-item: subheading-11.4-proof -->

*Proof.* Let `e:A ≃ B` be an equivalence, and let `x:A`.
Our goal is to show that
```text
ap{e} : (x = y)→ (e(x) = e(y))
```
is an equivalence for every `y:A`.
By Theorem 11.2.2 it suffices to show that
```text
Σ(y:A) e(x)=e(y)
```
is contractible.
Now observe that there is an equivalence

```text
Σ(y:A) e(x)=e(y) ≃ Σ(y:A) e(y)=e(x)
≐ fib(e, e(x))
```

by Theorem 11.1.3, since for each `y:A` the map
```text
inv : (e(x)=e(y))→ (e(y)= e(x))
```
is an equivalence by Exercise 9.1.
The fiber `fib(e, e(x))` is contractible by Theorem 10.4.6, so it follows by Exercise 10.3 that the type `Σ(y:A) e(x)=e(y)` is indeed contractible. ◻

<!-- rosetta-item-end: theorem-11.4.2 -->
