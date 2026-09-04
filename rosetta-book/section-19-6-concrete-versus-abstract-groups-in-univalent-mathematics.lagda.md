# Section 19.6 Concrete versus abstract groups in univalent mathematics

```agda
module section-19-6-concrete-versus-abstract-groups-in-univalent-mathematics where
```

<!-- rosetta-item: section-19.6 -->

In univalent mathematics there is another exciting perspective on group theory.
We won’t be able to go in full details here, but we can sketch some of key ideas.
To learn more about this beautiful univalent perspective on group theory, I recommend the forthcoming *Symmetry* book .

We saw in Example 19.4.3 that for every pointed connected `1`-type `X` we obtain a group with underlying type `Ω(X)`.
All groups can be constructed in this way.
In fact, for every group `G` in `𝒰` the type
```text
Σ(B:Pointed-Connected-1-Type_𝒰) G≅Ω(B)
```
of pointed connected `1`-types `B` equipped with a group isomorphism from `G` to `Ω(B)` is contractible.
We write `BG` for the unique pointed connected `1`-type whose loop space is isomorphic to `G`.
The pointed type `BG` is also called the **delooping** of `G`, or the **classifying type** of `G`.
The fact that the above type is contractible is of course heavily reliant on the univalence axiom.

## Example 19.6.1

<!-- rosetta-item: example-19.6.1 -->

We have already seen that
```text
S_n≅Ω(BS_n),
```
i.e., that the loop space of the type of all finite types of cardinality `n` is equivalent to the symmetric group `S_n`.
The type `BS_n` is of course a pointed connected `1`-type, so `BS_n` is indeed the classifying type of the symmetric group `S_n`.

<!-- rosetta-item-end: example-19.6.1 -->

Since the map
```text
Ω:Pointed-Connected-1-Type_𝒰→Group_𝒰
```
is an equivalence, we obtain two perspectives on the type of all groups.
The elements of the type `Group_𝒰` are groups according to the traditional definition of groups.
We call such groups **abstract groups**.
On the other hand, pointed connected `1`-types `B` are **concrete groups** in the sense that the contain an object `⋆:B`, and the group `B` represents is the group of self-identifications (i.e., symmetries) of the base point `⋆:B`.
Thus we see that when we present a group as a pointed connected `1`-type, then we *concretely* manifest that group as the group of symmetries of some object.

We can also bring group homomorphisms into the mix: for every group homomorphism `f:G→ H` the type of pointed maps `b:BG→_⋆ BH` equipped with a homotopy witnessing
<!-- rosetta-diagram: cbfa1902bf39; review: pending -->

*Square-shaped diagram (automatic draft).*

```text
  [G]  ---->  [H]
   |           |
[Ω(BG)]---->[Ω(BH)]

Arrows:
- G --≅--> Ω(BG)
- G --f--> H
- H --≅--> Ω(BH)
- Ω(BG) --Ω(b)--> Ω(BH)
```
commutes is contractible.
In other words, every group homomorphism `f:G→ H` has a unique **delooping** `Bf:BG→ BH`.

We can do all of group theory in this way.
For example, traditionally a `G`-set is defined to be a set `X` equipped with a group homomorphism `G→Aut(X)`.
That is, the type of **abstract `G`-sets** is defined to be
```text
G-Set_𝒰≔Σ(X:Set_𝒰) hom(G,Aut(X)).
```
However, this definition is equivalent to family `X:BG→Set_𝒰` of sets indexed by the classifying type `BG`.
Therefore we define **concrete `G`-sets** to be type families `X:BG→Set_𝒰`.
Given a concrete `G`-set `X:BG→Set_𝒰`, the set being acted upon is the set `X(⋆)`, and the action of `G` on `X(⋆)` is given by transport, since the elements of `G` are equivalent to loops in `BG`.

The type of **orbits** of a concrete `G`-set `X:BG→Set_𝒰` can then be defined as
```text
X/G≔ Σ(u:BG) X(u)
```
and the type of **fixed points** of `X` can be defined as
```text
X_G≔ Π(u:BG) X(u).
```
To see that these definitions make sense, note that the fiber inclusion `X(⋆)→ X/G` maps each element in the `G`-set `X` to its orbit.
The fiber inclusion is surjective by Exercise 18.5, and it maps two elements `x,y:X(⋆)` to the same orbit precisely when there is a group element `g` such that `gx=y`.
Similarly, for the type of fixed points notice that each `x:X_G` determines an element `x_⋆:X(⋆)`, which comes equipped with an identification
```text
apd_{x}(g):gx_⋆=x_⋆
```
since the group action of `G` on `X` is given by transport.

Also, notice that a subgroup `H` of `G` determines an inclusion homomorphism `i:H→ G`, and this inclusion function corresponds uniquely to a pointed map `Bi:BG→ BH`.
Since `Ω(Bi)` is an embedding, we note that `Bi` must be a `0`-truncated map.
Therefore, a concrete subgroup of a concrete group `BG` is defined to be a concrete `G`-set `X` such that the type of orbits is connected.
Such concrete `G`-sets are called **transitive**.

Dually, we say that a concrete `G`-set `X` is **free** if the type of orbits `X/G` is a set.
To see that this definition makes sense, we use the following generalization of the fundamental theorem of identity types:

## Theorem 19.6.2

<!-- rosetta-item: theorem-19.6.2; latex-label: thm:truncated-fundamental -->

Consider a connected type `A` equipped with an element `a:A`, and consider a family of types `B(x)` indexed by `x:A`.
Then the following are equivalent:

1.  Every family of maps
```text
f:Π(x:A) (a=x)→ B(x)
```
    is a family of `k`-truncated maps.

2.  The total space
```text
Σ(x:A) B(x)
```
    is `(k+1)`-truncated.

### Proof

<!-- rosetta-item: subheading-19.6-proof -->

*Proof.* Recall from Exercise 12.10 that the total space `Σ(x:A) B(x)` is `(k+1)`-truncated if and only if the base point inclusion
```text
(x,y):unit→Σ(x:A) B(x)
```
is `k`-truncated for every `(x,y):Σ(x:A) B(x)`.
Since the type `A` is assumed to be connected, this is equivalent to the condition that every base point inclusion of the form
```text
(a,y):unit→Σ(x:A) B(x)
```
is `k`-truncated.
Base point inclusions of this form are homotopic to `tot(f)`, where
```text
f:Π(x:A) (a=x)→ B(x)
```
is given by `f(a,refl)≔ y`.
The condition that `tot(f)` is `k`-truncated is by Lemma 11.1.2 equivalent to the condition that `f` is a family of `k`-truncated maps.
Furthermore, every family of maps `f:Π(x:A) (a=x)→ B(x)` is of the above form by the type theoretic Yoneda lemma (Theorem 13.3.3), completing the proof. ◻

<!-- rosetta-item-end: theorem-19.6.2 -->

By the previous theorem it follows that if the type of orbits of a concrete `G`-set `X` is a set, then the map `g↦ gx` must be an embedding for every `x:X(⋆)`.
In other words, the action of `G` on `X` is free.

## Remark 19.6.3

<!-- rosetta-item: remark-19.6.3 -->

Theorem 19.6.2 can be generalized further.
We include this generalization in Exercise 19.14.

<!-- rosetta-item-end: remark-19.6.3 -->

## Example 19.6.4

<!-- rosetta-item: example-19.6.4 -->

Consider two sets `A` and `B`, and a universe `𝒰` containing both of them.
Then the automorphism group `Aut(B)` acts on the decidable embeddings `B↪ᵈ A` by precomposition.
Its type of orbits is the binomial type
```text
binom(A, B)≔Σ(X:𝒰_B) X↪ᵈ A,
```
which we introduced in Definition 17.6.4.
By Proposition 17.6.6 it follows that `binom(A, B)` is a set, so the action of `Aut(B)` on `B↪ᵈ A` is free.
Note that we didn’t need to assume that `A` and `B` are sets: the action of `Aut(B)` on `B↪ᵈ A` is always free.

Similarly, we have an action of the automorphism group `Aut(B)` on the surjective maps `A↠ B` by postcomposition.
Its type of orbits is the stirling type of the second kind
```text
Stirling(A, B)≔Σ(X:𝒰_B) A↠ X,
```
which we introduced in Exercise 18.13.
Assuming that `B` is a set, it was shown in Exercise 18.13 that `Stirling(A, B)` is a set.
In other words, the action of `Aut(B)` on `A↠ B` is free.

<!-- rosetta-item-end: example-19.6.4 -->

## Example 19.6.5

<!-- rosetta-item: example-19.6.5 -->

In Exercise 17.20 we introduced the type
```text
D̃_n≔ Σ(X:BS_2) Σ(Y:X→𝔽) (Fin{n}≃Π(x:X) Y(x)).
```
Notice that this type is the type of orbits of the `ℤ/2`-set `D_n` given by
```text
D_n(X)≔ Σ(Y:X→𝔽) (Fin{n}≃Π(x:X) Y(x)).
```
The fact that this is a family of sets is a nice exercise.
Note that there is a surjective morphism of `ℤ/2`-sets from `D_n(Fin{2})` to the `ℤ/2` set of divisors of `n`, where the action is given by `d↦ n/d`.
The concrete `ℤ/2`-action `D_n` is transitive precisely when `n` is either `1` or a prime, and it is is free precisely when `n` is not a square.
Combining these two observations, we see that `n` is prime if and only if this action is both transitive and free.
In other words, `n` is prime if and only if the type `D̃_n` of orbits is contractible.

<!-- rosetta-item-end: example-19.6.5 -->

`G`-sets which are both transitive and free are very special.
Such `G`-sets are called **`G`-torsors**.
Note that a `G`-set `X` is a `G`-torsor if and only if the type of orbits `X/G` is contractible.
By the fundamental theorem of identity types, this implies that the family of maps
```text
Π(v:BG) (u=v)→ X(v)
```
is a family of equivalences, where `(u,x)` is the center of contraction of `X/G`.
It follows that a concrete `G`-set `X:BG→Set_𝒰` is a `G`-torsor if and only if it is in the image of
```text
Id_ : BG→ (BG→ Set_𝒰).
```
However, we know from Exercise 17.6 that this map is an embedding, so it follows that the type of concrete `G`-torsors is equivalent to `BG`.
On the other hand, the type of concrete `G`-torsors is equivalent to the type of abstract `G`-torsors.
This suggests that the classifying type `BG` of any group `G` can be constructed as the type of abstract `G`-torsors, and this is indeed one way to construct the classifying type of a group `G`.
