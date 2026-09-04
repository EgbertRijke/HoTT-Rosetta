# Section 18.3 Partitions

```agda
module section-18-3-partitions where
```

<!-- rosetta-item: section-18.3 -->

There are many equivalent ways of stating what an equivalence relation is.
We saw in Theorem 18.2.5 that the type of equivalence relations on `A` is equivalent to the type of surjective maps out of `A` into a set.
Here we will show that the type of equivalence relations on `A` is equivalent to the type of partitions of `A`.
Another type that is equivalent to the type of equivalence relations of `A` is the type of set-indexed `Σ`-decompositions of `A`, i.e., the type of triples `(X,Y,e)` consisting of a set `X`, a family `Y` of inhabited types indexed by `X`, and an equivalence `e:A≃ Σ(x:X) Y(x)`.
The fact that the type of equivalence relations on `A` is equivalent to the type of set-indexed `Σ`-decompositions of `A` is stated as Exercise 18.4

In this section we show that equivalence relations on `A` are partitions of `A`.
Recall that the type of inhabited subtypes of `A` is defined to be
```text
P_{U}^+(A)≔Σ(Q:A→Prop_𝒰) ‖Σ(a:A) Q(a)‖.
```
The equivalence of equivalence relations and partitions requires some finesse regarding universes.
This is why we set up the definition of partitions in the following way.

## Definition 18.3.1

<!-- rosetta-item: definition-18.3.1 -->

Let `A` be a type and let `𝒰` and `𝒱` be two universes.
A **`(𝒰,𝒱)`-partition** of a type `A` is a subset
```text
P:P_{𝒰}^+(A)→Prop_{𝒱}
```
of the type of inhabited subsets of `A` such that for each `x:A` there is a unique inhabited subset `Q` of `A` in `P` that contains `x`, i.e., if it comes equipped with an element of type
```text
is-partition(P):=Π(x:A) is-contr(Σ(Q:P_{𝒰}^+(A)) P(Q)× Q(x))
```
The type of all `(𝒰,𝒱)`-partitions of `A` is defined by
```text
Partition_{𝒰,𝒱}(A)≔Σ(P:P_{𝒰}^+(A)→Prop_{𝒱}) is-partition(P)
```

<!-- rosetta-item-end: definition-18.3.1 -->

## Theorem 18.3.2

<!-- rosetta-item: theorem-18.3.2 -->

Consider a type `A`, a universe `𝒰`, and consider a universe `𝒱` containing both `A` and every type in `𝒰`.
Then we have an equivalence
```text
Eq-Rel_{𝒰}(A)≃Partition_{𝒰,𝒱}(A).
```

### Proof

<!-- rosetta-item: subheading-18.3-proof -->

*Proof.* Consider an equivalence relation `R` on `A`.
Then we define
```text
P:P_{𝒰}^+(A)→Prop_𝒱
```
by `P(Q)≔∃_{(x:A)}∀_{(y:A)}Q(y)↔ R(x,y)`.
In other words, `P` is the subtype of equivalence classes of `R`, which are all inhabited.
To show that `P` is a partition of `A`, let `x:A`.
The type
```text
Σ(Q:P_{𝒰}^+(A)) P(Q)× Q(x)
```
is equivalent to the type
```text
Σ(Q:P_{𝒰}^+(A)) Π(y:A) Q(y)↔ R(x,y)
```
since the proposition `∃_{(z:A)}∀_{(y:A)}Q(y)↔ R(z,y)` is equivalent to the type `Π(y:A) Q(y)↔ R(x,y)`, given an element `q:Q(x)`.
By univalence it follows that the latter type is equivalent to the identity type `Q=R(x)` in `P_{𝒰}^+(A)`, so the total space is contractible.
Thus we obtain a map
```text
ψ:Eq-Rel_{U}(A)→Partition_{𝒰,𝒱}(A).
```

For the converse map, we first define for any `(𝒰,𝒱)`-partition `P` of `A` a binary relation `R_P` such that `R_P(x)` is at the center of contraction in the type
```text
Σ(Q:P^+_{U}(A)) P(Q)× Q(x).
```
In other words, `R_P(x)` is defined to be the unique block in the partition `P` such that `R_P(x,x)` holds.
It is immediate from its definition that `R_P(x,y)` is a proposition in `𝒰`.
To see that `R_P` is symmetric, note that if `R_P(x,y)` holds, then `R_P(x)` is an element of type
```text
Σ(Q:P^+_{U}(A)) P(Q)× Q(y).
```
By contractibility, this implies that `R(x)=R(y)`, from which we obtain that `R(y,x)` holds.
To see that `R_P` is transitive we observe similarly that if `R(x,y)` and `R(y,z)` hold, then we have an identification `R(x)=R(y)` and it follows that `R(x,z)` holds.
Thus we obtain a map
```text
φ:Partition_{𝒰,𝒱}(A)→Eq-Rel_{𝒰}(A).
```
It remains to prove that the maps `ψ` and `φ` are inverse to each other, first let `R` be an equivalence relation.
In order to show that `φ(ψ(R))=R` it suffices by univalence to show that the equivalence relation obtained from the partition induced by `R` is given by
```text
R'(x,y):=Σ(Q:P_{𝒰}^+(A)) (∃_{(u:A)}∀_{(v:A)}Q(v)↔ R(u,v))× Q(x)× Q(y).
```
is equivalent to `R`.
Observe that the proposition `R'(x,y)` is equivalent to `R(x,x)× R(x,y)`, which is equivalent to `R(x,y)`.
This shows that the composite
<!-- rosetta-diagram: d27d97483dac; review: pending -->

*Linear diagram (automatic draft).*

```text
[Eq-Rel_{𝒰}(A)]---->[Partition_{𝒰,𝒱}(A)]---->[Eq-Rel_{𝒰}(A)]

Arrows:
- Eq-Rel_{𝒰}(A) --ψ--> Partition_{𝒰,𝒱}(A)
- Partition_{𝒰,𝒱}(A) --φ--> Eq-Rel_{𝒰}(A)
```
is homotopic to the identity function.

Finally, we have to show that for any partition `P` of `A` and any inhabited subtype `Q` of `A` we have `ψ(φ(P))(Q)↔ P(Q)`.
Note that this is a proposition, so we may assume an element `x:A` such that `Q(x)` holds.
By univalence it follows that `ψ(φ(P))(Q)` holds if and only if `Q=R_P(x)`, where `R_P` is the equivalence relation constructed in the definition of the map `φ`.
Now we see that `P(Q)` holds if and only if `Q` is in the contractible type
```text
Σ(Q':P^+_{U}(A)) P(Q')× Q'(x),
```
which is the case if and only if `Q=R_P(x)`.
This shows that the composite
<!-- rosetta-diagram: d4e1aa380edc; review: pending -->

*Linear diagram (automatic draft).*

```text
[Partition_{𝒰,𝒱}(A)]---->[Eq-Rel_{𝒰}(A)]---->[Partition_{𝒰,𝒱}(A)]

Arrows:
- Partition_{𝒰,𝒱}(A) --φ--> Eq-Rel_{𝒰}(A)
- Eq-Rel_{𝒰}(A) --ψ--> Partition_{𝒰,𝒱}(A)
```
is homotopic to the identity function. ◻

<!-- rosetta-item-end: theorem-18.3.2 -->
