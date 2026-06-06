# Section 6.4 Peano's seventh and eighth axioms

```agda
module section-6-4-peanos-seventh-and-eighth-axioms where
```

Using the observational equality of `ℕ`, we can prove Peano's seventh and
eighth axioms.
In his *Arithmetices Principia*, the natural numbers are based at `1`, but today
it is customary to have the natural numbers based at `0`.
Adapting for this, the seventh and eighth axioms assert that

1. For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ (succ(m) = succ(n)).
```

2. For any natural number `n`, we have `0 ≠ succ(n)`.

## Theorem 6.4.1

For any two natural numbers `m` and `n`, we have

```text
  (m = n) ↔ (succ(m) = succ(n)).
```

## Proof

The forward implication is given by the action on paths of the successor
function

```text
  ap_succ : (m = n) → (succ(m) = succ(n)).
```

The direction of interest is the converse, which asserts that the successor
function is injective.

Here we use the proposition that `(m = n) ↔ EqN(m, n)` for all `m, n : ℕ`.
Furthermore, we have `EqN(succ(m), succ(n)) ≐ EqN(m, n)`.
Therefore, we define the function `(succ(m) = succ(n)) → (m = n)` as the
composite of the maps

```text
  (succ(m) = succ(n)) → EqN(succ(m), succ(n)) →
  EqN(m, n) → (m = n).
```

## Theorem 6.4.2

For any natural number `n`, we have `0 ≠ succ(n)`.

## Proof

By the proposition that `(m = n) ↔ EqN(m, n)`, it follows that there is a family
of maps

```text
  (0 = n) → EqN(0, n)
```

indexed by `n : ℕ`.
Since `EqN(0, succ(n)) ≐ ∅` it follows that

```text
  (0 = succ(n)) → ∅,
```

which is precisely the claim.
