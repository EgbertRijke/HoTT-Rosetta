# Agda training exercises

These are later Agda blocks left empty because they need auxiliary mathematics
absent from otherwise complete earlier files.

An exercise site contains an empty fence:

````text
```agda
```
````

For each exercise, record:

- a stable name;
- the file and mathematical location;
- the result to prove;
- the absent auxiliary result;
- why the earlier file should remain unchanged;
- every later result that needs it;
- the matching entry in `docs/invisible-math.md`.
- the proposal branch, solution commit, and review state.

The exercise belongs where the absent result first blocks formalization. The
invisible-math entry names the result's natural mathematical home.

Every exercise has a solution on `proposal/agda-exercise-solutions`. Create and
publish this branch from current `main` when the first exercise appears. Agents
must make one focused solution commit, validate and push it, then record its
commit here on `main`. Before each solution, they must bring current `main`
into the proposal without rewriting public history. The proposal is never
merged automatically.

These steps bind agents only. Humans may edit either branch freely.

## Exercises

### `definition-10.2.1-singleton-induction`

- **Place:** Section 10.2, Definition 10.2.1.
- **Task:** Formalize singleton induction and its computation rule.
- **Absent result:** Evaluation at a point, `ev-point`.
- **Reason:** Section 2.2 already gives a complete account of ordinary
  functions and typechecks. It should not grow solely to support Section 10.2.
- **Later use:** Theorem 10.2.3.
- **Invisible mathematics:** “Section 10.2: evaluation at a point” in
  `docs/invisible-math.md`.
- **Status:** Recorded; the current Agda block has not yet been emptied.
- **Proposal solution:** Not yet made.
