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

The exercise belongs where the absent result first blocks formalization. The
invisible-math entry names the result's natural mathematical home.

Count entries by chapter. At 15, keep this version and make a separate proposal
branch with the missing pinned blocks placed where they fit best. Validate and
report that alternative. Do not merge or push it without instruction.

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
