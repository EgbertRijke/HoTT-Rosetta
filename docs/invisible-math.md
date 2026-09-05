# Invisible mathematics

This file records the mathematics behind each empty auxiliary Agda block.

For each exercise, record:

- the same stable name used in `docs/agda-training-exercises.md`;
- each needed definition or lemma;
- its mathematical role;
- the book item where it most naturally belongs;
- its dependency order;
- its pinned agda-unimath commit, file, and lines;
- any necessary change of notation;
- every later use.

Record all non-obvious decomposition choices. Keep the explanation short.

## Entries

### Section 10.2: evaluation at a point

- **Exercise:** `definition-10.2.1-singleton-induction`.
- **Needed result:**
  `ev-point a : ((x : A) → P x) → P a`.
- **Role:** It defines the evaluation map whose section expresses singleton
  induction.
- **Natural home:** Remark 2.2.2, which presents function evaluation.
- **Order:** Define `ev-point` before `is-singleton`.
- **Source:** Commit `c85d7fb`,
  `src/foundation-core/function-types.lagda.md`, lines 48--50.
- **Notation:** Replace `UU` by `Type`.
- **Uses:** Definition 10.2.1 and Theorem 10.2.3.

Section 2.2 already typechecks and tells a complete story. Do not add
`ev-point` there solely to make Section 10.2 compile. Section 10.2 is the
training exercise because the need arises there.
