# Invisible mathematics

This file records the mathematics behind each empty auxiliary Agda block.

For each exercise, record:

- the same stable name used in `docs/agda-training-exercises.md`;
- each needed definition or lemma;
- its mathematical role;
- its dependency order;
- its pinned agda-unimath commit, file, and lines;
- any necessary change of notation;
- every later use.

Record all non-obvious decomposition choices. Keep the explanation short.

## Entries

### Section 10.2: evaluation at a point

Section 10.2 needs
`ev-point a : ((x : A) → P x) → P a` in Definition 10.2.1 and Theorem 10.2.3.
The pinned source is commit `c85d7fb`,
`src/foundation-core/function-types.lagda.md`, lines 48--50.

This is not a training exercise. Evaluation at a point belongs to Section 2.2,
where function evaluation is introduced. Section 10.2 should import it from
there. Until then, its typecheck fails at `ev-point`.
