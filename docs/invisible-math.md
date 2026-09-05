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

### Lemma 10.4.5: coherent inverse

- **Exercise:** `lemma-10.4.5-coherent-inverse`.
- **Goal:** Construct a coherent inverse from a two-sided inverse.
- **Main source:** Commit `c85d7fb`,
  `src/foundation-core/coherently-invertible-maps.lagda.md`, lines 464--524.
- **Later use:** Theorem 10.4.6.

Required mathematics, in dependency order:

1. **Cancellation of concatenation.** Natural home: Definition 5.2.5, after
   the inverse laws. Source: `src/foundation-core/identity-types.lagda.md`,
   lines 507--517.
2. **Right whiskering of path identifications.** Natural home: Definition
   5.3.1, where action on paths is introduced. Source:
   `src/foundation-core/whiskering-identifications-concatenation.lagda.md`,
   lines 78--83.
3. **Transposing concatenated homotopies.** Natural home: Proposition 9.1.6,
   after the groupoid laws for homotopies. Source:
   `src/foundation-core/homotopies.lagda.md`, lines 153--163.
4. **Whiskering concatenated homotopies.** Natural home: Proposition 9.1.6.
   Source: `src/foundation-core/whiskering-homotopies-concatenation.lagda.md`,
   lines 79--85.
5. **Composition and left whiskering.** Natural home: Definition 9.1.7,
   where whiskering is introduced. Source:
   `src/foundation/whiskering-homotopies-composition.lagda.md`, lines 269--285.
6. **Left whiskering of higher homotopies.** Natural home: Definition 9.1.7.
   Source: `src/foundation/whiskering-higher-homotopies-composition.lagda.md`,
   lines 62--69.
7. **Coherence of a homotopy to the identity.** Natural home: Definition
   10.4.4, after its naturality formula. Source:
   `src/foundation/whiskering-homotopies-composition.lagda.md`, lines 310--318.

All sources use commit `c85d7fb`. Replace `UU` by `Type`. The first result is
needed by the seventh. The second is needed by the fourth. Results 3--7 are
needed by the proof of Lemma 10.4.5.
