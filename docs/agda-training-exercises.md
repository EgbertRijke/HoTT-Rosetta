# Agda training exercises

This is the exercise index. The policy and mandatory agent workflow are in
`docs/conversion-contract.md`. Each entry links the empty site to its required
mathematics, proposal solution, and review state.

## Exercises

### `definition-10.2.1-singleton-induction`

- **Place:** Section 10.2, Definition 10.2.1.
- **Task:** Formalize singleton induction and its computation rule.
- **Absent result:** Evaluation at a point, `ev-point`.
- **Reason:** Section 2.2 already gives a complete account of ordinary
  functions and typechecks. It should not grow solely to support Section 10.2.
- **Later use:** Example 10.2.2 and Theorem 10.2.3.
- **Invisible mathematics:** “Section 10.2: evaluation at a point” in
  `docs/invisible-math.md`.
- **Status:** Empty on `main`; routine Section 10.2 and Chapter 10 checks are
  deferred, not passed.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `511f171`.
  It places `ev-point` at Remark 2.2.2 and restores Definition 10.2.1.
- **Validation:** Candidate Sections 2.2, 10.2, and 10.4 and aggregate Chapters
  2--10 pass ordinary Agda checks at that proposal commit. This also checks
  Example 10.2.2. The full unit suite and repository checks pass.

### `lemma-10.4.5-coherent-inverse`

- **Place:** Section 10.4, Lemma 10.4.5.
- **Task:** Turn an invertible map into a coherently invertible map.
- **Absent results:** Cancellation and whiskering laws for paths and
  homotopies.
- **Reason:** The former proof placed seven general lemmas beside Lemma 10.4.5.
  Their mathematics belongs with earlier path and homotopy operations.
- **Later use:** Theorem 10.4.6; through it, Theorem 11.1.3, Lemma 11.1.4,
  and Theorem 11.1.6.
- **Invisible mathematics:** “Lemma 10.4.5: coherent inverse” in
  `docs/invisible-math.md`.
- **Status:** Empty on `main`.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `5e5a5cd`.
