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
- **Later use:** Example 10.2.2, Theorem 10.2.3, and the identity-system
  implication in Theorem 11.2.2; through it, Sections 11.3--11.5.
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
  Theorem 11.1.6, and Sections 11.2--11.5.
- **Invisible mathematics:** “Lemma 10.4.5: coherent inverse” in
  `docs/invisible-math.md`.
- **Status:** Empty on `main`.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `5e5a5cd`.
- **Later validation:** Proposal `dc1ffed` includes current Section 11.1 and
  passes its candidate check and aggregate Chapters 9--11. The new section's
  dependency on this exercise is intentional; it remains deferred on `main`.

### `theorem-11.4.2-equivalences-are-embeddings`

- **Place:** Section 11.4, Theorem 11.4.2.
- **Task:** Prove that every equivalence is an embedding by the fundamental
  theorem and contractibility of its fibers.
- **Absent result:** `equiv-fiber`, the equivalence between `fiber f y` and
  `fiber' f y`, with its forward and inverse maps and homotopies.
- **Reason:** Section 10.3 is complete and typechecks. Do not enlarge its
  fiber definition solely to support this later theorem on `main`.
- **Later use:** Theorem 11.4.2 and its packaged map `emb-equiv`.
- **Invisible mathematics:** “Theorem 11.4.2: reversing fiber paths” in
  `docs/invisible-math.md`.
- **Status:** Empty on `main`; Section 11.4 and Chapter 11 are deferred.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `63e5e49`.
  It places the complete fiber-orientation equivalence at Definition 10.3.1
  and restores the retained Theorem 11.4.2 block.
- **Validation:** Candidate Sections 10.3 and 11.1--11.4 and aggregate
  Chapters 10--11 pass ordinary Agda checks on that proposal. Its 150-test
  suite, repository check, and whitespace check pass. This also validates the
  new consumers of the two earlier Chapter 10 exercises. Main keeps all
  three training sites empty and affected checks deferred.

The later coproduct identity formalization in Section 11.5 is validated on
proposal `3bbc564`, including aggregate Chapters 9--11. It imports the
fundamental theorem and therefore depends on the two Chapter 10 exercises,
but does not introduce another training exercise.

### `example-11.6.3-identities-in-fibers`

- **Place:** Section 11.6, Example 11.6.3.
- **Task:** Prove `(s ＝ t) ≃ fiber (ap f) (pr2 s ∙ inv (pr2 t))`.
- **Absent result:** `inv-inv`, used by the required inversion equivalence
  in Exercise 9.1. That exercise also supplies the concatenation equivalence.
- **Reason:** The involution law naturally belongs at Definition 5.2.5 in
  complete Section 5.2; do not enlarge it on `main` for this later example.
- **Later use:** The fiberwise equivalence and commuting-triangle proof
  in Example 11.6.3.
- **Invisible mathematics:** “Example 11.6.3: identities in fibers” in
  `docs/invisible-math.md`.
- **Status:** Empty on `main`; Section 11.6 and Chapter 11 are deferred.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `6bd180b`.
  It places `inv-inv` after the inverse laws at Definition 5.2.5, copies
  the required inverse maps and equivalences at Exercise 9.1, and restores
  the retained example without changing its proof.
- **Validation:** Candidate Sections 5.2 and 11.6, Exercises 9.1 and 10.6,
  and aggregate Chapters 5--11 pass ordinary Agda checks on the proposal.
  All 154 proposal unit tests, repository checks, and whitespace checks pass.
  Section 11.6's six-condition theorem is included in these checks.

Section 11.6's theorem and Exercise 10.6 also depend on singleton induction;
the theorem's fundamental-theorem applications additionally depend on coherent
inversion. These extend the later uses of the two existing Chapter 10 exercises.

Section 12.1's subterminal characterization uses Theorem 11.4.2's
`is-emb-is-equiv`. It therefore extends the later uses of that exercise and
its two Chapter 10 dependencies. No new training site is introduced: the
required contractible-identity theorem is added at the previously empty
Exercise 10.1, which the book explicitly cites.
