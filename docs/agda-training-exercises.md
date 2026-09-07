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
Published proposal `0c3d8b1` passes Section 12.1, Exercise 10.1, and aggregate
Chapters 10--12, with 155 unit tests and repository checks passing. Main keeps
its existing training sites empty and Section 12.1 deferred.

### `theorem-12.2.3-embeddings-propositional-fibers`

- **Place:** Section 12.2, Theorem 12.2.3.
- **Task:** Prove both directions between embeddings and proposition-valued
  fibers using the fundamental theorem of identity types.
- **Absent result:** `equiv-fiber`, with its two maps and inverse homotopies.
- **Reason:** This theorem directly needs the same auxiliary as Theorem
  11.4.2. Its natural home, Section 10.3, remains complete and unchanged on
  `main`; record this later empty site even though the auxiliary is already
  available on the shared proposal.
- **Later use:** Both implications of Theorem 12.2.3, both implications of
  Corollary 12.2.4, and the subtype identity equivalence.
- **Invisible mathematics:** “Theorem 12.2.3: embeddings and propositional
  fibers” in `docs/invisible-math.md`.
- **Status:** Empty on `main`; Section 12.2 and Chapter 12 are deferred.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `7b6b28c`.
  It reuses the complete auxiliary already placed at Definition 10.3.1 by
  `63e5e49` and restores the retained theorem without changing its proof.
- **Validation:** Section 12.2, Exercise 10.7, and aggregate Chapters 10--12
  pass ordinary Agda checks on that proposal. All 156 proposal unit tests,
  repository checks, and whitespace checks pass. Main's 153 tests pass,
  but its Section 12.2 and Chapter 12 checks remain deferred, not passed.

The fundamental-theorem applications also extend the later uses of the two
Chapter 10 training exercises. Only part (a) of Exercise 10.7 is added early,
at its exact book home, for the projection corollary. Parts (b) and (c) remain
explicit Agda gaps; their proofs are not required by this section.

### `theorem-12.3.4-propositional-identity-relation`

- **Place:** Section 12.3, Theorem 12.3.4.
- **Task:** Prove that a proposition-valued reflexive relation mapping into
  identity characterizes identity, including equivalence of every family of
  maps from identity into the relation, and conclude that the type is a set.
- **Absent results:** `fundamental-theorem-id-retraction`, and its total-map
  laws `tot-htpy`, `tot-id`, and `preserves-comp-tot`.
- **Reason:** These general results belong in the previously audited
  mathematical accounts of Sections 11.2 and 11.1, which pass on the shared
  proposal. Preserve those accounts on `main`, where their existing training
  dependencies still cause deferred checks; do not confuse that status with
  a successful main typecheck or a completeness record.
- **Later use:** The based and binary relation criteria, the arbitrary-map
  conclusion of Theorem 12.3.4, and Hedberg's Theorem 12.3.5.
- **Invisible mathematics:** “Theorem 12.3.4: propositional identity
  relations” in `docs/invisible-math.md`.
- **Status:** The based proof block is empty on `main`; Section 12.3 and
  Chapter 12 are deferred, not passed.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `b96fdf3`.
  It adds the three total-map laws at Definition 11.1.1, then the retract
  fundamental theorem at Theorem 11.2.2, and restores the retained based
  proof without changing it.
- **Validation:** Candidate Sections 11.1--11.6 and 12.1--12.3 and aggregate
  Chapters 10--12 pass ordinary Agda checks on that proposal. All 158
  proposal unit tests, repository checks, and whitespace checks pass.
  Main's 154 tests pass, but Section 12.3 remains deferred, not passed.

No exercise Agda is added for Section 12.3. It reuses the required
contractibility-of-retracts result already curated at Exercise 10.2. Its
fundamental-theorem uses also extend the two existing Chapter 10 training
dependencies; its proposition imports include the other recorded sites.

### `theorem-12.4.7-truncated-action-on-identities`

- **Place:** Section 12.4, Theorem 12.4.7.
- **Task:** Prove both directions between successor-truncated fibers of a
  map and truncated fibers of its action on identities.
- **Absent results:** `eq-fiber-fiber-ap` and `is-equiv-eq-fiber-fiber-ap`,
  together with `is-equiv-tr` and its inverse-transport homotopies.
- **Reason:** The specialized fiber equivalence belongs immediately after
  the general one at Example 11.6.3. Exercise 9.1 explicitly asks for
  transport equivalence with its inverse, so it is the exact home for
  this needed result, refining the initially suggested Example 9.2.3.
  Preserve the earlier main accounts; Section 11.6 passes only on the
  proposal. No Section 9.2 edit or review refresh is needed.
- **Later use:** The converse implication in Theorem 12.4.7. Its first
  implication also depends on the existing Example 11.6.3 exercise.
- **Invisible mathematics:** “Theorem 12.4.7: truncated action on
  identities” in `docs/invisible-math.md`.
- **Status:** Empty on `main`; candidate Section 12.4 and Chapter 12 defer.
- **Proposal solution:** `proposal/agda-exercise-solutions`, commit `31222b8`.
  It places transport and inverse-transport equivalences at Exercise 9.1,
  the fiber specialization at Example 11.6.3, and restores the retained
  later theorem without changing any existing proof code.
- **Validation:** Candidate Sections 11.6 and 12.4, Exercises 9.1 and
  12.8, and aggregate Chapters 9--12 pass ordinary Agda checks. All 161
  proposal unit tests and repository checks pass. Main's 156 tests pass;
  its Section 12.4 and Chapter 12 remain deferred, not passed.

Exercise 12.8(a) is added early because the pinned equivalence-invariance
proof needs its identity-retract result. Part (b)'s truncation-of-retracts
proof appears as a visibly labeled prerequisite at Proposition 12.4.5:
placing it in the exercise module would make the section and exercise
import one another. No earlier complete main file is enlarged for it.

Section 13.1 introduces no new training site. Its fundamental-theorem
proofs use the existing Chapter 10 exercises. Its Chapter 12 file imports
also transitively retain the Section 11.4, 11.6, and 12.4 training
dependencies; this conservative whole-file deferral does not mean every
imported exercise is directly used in the new proof. The two pre-axiom
equivalence results take their hypotheses as arguments. Function
extensionality is assumed only at Axiom 13.1.3. Published proposal merge
`dc97e2f5941b950b2cfd3283794adee1278891b2` passes candidate Sections 2.2
and 13.1, aggregate Chapters 1--6 and 13--14, all 165 unit tests, and
repository and whitespace checks. No new solution code was necessary;
main's deferred result is not a pass.
