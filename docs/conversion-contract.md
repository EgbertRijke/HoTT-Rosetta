# Conversion contract

This document contains rules the converter and checks must enforce.

## Scope and structure

- Follow active `\input` commands from `book/hott-intro.tex` in source order.
- A numbered LaTeX `\section` becomes a chapter, each `\subsection` a section,
  and each `\exitem` an exercise.
- Chapters 3--22 require high-fidelity prose and section Agda. Chapters 1--2
  are optional compatibility material.
- Complete section formalization before remaining exercise Agda. Exercise prose
  remains generated; exercise Agda is added early only for section dependencies.
- File presence is not completion. Track prose, numbered items, Agda coverage,
  provenance, typechecking, and optional review separately.

Chapter files contain introductory prose and generated imports. Section files
are the primary content. Numbered theorem-like environments share the LaTeX
counter, reset per subsection, and become level-two headings with stable
`rosetta-item` markers. The converter computes numbering from structure.

## Fidelity

Preserve complete prose, item order, mathematics, proofs, references, and
displays. Differences from LaTeX must be deliberate, tested, and visible.

- Normalize known notation through explicit rules supported by `book/hott.tex`;
  do not execute arbitrary TeX definitions.
- Preserve unsupported macros and environments as diagnostics rather than
  silently dropping content.
- Resolve references from labels. Use small tested aliases only when no useful
  stable number exists, and escape Markdown metacharacters in replacements.
- Convert proof trees and TikZ-CD diagrams into faithful visible drafts with
  stable review markers. Presentation review remains optional.
- Implement recurring conversion repairs in converter code with regression
  tests, then regenerate every affected document.

## Generated product

- `data/project-layout.json` is the sole authority for the active output path.
- `data/rosetta-files.json` defines stable generated filenames.
- Durable changes belong in converter code or versioned data, not manual edits
  to generated files.
- Generated modules use repository-local imports only.
- `archive/legacy-rosetta/` is never an active input, comparison source, import,
  or Agda include path.
- Preview and candidate checks use temporary staging; caches and `.agdai` files
  are not product files.

## Agda provenance

Agda blocks are curated independently of mechanical LaTeX conversion.

- Search pinned `external/agda-unimath` for exact and analogous material.
- Never invent a new block. If nothing applies, record a gap.
- Each block records its item, destination, upstream commit, file, inclusive
  line range, SHA-256 digest, stored code, and provenance category.
- `exact` means the entire stored block is byte-for-byte identical to its
  pinned range. Any local change is `adapted` and needs a concrete note.
- Historical handwritten/local records may remain but must not be presented as
  upstream copies or used as precedent for new handwritten blocks.
- Typecheck every changed section containing Agda and affected aggregates.

## Auxiliary results

Keep an earlier file unchanged when it already tells a complete mathematical
story and typechecks. Do not enlarge it solely to support a later file.

If a later Agda block needs an absent auxiliary definition or lemma:

- leave the later block empty;
- list it in `docs/agda-training-exercises.md`;
- state why the auxiliary result is needed there;
- list its exact agda-unimath requirements in `docs/invisible-math.md`;
- name the earlier item where each requirement would most naturally belong;
- note every later result that needs it;
- treat the resulting unresolved names as expected until the exercise is
  filled.

The exercise belongs where the missing mathematics first blocks the intended
formalization. Its invisible mathematics may have a natural home in an earlier
file. Preserve the book's prose. When the classification is unclear, report it
before changing the manifest.

Every training exercise has a solution on the shared branch
`proposal/agda-exercise-solutions`. There is no chapter threshold.
Create and publish this branch from current `main` when the first exercise is
recorded. Keep all later solutions on the same branch.

For each exercise, an agent must:

1. Commit and push the empty block and both mathematical records on `main`.
2. Fetch both remote branches and inspect their history.
3. Bring the latest `main` into the proposal branch without rewriting public
   history.
4. Add the pinned agda-unimath blocks at their best mathematical locations.
5. Record every placement and dependency choice.
6. Make one focused solution commit.
7. Regenerate and typecheck every affected section and later user.
8. Push only the named proposal branch.
9. On `main`, record the proposal branch and solution commit in
   `docs/agda-training-exercises.md`; commit and push that record.
10. Keep the handoff current.

Never merge the proposal automatically. Never force-push it. Before changing
it, preserve all collaborator work.

These steps are mandatory for agents. Humans may edit either branch without
following them. This is allowed, though the same care is encouraged.

## Deferred Agda checks

An active file that contains or imports a block marked `exercise` is
intentionally incomplete. Routine candidate and aggregate checks must not run
Agda on it. Report `deferred` and list the exercises instead.

`deferred` means only that Agda was not run. It is neither `passed` nor
`failed`. The checker must not add definitions, change Agda options, inspect
compiler errors, suppress errors, or infer mathematical correctness.

The project commands accept `--force` to run the existing Agda invocation and
show its ordinary result. Every proposed solution and affected later file must
pass Agda on `proposal/agda-exercise-solutions` before acceptance.

## Agda narrative placement

Agda blocks must appear where their declarations are both narratively relevant
and valid in Agda's sequential scope. Visual proximity alone is not sufficient.

- Numbered items have stable opening `rosetta-item` markers and closing
  `rosetta-item-end` markers. A closing marker belongs after an immediately
  following proof or construction, because Pandoc may render that material as
  a separate div.
- The default manifest insertion point is immediately before the matching item
  end marker. It must not absorb transition prose that belongs between items.
- Use a manifest `after_text` anchor only when one block implements a specific
  intermediate step within a longer narrative. The exact anchor must occur in
  the generated item; a missing anchor is an error rather than permission to
  fall back silently.
- General prerequisites may use a section item and `display_heading` when
  dependency order prevents a more local narrative home. Apply the heading to
  the first generated block in the group and verify the resulting order.
- A reusable lemma should move to the earliest genuine mathematical home only
  when its own dependencies are already available there and every consumer
  remains later in generated Agda order. Splitting an upstream excerpt may
  require restoring its enclosing anonymous module; that is an adaptation and
  must be recorded as such.
- Treat relocation as a code change: regenerate all affected products,
  typecheck every changed Agda section and downstream consumer, and add
  regression tests for item boundaries and any curated narrative anchor.

## Review UI

Review is optional metadata and cannot affect conversion or ordinary checks.
The UI may display files, provenance, diffs, typechecks, gaps, comments, and
decisions. Changed content makes prior review evidence stale.

For Agda blocks, `pending` means that no review decision has been recorded.
`needs-further-review` means that a reviewer inspected the block but did not
approve or reject it. An evidence mismatch displays as `stale` regardless of
the saved decision until the block is reviewed against its current content.

Edits to existing curated blocks are staged in a temporary scratchpad. Only an
exact passing draft may be promoted; promotion shows the manifest diff, writes
atomically with a recoverable backup, regenerates the destination, and marks
prior review stale. Missing-code items remain comment-only under the current
no-handwritten-code policy.

Strict release checks may require provenance and completed reviews; ordinary
`convert` and `check` must not.
