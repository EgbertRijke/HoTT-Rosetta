# Implementation handoff

Updated 2026-09-04.

## Current branch

Work continues on `main`. The narrative-placement branch was merged and
removed from the fork. Key commits leading into this handoff are:

- `d33e710 fix(converter): place Agda blocks by narrative scope`
- `47b17f3 docs(review): record Agda placement feedback`
- `f184957 feat(review): improve Agda review triage and table controls`

The first commit adds stable `rosetta-item-end` markers, curated narrative
anchors, optional headings for prerequisite groups, manifest relocations, and
regenerated products. The second preserves the collaborator's Agda review
comments separately. The third preserves applicable review evidence after the
converter change, adds the `needs-further-review` decision, migrates reviewed
but inconclusive records, and adds sortable and filterable review tables.

The branch passed the full unit suite, `python3 rosetta.py check`, and
`git diff --check`. Candidate typechecks passed for the affected sections 8.1,
8.5, 9.1, 9.2, 9.3, and 10.4. Regeneration also brought two exercise products
into agreement with existing notation conversion rules; those small notation
changes were generated consequences rather than hand edits.

### What changed

- The renderer now closes a numbered item's scope after its adjacent proof or
  construction, not merely at the closing theorem div emitted by Pandoc.
  Consequently, ordinary block insertion no longer captures transition prose.
- Section 8.5's general-purpose helpers are visibly grouped as **Agda
  prerequisites for Section 8.5**. Logical-equivalence projections and
  decidability of equality with one moved to their earlier narrative homes in
  Section 8.1. Other helpers stayed at section scope because moving them into
  earlier modules caused dependency-order or name-resolution failures.
- Section 9.2's combined invertibility material was split into the forward
  prerequisite at Definition 9.2.1 and the converse at Proposition 9.2.7. The
  involution material moved beside the homotopy/involution examples it
  formalizes. Anonymous module wrappers were restored where separated upstream
  excerpts otherwise lost their required scope.
- In Theorem 9.3.4, the inverse-map code now follows the prose that finishes
  defining `eq-pair`; the equivalence proof remains after the rest of the proof
  narrative.

Most generated-file differences outside the central placement work were either
new item-end markers, movement of an unchanged Agda fence ahead of transition
prose, or existing notation normalization. Review hashes were refreshed only
where inspection established that the reviewable Agda remained unchanged.

### Remaining collaborator review

The collaborator explicitly reserved these generated files for manual review:

- Section 8.1
- Section 8.5
- Section 9.1
- Section 9.2

Do not refresh or transfer stale review evidence for those files merely because
the Agda declarations look familiar. All stale Agda review records outside
those four files were reconciled before `f184957`; Section 9.3 is not part of
the remaining manual-review set.

Complete the four-file narrative review, then repeat the required checks and
affected typechecks for Sections 8.1, 8.5, 9.1, 9.2, 9.3, and 10.4. In
particular, decide whether the Section 8.5 prerequisite group is the desired
editorial presentation. Do not move those helpers solely for visual proximity:
first establish that every definition is in Agda scope at its new location.

### Review workflow state

Agda review decisions now distinguish `pending` (no recorded decision) from
`needs-further-review` (inspected but not ready for approval or rejection).
Content mismatches still display as `stale` over the saved decision. Existing
pending code-block records with comments by `Daniel C`, `Daniel`, or
`Reviewer` were migrated to the new decision; missing-code records and records
with only `codex` comments were not.

On the review home page, status totals are filter buttons and all five table
columns are sortable. A repeated header click cycles ascending, descending,
and default order. The active status button, directional arrows, live result
summary, and **Reset table view** control make the current view explicit.
These controls are client-side presentation only and do not change review data.

## Current goal

Complete the remaining Agda for every **section file** in the book, working
through Chapters 3--22 in source order. File existence is not evidence that a
section is complete: inspect every numbered definition, lemma, proposition,
theorem, construction, and proof for applicable formalization.

Section 10.2 currently fails at `ev-point`. Its Definition 10.2.1 block is now
a recorded training exercise. Do not enlarge the already complete Section 2.2
solely to fix it. The needed result's natural home, Remark 2.2.2, and pinned
source are recorded in `docs/invisible-math.md`. The current block has not yet
been emptied.

Exercise prose remains part of conversion, but missing exercise Agda is the
final formalization phase. Do not search for or add exercise Agda yet unless a
later section imports or otherwise directly requires it. When an exercise is a
section dependency, add only the dependency needed to unblock section work,
with the same provenance and validation requirements as section code.

Chapters 1--2 are optional compatibility material. Do not let work there delay
section completion in Chapters 3--22.

## Section-completion workflow

For each incomplete section:

1. Compare the LaTeX source, active generated section, numbered-item inventory,
   current Agda manifest entries, explicit gaps, and downstream imports. Do not
   infer completeness from filenames or review state.
2. List the section items that still lack substantive Agda or whose existing
   block is incomplete, misplaced, incorrectly sourced, or not typechecking.
   For placement work, follow
   `skills/hott-rosetta-translation/references/agda-block-placement.md`.
3. Search the pinned `external/agda-unimath` checkout for exact material first,
   then for the closest analogous implementation. Follow the search and
   dependency procedure in `skills/hott-rosetta-translation/SKILL.md` and its
   section references.
4. Copy the closest applicable code. Make only locally necessary adaptations
   for established names, universes, imports, and dependency structure.
5. Record exact commit/file/inclusive-line/hash provenance and classify the
   block honestly as exact or adapted. Never create a new block by hand.
6. Add repository-local imports only. If a section requires exercise code,
   formalize that dependency before continuing and document why it was needed.
7. Regenerate the section and run
   `python3 rosetta.py typecheck-candidate N M`.
8. Recheck later section consumers whenever a shared name, dependency, or
   imported block changes. After completing a chapter's sections, typecheck its
   aggregate chapter candidate.
9. If no applicable agda-unimath source exists, record a clear gap and continue
   with other section items. Do not substitute invented Agda.

Once every required section has been audited and its applicable Agda supplied,
begin the deferred exercise-Agda pass in book order.

## Priority order

1. Faithful section prose, mathematics, numbering, and Markdown.
2. Remaining provenance-backed Agda for all section definitions and results.
3. Section dependency closure, including only exercises required downstream.
4. Aggregate chapter correctness and converter-wide regressions.
5. Remaining exercise Agda after section work is complete.
6. Optional review-interface and diagram presentation improvements.

## Active document model

- `data/project-layout.json` defines the only active Rosetta directory,
  currently `rosetta-book/`.
- `data/rosetta-files.json` records stable chapter, section, exercise, and
  support filenames.
- `archive/legacy-rosetta/` is a historical backup only. Active scripts,
  tests, review tools, Agda invocations, and agent workflows must never read,
  write, compare against, or import it.
- Generated files are products. Durable corrections belong in converter code
  or versioned data, followed by regeneration.
- Review state is optional metadata and never controls conversion, ordinary
  checks, or the definition of section completion.

## Agda and provenance rules

- Never invent Agda. Search pinned agda-unimath for exact and analogous code.
- Preserve upstream names and structure wherever local compatibility permits.
- Exact blocks must be byte-for-byte identical to their pinned source range.
- Adapted blocks require a concise, concrete adaptation note.
- Record the upstream commit, file, inclusive lines, SHA-256 hash, stored code,
  destination, item, and provenance category in `data/agda-blocks*.json`.
- Generated documents must be self-contained and use repository-local imports,
  never imports from `external/agda-unimath`.
- Historical handwritten/local blocks may remain, but do not add new ones.
- A missing applicable source is a reportable gap, not permission to write a
  replacement.
- Do not enlarge an earlier complete section solely to support later Agda.
  Leave the blocked later formalization empty. Record the exercise in
  `docs/agda-training-exercises.md`. Record each upstream requirement and its
  natural mathematical home in `docs/invisible-math.md`.
- Count these exercises by chapter. At 15, preserve the cautious version and
  build a source-backed placement alternative on a separate proposal branch.
  Validate it, but do not merge or push it without instruction. Never record
  an unpushed branch name in tracked files.

Avoid snapshot counts in handoff documentation. Obtain current block, gap,
review, and generated-file counts from `python3 rosetta.py check` and the
versioned manifests so the instructions do not become stale as work proceeds.

## Review program

The review program is optional. It displays active generated Markdown,
candidate and recorded-source Agda, provenance, typecheck state, comments,
missing-code items, and a collapsible highlighted Agda diff.

Edits to existing curated blocks use a separate scratchpad page. Scratchpad
drafts are temporary, typechecked against the overlaid destination, and may be
promoted only when the exact current draft passes. Promotion shows the manifest
diff before confirmation and regenerates the destination. Missing-code entries
remain comment-only because current policy forbids new handwritten blocks.

The web server initializes review data in the background and shows a loading
page until the index is ready. Review UI behavior must remain independent of
ordinary conversion and checks.

Add a concise `codex` review comment only when it helps resolve a mathematical,
source, or dependency question. Do not add routine search logs, obvious code
summaries, or comments that merely report a passing typecheck.

## Implementation map

- `converter/rosetta/render.py`: LaTeX-to-Markdown structure and item markers.
- `converter/rosetta/generate.py`: document generation and candidate checks.
- `converter/rosetta/agda_manifest.py`: curated block loading and insertion.
- `converter/rosetta/agda_review.py`: review records and discovery.
- `converter/rosetta/agda_scratchpad.py`: temporary edits and promotion gate.
- `converter/rosetta/review_web.py`: optional browser interface.
- `converter/rosetta/layout.py`, `converter/rosetta/file_registry.py`: active
  location and stable names.
- `data/agda-blocks*.json`: curated Agda and provenance.
- `data/agda-gaps.json`: explicit gaps that cannot be inferred automatically.
- `data/agda-coverage.json`: audited coverage evidence; verify rather than
  assuming entries remain complete after dependency or source changes.

Everyday commands:

```text
python3 rosetta.py candidate N M
python3 rosetta.py typecheck-candidate N M
python3 rosetta.py check
python3 rosetta.py review --web
```

## Required validation

Before handing work back, run:

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

Also typecheck every changed section containing Agda. Typecheck an exercise
candidate only when its Agda changes. Typecheck affected aggregate chapters
when shared dependencies or completed section sets change.

Preserve all unrelated and in-progress work. Commits are allowed and should be
focused: inspect the worktree first, stage only the intended files or hunks,
validate, and use a clear message. Do not reset, clean, overwrite, amend or
rewrite existing history, pull, or push unless the task specifically calls for
that operation.
