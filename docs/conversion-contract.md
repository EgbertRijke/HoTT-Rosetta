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
