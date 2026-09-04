# Agda block placement

Narrative placement and Agda dependency order are independent constraints.
Choose a location only when it satisfies both.

## Placement model

The renderer emits `<!-- rosetta-item: ID -->` at the start of a numbered item
and `<!-- rosetta-item-end: ID -->` after its complete scope. Pandoc emits a
theorem and its following proof or construction as separate divs, so the
renderer deliberately holds the item end until that adjacent div closes.
Transition prose belongs outside the item.

Manifest blocks default to insertion immediately before the matching end
marker. The older next-`##` fallback exists for anchors without an end marker,
including section-level anchors; do not rely on it for numbered items.

Use the optional fields as follows:

- `after_text`: an exact generated-prose substring after which a block is
  inserted. Use it for an intermediate definition or proof step inside a long
  item. Keep the anchor distinctive, and add a regression test. Conversion must
  fail if the text disappears.
- `display_heading`: a visible level-three heading emitted immediately before
  that block. Use it on the first block of a section-level prerequisite group,
  not as a substitute for finding a real narrative home.
- `order`: declaration order among blocks sharing a location. It is also Agda
  scope order, so choose it from dependencies rather than appearance alone.

Avoid assigning several blocks the same `after_text` without a test for their
final order. Repeated insertion at one exact character position can produce an
order that is not obvious from the manifest.

## Relocation procedure

1. Identify what the block formalizes: the item statement, an intermediate
   prose step, a reusable earlier lemma, or only a technical prerequisite.
2. List every name it consumes and every later block that consumes it. Inspect
   repository-local imports and generated declaration order, not just source
   filenames.
3. Prefer, in order: the genuine earlier mathematical item; the exact prose
   step via `after_text`; the item's end marker; or a visibly labeled
   section-level prerequisite group.
4. When splitting a contiguous upstream excerpt, preserve any required
   anonymous module parameters. Restoring that wrapper changes the stored text,
   so mark the block `adapted` and explain the change in `source_note`.
5. Regenerate every affected destination. Inspect the rendered prose around
   each fence, not only the code or manifest diff.
6. Typecheck the source and destination sections, plus downstream consumers.
   Run the full unit suite, `python3 rosetta.py check`, and `git diff --check`.

If an editorially attractive move introduces missing names, duplicate names,
module-scope loss, or a dependency cycle, do not patch around it with invented
Agda. Keep the declaration at the earliest valid scope and label a prerequisite
group when needed.

## Lessons from Sections 8.5 and 9.3

Section 8.5 exposed the difference between subject matter and dependency
scope. Some generic logical and decidability lemmas could move to their true
earlier homes in Section 8.1. Several arithmetic helpers could not: moving them
earlier caused dependency-order or name-resolution failures. Grouping those as
section prerequisites made their role explicit without breaking Agda.

Section 9.2 showed that one upstream module excerpt can formalize two different
narrative claims. The forward construction belongs with the definition and is
needed by intervening examples; the converse belongs with the later
proposition. Splitting the excerpt required restoring its anonymous module
wrapper and recording both blocks as adaptations.

Theorem 9.3.4 showed when `after_text` is appropriate. Its inverse-map block
implements the prose ending “This completes the definition of the function
`eq-pair`,” while the later block proves the equivalence. Anchoring the first
block to that sentence preserves the proof's actual sequence.
