# Review UI

Run `python3 rosetta.py review --web`, open the printed local address, and stop
the server with `Ctrl-C`. The loading page remains visible while review data is
indexed. Review is optional and never gates conversion or ordinary checks.

Each Agda page shows the book statement, Rosetta code, recorded agda-unimath
source and provenance, typecheck state, comments, and a collapsible highlighted
diff. Reviewers may approve, mark a block as needing further review, reject,
clear a decision back to pending, or comment. Here, pending means that no
decision has been recorded; needing further review means that the block was
inspected but is not ready for approval or rejection. Changed content makes an
earlier decision display as stale. Records are stored in
`data/agda-reviews.json`.

The home page supports several client-side ways to find work without changing
the stored review data:

- Select a status total to show only records in that state. Select the active
  total again to show all states.
- Select any column heading to sort ascending, select it again for descending,
  and select it a third time to restore default order.
- Search across visible row text or restrict the table to records with
  comments. These controls combine with status filtering and sorting.
- Use **Reset table view** to clear the status filter, search, comments-only
  filter, and sorting together. The text above the table reports the active
  view and visible record count.

Relocating a block or changing generated item boundaries can refresh its
`review_sha256` and make a prior decision stale even when the Agda text is
unchanged. Preserve existing reviewer comments and inspect diffs before
committing review metadata; never replace the file wholesale after
regeneration.

Use **Open scratchpad editor** to edit an existing block temporarily. Save the
draft, typecheck the overlaid destination, and preview promotion. Only the exact
passing draft can be promoted. Confirmation creates a backup, updates the
appropriate `data/agda-blocks*.json`, regenerates the destination, and clears
the draft. Adapted code requires a concise note.

Missing-code pages accept comments but cannot receive a review decision, be
edited, or be typechecked. Current policy forbids adding handwritten
replacement blocks.

Training exercises show an empty Agda block and their recorded invisible
mathematics. Their solutions live on `proposal/agda-exercise-solutions`, not on
`main`.

The file reader displays active generated files read-only. Durable changes
belong in converter code or curated data followed by regeneration.
