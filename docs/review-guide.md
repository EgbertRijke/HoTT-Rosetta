# Review UI

Run `python3 rosetta.py review --web`, open the printed local address, and stop
the server with `Ctrl-C`. The loading page remains visible while review data is
indexed. Review is optional and never gates conversion or ordinary checks.

Each Agda page shows the book statement, Rosetta code, recorded agda-unimath
source and provenance, typecheck state, comments, and a collapsible highlighted
diff. Reviewers may approve, reject, or comment; changed content makes earlier
decisions stale. Records are stored in `data/agda-reviews.json`.

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

Missing-code pages accept comments but cannot be approved, edited, or
typechecked. Current policy forbids adding handwritten replacement blocks.

The file reader displays active generated files read-only. Durable changes
belong in converter code or curated data followed by regeneration.
