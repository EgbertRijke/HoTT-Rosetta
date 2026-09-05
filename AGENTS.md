# HoTT Rosetta agent instructions

Before changing the repository, read:

1. `docs/implementation-handoff.md`
2. `docs/conversion-contract.md`
3. `skills/hott-rosetta-translation/SKILL.md`
4. The task references selected by that skill
5. `docs/agda-training-exercises.md`
6. `docs/invisible-math.md`

`docs/initial-prompt.txt` and `docs/audit-baseline.md` are historical evidence,
not current instructions.

## Requirements

- Complete section prose and section Agda for Chapters 3--22 before filling
  remaining exercise Agda. Add exercise Agda earlier only when a section needs
  it. Chapters 1--2 are optional.
- File presence and review state never establish completeness. The optional
  review UI must not control conversion or ordinary checks.
- Obtain the active output path from `data/project-layout.json`; never hard-code
  it.
- Never use `archive/legacy-rosetta/` in active code, tests, comparisons,
  imports, or Agda include paths.
- Never invent Agda. Copy exact or analogous pinned agda-unimath code, make
  only necessary local adaptations, and record commit/file/line/hash
  provenance. If no applicable source exists, report the gap.
- Do not enlarge an earlier complete file solely to support a later one. If a
  later Agda block needs an absent auxiliary result, leave that later block
  empty. Record the exercise in `docs/agda-training-exercises.md`. In
  `docs/invisible-math.md`, record the needed agda-unimath results and their
  natural mathematical home.
- Use one shared branch, `proposal/agda-exercise-solutions`, for every training
  exercise. Create and publish it from current `main` when the first exercise
  appears. Before each solution, bring in the latest `main`. Add one focused
  solution commit, validate it, push it, and record its commit in the exercise
  index. Never merge the proposal automatically or rewrite its public history.
- These branch steps bind agents only. Humans may edit either branch freely.
  Agents must inspect and preserve human changes.
- Generated modules must use repository-local imports, never imports from
  `external/agda-unimath`.
- Preserve unrelated and in-progress work. Agents may create focused commits
  using standard Git practices: inspect the worktree, stage only intended
  changes, and use clear commit messages. Do not reset, clean, overwrite, or
  include unrelated changes in a commit.

## Validation

```text
python3 -m unittest discover
python3 rosetta.py check
git diff --check
```

Also run `python3 rosetta.py typecheck-candidate N M` for every changed section
containing Agda. Typecheck exercises only when their Agda changes.
