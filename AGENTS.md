# Agent instructions for ConjointSD

Always follow these project rules when making changes:

## Assumptions (required)

Always add new assumptions (even minor ones) to `ConjointSD/Assumptions.lean` and reuse existing assumptions when possible.

## Jargon links (required)

Use the existing jargon pages in `readable/` (e.g., `readable/jargon_*.md`) when writing or updating documentation. If a new term is introduced, add a new `readable/jargon_*.md` entry and reuse existing jargon pages whenever possible.

## Documentation updates (required)

When you change Lean sources, update the corresponding documentation:

- `project_map.md`: keep the map accurate for any new/removed/renamed `.lean` files or dependency shifts.
- `readable/lean_index.md`: add/remove entries when Lean files are added/removed/renamed.
- `readable/*.md`: update the readable summary for any `.lean` file you modify (e.g., `ConjointSD/PredictedSD.lean` -> `readable/PredictedSD.md`). You may not need to change the file if your change does not make meaningful changes to functionality or mathematical content (e.g. if you're just fixing linter errors). It is fine to skip updating a file if you have nothing meaningful to say
- `gaps.md`: update if your changes add/close proof gaps or alter the state of assumptions called out there.
- `README.md`: update if build instructions or repo layout change.

If unsure which doc to touch, scan the repo and err on the side of updating the mapping/summary docs above.

## Build verification (required)

After touching any `.lean` file, make sure the project still builds:

- Run `lake build` from the repo root without adding a timeout.
- If build verification is not possible in the environment, state that explicitly and explain what is missing.

## Lint (required)

Fix any new linter errors introduced by your changes:

- Run `lake lint` and resolve new issues before finishing.
- If you cannot run lint locally, call that out clearly and leave no known new lint failures.