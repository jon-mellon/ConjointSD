# runLinter.lean

Lean file: [scripts/runLinter.lean](../scripts/runLinter.lean)

This script wires `lake lint` to a Batteries-based linter runner.

What it does:
- Locates default Lake targets and runs linters on their root modules.
- Supports `--update` to refresh `scripts/nolints.json`.
- Reports errors in standard linter format.
- Skips `docBlame` and `unusedArguments` to avoid project-wide noise.

Usage:
- `lake lint`
- `lake lint --update`
