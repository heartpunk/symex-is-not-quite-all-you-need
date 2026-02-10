# Symex Is Not Quite All You Need

## Project Overview

Lean 4 mechanization of the paper "Symbolic Execution is (Not Quite) All You Need".
The Lean project lives in `lean/`, the LaTeX paper in `paper/`.

## Version Control

- Use `jj` (Jujutsu), not `git`, for all VCS operations
- **Incremental commits**: make one logical change at a time, commit frequently
  - Each definition, each lemma, each refactor = its own commit
  - Do NOT batch unrelated changes into a single commit
- `lake build` must pass before every commit

## Lean Conventions

- `autoImplicit = false` and `relaxedAutoImplicit = false` are set in lakefile.toml
- All variables must be explicitly declared
- Use Mathlib conventions for style and naming
- `sorry` is acceptable during scaffolding; track all instances in SORRY_AUDIT.md
- Core definitions go in `ConditionalSimulation.lean`; dependent modules import it
