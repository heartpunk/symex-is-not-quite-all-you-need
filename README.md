# Symbolic Execution is (Not Quite) All You Need

Submitted to the 2026 LangSec Workshop at IEEE Security & Privacy.

## Abstract

Given a programming language implementation running on a host machine and a grammar, you can use symbolic execution and formal ISA semantics as oracles to extract a formal labeled transition system that simulates the implementation's behavior. With a complete oracle, the extraction yields bisimulation. The main results are mechanized in Lean 4 with no admitted axioms.

## Repository Structure

- `paper/main.tex` / [main.pdf](paper/main.pdf) — the paper
- `paper/refs.bib` — bibliography
- `lean/` — Lean 4 mechanization (0 sorry across 6 files, ~1900 lines)

### Lean Modules

| File | Content |
|------|---------|
| `ConditionalSimulation.lean` | LTS, reachability, traces, simulation, grammar/holes, oracle soundness |
| `CoRefinementConvergence.lean` | Monotone stabilization, co-refinement fixpoint |
| `ExtractionPossibility.lean` | `extraction_possible`, `extraction_bisimulation` |
| `ICTACCorrespondence.lean` | Bridge from trace correspondence to oracle soundness/completeness |
| `Learnability.lean` | Standalone general framework: any `State → Label → State → Prop` satisfying five preconditions admits faithful extraction |
| `CoveringPipelineBridge.lean` | Iterator-style covering bridge |

## Building

**Paper** (requires LaTeX):
```
cd paper && latexmk -pdf main.tex
```

**Lean mechanization** (requires Lean 4 / elan):
```
cd lean && lake build
```

## Citation

See `CITATION.cff`, or use GitHub's "Cite this repository" button.

## License

Documentation: [CC-BY-SA-4.0](https://creativecommons.org/licenses/by-sa/4.0/)
Code: [GPL-3.0](https://www.gnu.org/licenses/gpl-3.0.html)
