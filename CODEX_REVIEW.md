# Codex Review Analysis

Codex review received 2026-02-11. Sorted by validity.

## Wrong (no action needed)

- **Fixpoint property invalid**: Codex misread the proof. The argument is by contradiction: for d ∉ X, if σ and σ₂ disagreed, refineStep would add d, but X = refineStep(X) at fixpoint, so d ∈ X — contradiction. Valid proof, 0 sorry.
- **Branch completeness assumed**: `non_ctrl_at_fixpoint` doesn't assume completeness — it PROVES controllability at fixpoint via h_faithful. Earned, not assumed.
- **[Fintype Dim] unrealistic**: Dim is grammar-bound semantic state (variables, registers), not heap addresses. Finite for a fixed grammar.

## Valid — paper framing issues (TODO)

- [ ] **Oracle construction is existential**: R quantifies over concrete steps, making OracleSoundFor trivially satisfied. Paper should be clear this is an existence proof, not an extraction algorithm.
- [ ] **h_faithful is strong**: Full observation injectivity is a strong assumption. Paper should discuss honestly. L3 (weaken to transition-relevant injectivity) partially addresses this.
- [ ] **HTHLabel presupposes structure**: Lean takes GrammarConformant/HTHLabel as given. Paper claims to discover this structure via testing. Paper should distinguish what's proved (given structure → simulation) from what's conjectured (testing discovers structure).
- [ ] **OracleSoundFor is just the semantics**: Follows from existential oracle. Non-trivial content is in co-refinement fixpoint (about π), not in R.
- [ ] **Check bisimulation vs simulation claim**: Paper may claim bisimulation; Lean proves one-way simulation G' ≼ H_I. Fix if mismatched.
- [ ] **"Oracles assume the hard part"**: Oracle soundness is a hypothesis. Frame as conditional result, not "we solve extraction."

## Valid — practical concerns (acknowledge in paper, not proof bugs)

- [ ] X is not exactly AST-bound state in realistic settings (allocator state, hash seeds, etc.)
- [ ] HTH labels + evaluation order: not formally defined, brittle under optimization/JIT
- [ ] Covering set is syntactic, not semantic — doesn't cover context-sensitive interactions
- [ ] R* definition ambiguous (union vs transitive closure)
- [ ] BStates/Alt(s) circularity without explicit monotonicity argument

## Not applicable

- Mismatch #5 ("X is transitive closure of AST-bound state" comment in Lean): this is a docstring, not a formal claim. Valid to clean up but not a proof issue.
