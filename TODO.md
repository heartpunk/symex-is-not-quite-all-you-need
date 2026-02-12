# Review TODO

Consolidated from 4 independent reviews (3 opus agents + Codex), 2026-02-12.
Organized by priority. Check off as completed.

---

## P0: Submission-blocking

These must be fixed before ANY submission (full paper or WIP report).

- [ ] **No citations in body.** Zero `\cite{}` commands anywhere. `\nocite{*}` dumps all 9 refs as phantoms. Add inline citations throughout. (paper)
- [ ] **"TODO add index terms" renders in PDF.** Line 45: literal TODO in `\begin{IEEEkeywords}`. (paper)
- [ ] **Version "0.0.2" in title.** Line 30. Remove before submission. (paper)
- [ ] **Empty acknowledgments section.** Line 376: `\section*{Acknowledgments}` with only a TODO comment renders as empty section. (paper)
- [ ] **1600+ lines of DRAFT appendix in document body.** Lines 383-2051. Red text, `[DRAFT] DELETE BEFORE SUBMISSION` markers, editorial notes like `[NOTE: Sophie flagged this may need to move earlier]` (line 189) and `[That's the whole technique.]` (line 248) all render in compiled PDF. Either excise or gate behind a conditional. (paper)
- [ ] **Incomplete sentence.** Line 68: "$\Sigma$ is the concrete runtime space... In the case of the more abstract view, like a labeled transition system, which we focus on in this paper." Trails off mid-thought. (paper)

---

## P1: Paper-Lean accuracy

Mismatches between what the paper claims and what Lean proves.

- [x] **Three-oracle framing vs one-oracle proof.** Section V-A (line 257) claims three oracle dependencies (grammar, branching, value-transformation). Lean's `extraction_pipeline` takes ONE `symex` parameter + `GrammarConformant`. Reframe Section V-A to match, or explain the subsumption. (paper)
- [x] **Hidden typeclass hypotheses.** `[DecidableEq Dim]` and `[Inhabited Value]` are required by all main Lean theorems but not in the paper's theorem statement (lines 327-334). Add them or note them as mild technical conditions. (paper)
- [x] **Guard/Update vs existential oracle.** Paper says $R_\ell(x,x') := \text{Guard}_\ell(x) \land \text{Update}_\ell(x,x')$ (line 87). Lean's `extractionOracle` is an existential projection through symex. These are structurally different. Paper should explain the relationship or use notation matching the Lean. (paper)
- [ ] **Bisimulation is a different construction, not "just add h_symex_complete."** `extraction_bisimulation` uses a different oracle (reachability-restricted), different refinement step (observation disagreements), and does NOT reuse `extraction_possible`. Paper says "strengthened fixpoint" (line 359) which understates this. Be more explicit. (paper)
- [ ] **Config = `Dim → Value` never stated.** Paper says "learned configuration space" but never says it's the function type. Mention in the theorem statement or a footnote. (paper)
- [ ] **Section V intro overclaims "sound and complete."** Line 257 says "sound and complete oracles." Main Theorem only requires soundness. Completeness only needed for bisimulation extension. Fix the intro. (paper)
- [ ] **Section III-D claims completeness informally.** Lines 155-159 claim completeness follows from the branching oracle, but the main theorem only proves simulation (one direction). Clarify that this is about the technique's design, not the proved theorem. (paper)
- [ ] **h_faithful asymmetry underdocumented.** Requires σ₁ reachable but σ₂ can be ANY state. Paper (line 351) says "reachable states be distinguishable by observation" which undersells the actual strength. One sentence fix. (paper)

---

## P2: Paper clarity & consistency

Not wrong, but confusing or could trip up reviewers.

- [ ] **O's Σ-level vs π-level interface.** O is defined as operating at Σ level (line 99) but also as "producing constraints over π(s)" (line 103). The projection step is not stated explicitly. Add one sentence clarifying O analyzes at Σ and projects results onto π. (paper, Codex #1/#5)
- [ ] **O/symex confusion between Setup and Construction.** Setup (V-B, line 277) references O and O* fixpoint process. Construction (V-D, line 307) switches to `symex`. Clarify the relationship: O is the methodological process, symex is the formal parameter. (paper)
- [ ] **"No internal branching in HTH blocks" needs explicit hole-granularity constraint.** The HTH draft section asserts basic blocks have no branching, but this is only true if hole boundaries are fine enough. Either define "hole" to guarantee this or state it as an assumption. (paper, Codex #2)
- [ ] **DRAFT Branching Oracle section lags behind O = symex+ISA framing.** Lines 704-782 only list tools (S2E/angr/KLEE + Sail) without mentioning K reachability logic or the "O = symex+ISA" shorthand established at line 130. Update or delete. (paper, Codex #3)
- [ ] **R* definition ambiguous.** Line 89: "R* = ⋃_ℓ R_ℓ and its transitive closure" — union or closure of union? Clarify: R* := (⋃_ℓ R_ℓ)*. Or delete — R* is never used. (paper)
- [ ] **Completeness reads as derived rather than assumed.** Lines 154-159 and 704-782. Worth one sentence: "this is an assumption, not proven here." (paper, Codex #6)
- [ ] **Value transformation oracle section assumes no internal branching.** Lines 820-872. "Symbolically execute just that region" assumes single-path. Tie back to the HTH straight-line assumption. (paper, Codex #7)
- [ ] **Appendix sentinel detection contradicts Section IV-D.** Section IV-D (line 210) says "we cannot simply look for where sentinel *values* appear." Appendix (line 956) says "When we see κ₁ computed in the trace, we know h₁ was just evaluated." Contradiction. (paper)
- [ ] **ICTAC bisimulation vs general bisimulation: different strength.** ICTAC version has no reachability restriction (witness `fun x σ => σ = x`). General version restricts to reachable states. Paper doesn't highlight this asymmetry. (paper)
- [ ] **$\Sigma$ notation mixes ISA-level and LTS-level** without resolving which view the paper takes. Line 68. (paper)
- [ ] **O* "behavioral pattern" undefined.** Line 107: "one representative per behavioral pattern (same control flow, same HTH structure)" — never formally pinned down. (paper)
- [ ] **Forward reference to R in notation.** Line 76 references R before it's defined at line 88. (paper)
- [ ] **Simulation notation ≼ direction.** Line 111: G' ≼ M means "G' simulates M." In process algebra, ≼ often means the opposite. Anchor to a standard reference or footnote the convention. (paper)
- [ ] **GCD example assumes Python but never states it.** Lines 1081-1345. (paper)

---

## P3: Lean cleanup

Dead code and disconnected modules. Not blocking but misrepresents formalization completeness.

- [ ] **`GrammarConformant.labels_from_grammar` never used.** The field is carried but never checked by any theorem. Could be removed or noted as future work. (ConditionalSimulation.lean)
- [ ] **InformationSufficiency.lean almost entirely disconnected from extraction pipeline.** Covering sets, differential causality, causal propagation — none used by `extraction_possible` or `extraction_bisimulation`. The paper's argument that testing discovers dimensions is not mechanized. (InformationSufficiency.lean)
- [ ] **ICTACCorrespondence → ExtractionPossibility chain not mechanized.** `symexOfTraceDecomp_sound` exists but is never composed with `extraction_possible`. Manual instantiation required. (ICTACCorrespondence.lean)
- [ ] **~30 dead definitions/theorems.** Including: `BranchingOracle` infrastructure, `IsMaximalTrace`/`IsBranchPoint`/`IsDeadEnd`, `Sim.refl`/`Sim.trans`, `trace_equivalence_of_sound_complete`, `coveringSet`/`coveringSet_adequate`, `DistinctSentinels`, `ReachabilityOracleSoundFor`, `symexOfTraceDecomp_sound`, `extractionProjection_tracked`/`_eq_on_tracked`, `branch_divergence_refines`, `simulation_at_coRefinement_fixpoint_gc`, `branches_complete`, `non_controllable_internal`, `ofOption`, `Reachable.extend`, `holePositions`, `Sim_of_sound_oracle`/`_of_complete_oracle`. (all files)
- [ ] **`extraction_bisimulation` does not reuse `extraction_possible`.** Entirely independent proof with different refinement step and oracle. Consider refactoring to share infrastructure, or document the independence. (ExtractionPossibility.lean)
- [ ] **Docstring line references to scratch.tex are brittle.** E.g., "line 230, line 323" in CoRefinementConvergence.lean — 230 is wrong (should be 236). Reference theorem names instead. (CoRefinementConvergence.lean)
- [ ] **`Function.iterate_stable` and `Finset.monotone_stabilizes` could be contributed to Mathlib.** Currently project-local in the `Function`/`Finset` namespace, risking future collision. (CoRefinementConvergence.lean)
- [ ] **Multiple `open Classical in` could be one section-level `open Classical`.** Lines 82, 117, 174/268/315 in ExtractionPossibility.lean. (ExtractionPossibility.lean)

---

## P4: Nice-to-have / editorial

- [ ] **HTH labeling precondition paragraph formatting.** Line 281-282: first sentence is very long, would read better split. (paper)
- [ ] **DRAFT appendix notation re-introduces O/Alt(s)/ReplayApply** without linking back to formal definitions or symex+ISA framing. (paper)
- [ ] **Naming inconsistency.** `OracleSoundFor` vs `ReachabilityOracleSoundFor` vs `ReachabilityOracleValueSound`. (Lean)
- [ ] **`IsXControllable` quantifies over ALL states (including unreachable).** Works in proofs but potentially confusing. Document the design choice. (ConditionalSimulation.lean)
- [ ] **`HTHLabel` has no well-formedness invariant.** `fromPos`/`toPos` are unbounded `Nat`, no connection to rule output length. (ConditionalSimulation.lean)
- [ ] **Redundant Mathlib import.** `import Mathlib.Logic.Relation` may be transitively available. (ConditionalSimulation.lean)

---

## Decision log

Decisions about what NOT to fix and why.

- **This tranche of P1s first**: Doing this particular batch of paper-Lean accuracy fixes before P0 submission-blocking items because these specific mismatches are the more important blockers for a shepherded workshop-style venue — reviewers cross-checking the Lean will flag them.
- **Three-way co-refinement not formalized**: Acknowledged scope limitation. Paper should note it. Formalizing is future work.
- **InformationSufficiency disconnection**: The module proves valid mathematical results about differential causality. The bridge to extraction is methodological, not formal. Paper should be clear about this.
- **Dead code**: Some definitions exist for conceptual completeness (branching oracles, maximal traces). Could be kept with a note or removed for a cleaner artifact. User's call.
- **`extraction_bisimulation` independence**: The different construction is mathematically necessary (reachability refinement vs non-controllability refinement). Documenting is better than forcing shared infrastructure.
- **Three-oracle → single-parameter**: Added clarifying paragraph at end of V-A explaining that Lean unifies branching + value-transformation into one `symex` parameter, grammar is structural precondition. Conceptual decomposition preserved.
- **Hidden typeclass hypotheses**: Added footnote to Main Theorem noting DecidableEq Dim, Fintype Dim, Inhabited Value as mild technical conditions for the mechanization.
- **Guard/Update vs existential oracle**: Added sentences in V-D Oracle bullet explaining that the existential projection is the mechanized form, and collapses to Guard ∧ Update when symex factors as PC + Sub (ICTAC setting).
