# Review TODO

Consolidated from 4 independent reviews (3 opus agents + Codex), 2026-02-12.
Organized by priority. Check off as completed.

---

## P0: Submission-blocking

These must be fixed before ANY submission (full paper or WIP report).

- [x] **No citations in body.** Added inline `\cite{}` for all 10 references, removed `\nocite{*}`. (paper)
- [x] **"TODO add index terms" renders in PDF.** Added keywords: symbolic execution, formal verification, labeled transition systems, semantic extraction, grammar mining, Lean 4. (paper)
- [x] **Version "0.0.2" in title.** Bumped to 0.1.0 for submission. Will remove version number entirely for camera-ready. (paper)
- [ ] **Empty acknowledgments section.** Line ~398: `\section*{Acknowledgments}` with only a TODO comment renders as empty section. (paper)
- [ ] **1600+ lines of DRAFT appendix in document body.** Lines ~420-2077. Red text, `[DRAFT] DELETE BEFORE SUBMISSION` markers render in compiled PDF. Either excise or gate behind a conditional. (Editorial notes at lines 189 and 248 already fixed.) (paper)
- [x] **Incomplete sentence.** Line 68: now reads "In the more abstract view of a labeled transition system, which we focus on in this paper, $\Sigma$ is simply the state space of $H$." Complete sentence. (paper — already fixed)

---

## P1: Paper-Lean accuracy

Mismatches between what the paper claims and what Lean proves.

- [x] **Three-oracle framing vs one-oracle proof.** Section V-A (line 257) claims three oracle dependencies (grammar, branching, value-transformation). Lean's `extraction_pipeline` takes ONE `symex` parameter + `GrammarConformant`. Reframe Section V-A to match, or explain the subsumption. (paper)
- [x] **Hidden typeclass hypotheses.** `[DecidableEq Dim]` and `[Inhabited Value]` are required by all main Lean theorems but not in the paper's theorem statement (lines 327-334). Add them or note them as mild technical conditions. (paper)
- [x] **Guard/Update vs existential oracle.** Paper says $R_\ell(x,x') := \text{Guard}_\ell(x) \land \text{Update}_\ell(x,x')$ (line 87). Lean's `extractionOracle` is an existential projection through symex. These are structurally different. Paper should explain the relationship or use notation matching the Lean. (paper)
- [x] **Bisimulation is a different construction, not "just add h_symex_complete."** `extraction_bisimulation` uses a different oracle (reachability-restricted), different refinement step (observation disagreements), and does NOT reuse `extraction_possible`. Paper says "strengthened fixpoint" (line 359) which understates this. Be more explicit. (paper)
- [x] **Config = `Dim → Value` never stated.** Paper says "learned configuration space" but never says it's the function type. Mention in the theorem statement or a footnote. (paper)
- [x] **Section V intro overclaims "sound and complete."** Line 257 says "sound and complete oracles." Main Theorem only requires soundness. Completeness only needed for bisimulation extension. Fix the intro. (paper)
- [x] **Section III-D claims completeness informally.** Lines 155-159 claim completeness follows from the branching oracle, but the main theorem only proves simulation (one direction). Clarify that this is about the technique's design, not the proved theorem. (paper)
- [x] **h_faithful asymmetry underdocumented.** Requires σ₁ reachable but σ₂ can be ANY state. Paper (line 351) says "reachable states be distinguishable by observation" which undersells the actual strength. One sentence fix. (paper)

- [x] **Paper overclaims CFG and structured control flow requirements.** Fixed in 3 commits: Line 77 now states actual requirement (grammar conformance + finite nonterminals). Section IV-A retitled "Scope Restriction," rewritten to frame structured control flow as scoping decision not formal requirement. Line 248 lexical scope sentence replaced with honest scope inference framing. (paper)

---

## P2: Paper clarity & consistency

Not wrong, but confusing or could trip up reviewers.

- [x] **Audit all "structured control flow" / "lexical scope" claims.** Main body instances fixed (IV-A, line 77, line 248). Remarks "On tractability" (line 382) already correctly states "eager evaluation, no concurrency, no nondeterminism." Appendix instances will be handled by appendix triage (gate/delete). (paper)
- [x] **O's Σ-level vs π-level interface.** Fixed: O(s) now says it produces constraints at Σ level "which are then lifted to constraints over π(s)." (paper, line 103)
- [x] **O/symex confusion between Setup and Construction.** Already addressed: line 269 bridges O → symex ("the three-way decomposition above is conceptual; the mechanization shows that a single sound symex oracle suffices"), and Setup (line 277) identifies O as "the symex+ISA oracle." No change needed. (paper)
- [ ] **"No internal branching in HTH blocks" needs explicit hole-granularity constraint.** The HTH draft section asserts basic blocks have no branching, but this is only true if hole boundaries are fine enough. Either define "hole" to guarantee this or state it as an assumption. (paper, Codex #2)
- [ ] **DRAFT Branching Oracle section lags behind O = symex+ISA framing.** Lines 704-782 only list tools (S2E/angr/KLEE + Sail) without mentioning K reachability logic or the "O = symex+ISA" shorthand established at line 130. Update or delete. (paper, Codex #3)
- [x] **R* definition ambiguous.** Deleted — R* was never used anywhere in the paper. (paper)
- [x] **Completeness reads as derived rather than assumed.** Fixed: opening sentence now says "Given a complete branching oracle," and "by definition" → "by assumption." Appendix instances (704-782) will die with appendix gate. (paper)
- [ ] **Value transformation oracle section assumes no internal branching.** Lines 820-872. "Symbolically execute just that region" assumes single-path. Tie back to the HTH straight-line assumption. (paper, Codex #7)
- [ ] **Appendix sentinel detection contradicts Section IV-D.** Section IV-D (line 210) says "we cannot simply look for where sentinel *values* appear." Appendix (line 956) says "When we see κ₁ computed in the trace, we know h₁ was just evaluated." Contradiction. (paper)
- [x] **ICTAC bisimulation vs general bisimulation: different strength.** No change needed — line 374 already explains the reachability restriction is natural and excludes only irrelevant unreachable states. The asymmetry is a mathematical curiosity of π=id, not meaningful for language semantics. (paper)
- [x] **$\Sigma$ notation mixes ISA-level and LTS-level.** Already resolved: line 68 says "In the more abstract view of a labeled transition system, which we focus on in this paper, $\Sigma$ is simply the state space of $H$." No change needed. (paper)
- [x] **O* "behavioral pattern" undefined.** The parenthetical "(same control flow, same HTH structure)" IS the definition. Adequate for a notation section. No change needed. (paper)
- [x] **Forward reference to R in notation.** Accepted — forward refs within a notation list are normal. No change. (paper)
- [ ] **Simulation notation ≼ direction.** Line 111: G' ≼ M means "G' simulates M." In process algebra, ≼ often means the opposite. Anchor to a standard reference or footnote the convention. (paper)
- [ ] **GCD example assumes Python but never states it.** Lines 1081-1345. (paper)

---

## P3: Lean cleanup

Dead code and disconnected modules. Not blocking but misrepresents formalization completeness.

- [ ] **`GrammarConformant.labels_from_grammar` never used.** The field is carried but never checked by any theorem. Could be removed or noted as future work. (ConditionalSimulation.lean)
- [x] **InformationSufficiency.lean disconnected from extraction pipeline.** Resolved by removing the module entirely. Its mathematical content (one non-trivial lemma about trace splitting via label determinism) didn't justify a full module. Practical feasibility of the testing methodology is a prose claim in the paper, not a formal theorem. (InformationSufficiency.lean — deleted)
- [x] **ICTACCorrespondence → ExtractionPossibility chain not mechanized.** ~~`symexOfTraceDecomp_sound`~~ removed — was dead code, never composed with `extraction_possible`. The bridge theorems `OracleSoundFor_of_TraceCorrespondence` and `OracleCompleteFor_of_TraceCorrespondence_id` remain and are used by `bisimulation_of_TraceCorrespondence_id`. (ICTACCorrespondence.lean)
- [ ] **Dead definitions/theorems.** Including: `BranchingOracle` infrastructure, `IsMaximalTrace`/`IsBranchPoint`/`IsDeadEnd`, ~~`Sim.refl`/`Sim.trans`~~, ~~`trace_equivalence_of_sound_complete`~~, ~~`symexOfTraceDecomp_sound`~~, ~~`extractionProjection_tracked`~~/`_eq_on_tracked`~~, ~~`ofOption`~~, ~~`Reachable.extend`~~, ~~`holePositions`~~, ~~`Sim_of_sound_oracle`/`_of_complete_oracle`~~. Also removed: `trace_inclusion_of_sound_oracle`, `trace_lifting_of_complete_oracle` (only used by `trace_equivalence`). `BranchingOracle` infrastructure kept for paper correspondence — marked with docstrings. (Note: `simulation_at_coRefinement_fixpoint_gc`, `branches_complete`, and `non_controllable_internal` were previously listed here but ARE used in the extraction pipeline — removed from dead list.) (Removed with InformationSufficiency: `coveringSet`/`coveringSet_adequate`, `DistinctSentinels`, `ReachabilityOracleSoundFor`, `branch_divergence_refines`, plus all differential causality infrastructure.)
- [ ] **`extraction_bisimulation` does not reuse `extraction_possible`.** Entirely independent proof with different refinement step and oracle. Consider refactoring to share infrastructure, or document the independence. (ExtractionPossibility.lean)
- [x] **Docstring line references to scratch.tex are brittle.** Fixed: replaced stale line numbers with section names in CoRefinementConvergence.lean:98-99. (CoRefinementConvergence.lean)
- [ ] **`Function.iterate_stable` and `Finset.monotone_stabilizes` could be contributed to Mathlib.** Currently project-local in the `Function`/`Finset` namespace, risking future collision. (CoRefinementConvergence.lean)
- [x] **Multiple `open Classical in` could be one section-level `open Classical`.** Replaced 4 instances with one top-level `open Classical`. (ExtractionPossibility.lean)

---

## P4: Nice-to-have / editorial

- [ ] **HTH labeling precondition paragraph formatting.** Line 281-282: first sentence is very long, would read better split. (paper)
- [ ] **DRAFT appendix notation re-introduces O/Alt(s)/ReplayApply** without linking back to formal definitions or symex+ISA framing. (paper)
- [ ] **Naming inconsistency.** `OracleSoundFor` vs `ReachabilityOracleSoundFor` vs `ReachabilityOracleValueSound`. (Lean)
- [ ] **`IsXControllable` quantifies over ALL states (including unreachable).** Works in proofs but potentially confusing. Document the design choice. (ConditionalSimulation.lean)
- [ ] **`HTHLabel` has no well-formedness invariant.** `fromPos`/`toPos` are unbounded `Nat`, no connection to rule output length. (ConditionalSimulation.lean)
- [ ] **Redundant Mathlib import.** `import Mathlib.Logic.Relation` may be transitively available. (ConditionalSimulation.lean)
- [ ] **Consider remarking on STALAGMITE as future work.** Bettscheider & Zeller's grammar mining via symbolic parsing \cite{bettscheider2024lookma} is a structural analog of our learnability framework (symex as oracle, iterative refinement, grammar nonterminals as projection). Their approach currently lacks convergence guarantees and identifiability analysis. Improving their work using our principled refinement loop and convergence bounds could be future work worth remarking on in the paper. (paper)

---

## Decision log

Decisions about what NOT to fix and why.

- **This tranche of P1s first**: Doing this particular batch of paper-Lean accuracy fixes before P0 submission-blocking items because these specific mismatches are the more important blockers for a shepherded workshop-style venue — reviewers cross-checking the Lean will flag them.
- **Three-way co-refinement not formalized**: Acknowledged scope limitation. Paper should note it. Formalizing is future work.
- **InformationSufficiency removed**: Module deleted. One non-trivial lemma (trace splitting via label determinism) didn't justify a separate module. Practical feasibility of testing methodology is a prose claim.
- **Dead code**: Some definitions exist for conceptual completeness (branching oracles, maximal traces). Could be kept with a note or removed for a cleaner artifact. User's call.
- **`extraction_bisimulation` independence**: The different construction is mathematically necessary (reachability refinement vs non-controllability refinement). Documenting is better than forcing shared infrastructure.
- **Three-oracle → single-parameter**: Added clarifying paragraph at end of V-A explaining that Lean unifies branching + value-transformation into one `symex` parameter, grammar is structural precondition. Conceptual decomposition preserved.
- **Hidden typeclass hypotheses**: Added footnote to Main Theorem noting DecidableEq Dim, Fintype Dim, Inhabited Value as mild technical conditions for the mechanization.
- **Guard/Update vs existential oracle**: Added sentences in V-D Oracle bullet explaining that the existential projection is the mechanized form, and collapses to Guard ∧ Update when symex factors as PC + Sub (ICTAC setting).
- **Bisimulation construction honesty**: Replaced single-paragraph remark with multi-paragraph treatment. Now explains: why simulation proof can't be directly extended, the three differences (refinement step, reachability-restricted oracle, π-injectivity), how completeness follows from injectivity, and the ICTAC special case.
- **Config = Dim → Value**: Added to both Notation section (X entry) and V-D Projection bullet. Configuration type is Dim → Value, dimension-indexed observations.
- **Section V intro / bisimulation promotion**: Fixed intro to say "sound oracle" for simulation, added "with completeness, bisimulation" forward ref. Promoted bisimulation from buried remark to named Corollary with label. Explicitly states completeness is needed for reverse direction.
- **III-D completeness phrasing**: Added sentence making conditionality explicit and pointing to bisimulation Corollary as the formal result.
- **h_faithful asymmetry**: Fixed both Notation section and Remarks to say "distinguishable from all states, not just reachable ones" and explain why (IsXControllable quantifies over all states in fiber).
