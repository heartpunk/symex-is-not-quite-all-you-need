/-
# Extraction Possibility

End-to-end existence theorem: given a grammar-conformant implementation
with a faithful observation function over a finite dimension space,
there exist a projection π and oracle R forming a co-refinement
fixpoint — and hence yielding a simulation (via `simulation_at_coRefinement_fixpoint`).

Also provides the bridge connecting differential causality testing
(InformationSufficiency) to the co-refinement process: `branch_divergence_refines`
shows that branch divergence witnesses are valid refinement step inputs.
-/

import InformationSufficiency
import CoRefinementConvergence

/-! ## Extraction Pipeline Definitions

The co-refinement process in `extraction_possible` uses three concrete
constructions. These are extracted as top-level definitions so they can
be referenced by bridge lemmas connecting the differential causality
testing results (InformationSufficiency) to the co-refinement process
(ExtractionPossibility).
-/

/-- Projection that observes tracked dimensions, defaulting elsewhere.
    Two states have the same projected configuration iff they agree on
    all tracked dimensions in X. Used by the co-refinement process in
    `extraction_possible`. -/
abbrev extractionProjection {HostState Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value]
    (observe : HostState → Dim → Value) (X : Finset Dim) :
    Projection HostState (Dim → Value) :=
  fun σ d => if d ∈ X then observe σ d else default

/-- Oracle witnessing transitions via concrete state pairs. Sound by
    construction: given any step σ →ℓ σ', the oracle claims
    R ℓ (π σ) (π σ') with σ and σ' as witnesses. -/
abbrev extractionOracle {HostState Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value] {L : Type*}
    (H_I : LTS HostState L) (observe : HostState → Dim → Value)
    (X : Finset Dim) : L → (Dim → Value) → (Dim → Value) → Prop :=
  fun ℓ x x' =>
    ∃ σ σ', extractionProjection observe X σ = x ∧
      H_I.step σ ℓ σ' ∧ extractionProjection observe X σ' = x'

/-- Refinement step: add dimensions witnessing non-controllable transition
    availability. Dimension d is added when there exist reachable state σ
    (which can take some transition ℓ) and state σ₂ (with the same
    projection but unable to take ℓ) that differ at d.

    These are exactly the dimensions that differential causality testing
    at branch divergence points detects — see `branch_divergence_refines`. -/
open Classical in
noncomputable abbrev extractionRefineStep {HostState Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value] {L : Type*}
    (H_I : LTS HostState L) (observe : HostState → Dim → Value)
    (X : Finset Dim) : Finset Dim :=
  X ∪ Finset.univ.filter (fun d =>
    ∃ (σ_w σ₂_w : HostState) (ℓ_w : L),
      H_I.Reachable σ_w ∧
      (∃ σ_w', H_I.step σ_w ℓ_w σ_w') ∧
      extractionProjection observe X σ₂_w = extractionProjection observe X σ_w ∧
      (¬∃ σ₂_w', H_I.step σ₂_w ℓ_w σ₂_w') ∧
      observe σ_w d ≠ observe σ₂_w d)

/-! ## Bridge: Differential Causality → Refinement Step

The following bridge lemma connects the two main Lean clusters:
- **InformationSufficiency**: differential causality testing identifies
  which dimensions differ at branch divergence points
- **ExtractionPossibility**: the co-refinement process adds dimensions
  based on non-controllable transition witnesses

The bridge says: a branch divergence witness (two states with the same
projection but different transition availability, differing at dimension d)
is exactly a valid input to `extractionRefineStep`. This justifies the
paper's claim that differential causality testing discovers the dimensions
needed for co-refinement convergence.
-/

/-- Branch divergence witnesses from differential causality testing are
    valid refinement step witnesses: if two states at a branch point have
    the same projection but different observations at dimension d, and one
    can take a transition that the other cannot, then d is added by the
    refinement step.

    This bridges InformationSufficiency (which identifies dimension
    differences via differential causality testing) and ExtractionPossibility
    (which uses those dimensions in the co-refinement process). -/
open Classical in
theorem branch_divergence_refines
    {HostState Dim Value : Type*} [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    {L : Type*} {H_I : LTS HostState L}
    (observe : HostState → Dim → Value) (X : Finset Dim)
    {σ σ₂ : HostState} {ℓ : L}
    (h_reach : H_I.Reachable σ)
    (h_can : ∃ σ', H_I.step σ ℓ σ')
    (h_proj_eq : extractionProjection observe X σ₂ = extractionProjection observe X σ)
    (h_cant : ¬∃ σ₂', H_I.step σ₂ ℓ σ₂')
    {d : Dim}
    (h_diff : observe σ d ≠ observe σ₂ d)
    : d ∈ extractionRefineStep H_I observe X := by
  apply Finset.mem_union_right
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ d, σ, σ₂, ℓ, h_reach, h_can, h_proj_eq, h_cant, h_diff⟩

/-! ## End-to-End Extraction

The extraction pipeline combines:
- **Grammar conformance** (`GrammarConformant`): H_I's labels come from Γ
  and consecutive transitions are compatible.
- **Label determinism**: same state + same HTH label → same target state.
- **Adequate covering set**: every grammar rule has a template exercising it.
- **Sound reachability oracle**: dimension-aware host-level dataflow claims
  are backed by actual execution paths.
- **Faithful observation**: the observation function captures all
  transition-relevant state (injective on dimensions).

Together these guarantee the existence of a projection π and oracle R
satisfying `IsCoRefinementFixpoint` — the oracle captures every concrete
transition, and non-controllable transitions preserve π.

The proof constructs a `CoRefinementProcess` with:
- **Config** = `Dim → Value` (dimension-indexed observations)
- **mkProjection X** = `extractionProjection`: observe tracked dimensions,
  default elsewhere
- **mkOracle X** = `extractionOracle`: existential witness from concrete
  transitions
- **refineStep X** = `extractionRefineStep`: add dimensions witnessing
  non-controllable transition availability

At the fixpoint, no non-controllable transitions exist: any
counterexample σ₂ (same projection, can't take ℓ) agrees with σ on
all dimensions (tracked by projection equality, untracked by fixpoint
condition), so σ₂ = σ by faithfulness — contradicting the assumption
that σ₂ can't take ℓ while σ can.
-/

open Classical in
/-- End-to-end extraction possibility: given a grammar-conformant
    implementation with a faithful observation function over a finite
    dimension space, there exist a projection and oracle forming a
    co-refinement fixpoint — and hence yielding a simulation of H_I.

    The proof constructs a concrete `CoRefinementProcess` whose
    refinement step (`extractionRefineStep`) adds dimensions that witness
    why transitions are non-controllable. At fixpoint, faithfulness of
    `observe` implies no non-controllable transitions remain, so the
    preservation condition holds vacuously. -/
theorem extraction_possible
    {HostState T Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (h_label_det : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ₁ → gc.H_I.step σ ℓ σ₂ → σ₁ = σ₂)
    (templates : List (Template T gc.Γ.NT))
    (h_adequate : AdequateCoveringSet gc.Γ.rules templates)
    (reach : ReachabilityOracle HostState Dim)
    (h_reach_sound : ReachabilityOracleSoundFor gc.H_I reach)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    : ∃ (Config : Type*) (π : Projection HostState Config)
        (R : HTHLabel T gc.Γ.NT → Config → Config → Prop),
      IsCoRefinementFixpoint gc.H_I π R := by
  let mkProj := extractionProjection observe
  let mkOrc := extractionOracle gc.H_I observe
  let refStep := extractionRefineStep gc.H_I observe
  -- Build co-refinement process
  let proc : CoRefinementProcess HostState (Dim → Value) Dim
      (HTHLabel T gc.Γ.NT) := {
    H_I := gc.H_I
    mkProjection := mkProj
    mkOracle := mkOrc
    refineStep := refStep
    refine_inflationary := fun X => Finset.subset_union_left
    sound_at_fixpoint := by
      intro X _hfp σ σ' ℓ hstep
      exact ⟨σ, σ', rfl, hstep, rfl⟩
    non_ctrl_at_fixpoint := by
      intro X hfp σ σ' ℓ h_reach hstep h_not_ctrl
      -- At fixpoint, ¬IsXControllable is impossible:
      -- any counterexample σ₂ must equal σ by faithfulness.
      exfalso; apply h_not_ctrl
      intro σ₂ hproj_eq
      by_cases h_can : ∃ s', gc.H_I.step σ₂ ℓ s'
      · exact h_can
      · -- σ₂ can't take ℓ. Show σ₂ = σ, contradicting this.
        have h_eq : σ₂ = σ := by
          apply h_faithful
          intro d
          by_cases hd : d ∈ X
          · -- d ∈ X: projection equality gives agreement
            have h_pe : (if d ∈ X then observe σ₂ d else (default : Value)) =
                (if d ∈ X then observe σ d else default) := congr_fun hproj_eq d
            rw [if_pos hd, if_pos hd] at h_pe
            exact h_pe
          · -- d ∉ X: fixpoint ensures d would be in X if they differed
            by_contra h_ne
            have h_mem : d ∈ refStep X := by
              apply Finset.mem_union_right
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ d, σ, σ₂, ℓ, h_reach, ⟨σ', hstep⟩,
                     hproj_eq, h_can, fun h => h_ne h.symm⟩
            rw [show refStep X = X from hfp] at h_mem
            exact hd h_mem
        subst h_eq; exact ⟨σ', hstep⟩
  }
  -- Apply yields_fixpoint to get the co-refinement fixpoint
  obtain ⟨X, hfix⟩ := proc.yields_fixpoint ∅
  exact ⟨Dim → Value, mkProj X, mkOrc X, hfix⟩

/-! ## End-to-End Pipeline: Inputs → Simulation

The pipeline theorem composes two independent results:
1. **`extraction_possible`**: co-refinement converges to a fixpoint
2. **`simulation_at_coRefinement_fixpoint`**: fixpoint yields simulation

The testing infrastructure hypotheses (templates, oracle, label
determinism) enable discovering dimensions via differential causality
testing (`differential_causality_identifies_projection` +
`branch_divergence_refines`). The faithfulness hypothesis enables the
convergence proof. Together they justify the full pipeline.
-/

open Classical in
/-- End-to-end extraction pipeline: the full set of pipeline inputs —
    grammar conformance, label determinism, covering set, reachability
    oracle, observation function with faithfulness — yield a simulation
    of the implementation by an oracle-constructed LTS.

    Composes `extraction_possible` (co-refinement converges) with
    `simulation_at_coRefinement_fixpoint` (fixpoint yields simulation).
    The conclusion is the paper's main claim: there exists G' that
    simulates H_I. -/
theorem extraction_pipeline
    {HostState T Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (h_label_det : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ₁ → gc.H_I.step σ ℓ σ₂ → σ₁ = σ₂)
    (templates : List (Template T gc.Γ.NT))
    (h_adequate : AdequateCoveringSet gc.Γ.rules templates)
    (reach : ReachabilityOracle HostState Dim)
    (h_reach_sound : ReachabilityOracleSoundFor gc.H_I reach)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    : ∃ (Config : Type*) (π : Projection HostState Config)
        (R : HTHLabel T gc.Γ.NT → Config → Config → Prop),
      (LTS.ofOracle (π gc.H_I.init) R).Simulates gc.H_I (fun x σ => π σ = x) := by
  obtain ⟨Config, π, R, h_fix⟩ := extraction_possible gc h_label_det
    templates h_adequate reach h_reach_sound observe h_faithful
  exact ⟨Config, π, R, simulation_at_coRefinement_fixpoint gc.H_I π R h_fix⟩
