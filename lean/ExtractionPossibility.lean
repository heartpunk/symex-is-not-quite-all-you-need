/-
# Extraction Possibility

End-to-end existence theorem: given a grammar-conformant implementation
with a faithful observation function over a finite dimension space,
there exist a projection π and oracle R forming a co-refinement
fixpoint — and hence yielding a simulation (via `simulation_at_coRefinement_fixpoint`).
-/

import InformationSufficiency
import CoRefinementConvergence

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
- **mkProjection X** = observe tracked dimensions, default elsewhere
- **mkOracle X** = existential witness from concrete transitions
- **refineStep X** = add dimensions witnessing non-controllable
  transition availability

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
    refinement step adds dimensions that witness why transitions are
    non-controllable. At fixpoint, faithfulness of `observe` implies
    no non-controllable transitions remain, so the preservation
    condition holds vacuously. -/
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
  -- Projection: observe tracked dimensions, default elsewhere
  let mkProj : Finset Dim → Projection HostState (Dim → Value) :=
    fun X σ d => if d ∈ X then observe σ d else default
  -- Oracle: existential witness from concrete transitions
  let mkOrc : Finset Dim →
      (HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop) :=
    fun X ℓ x x' =>
      ∃ σ σ', mkProj X σ = x ∧ gc.H_I.step σ ℓ σ' ∧ mkProj X σ' = x'
  -- Refinement: add dims witnessing non-controllable transition availability
  let refStep : Finset Dim → Finset Dim :=
    fun X => X ∪ Finset.univ.filter (fun d =>
      ∃ (σ_w σ₂_w : HostState) (ℓ_w : HTHLabel T gc.Γ.NT),
        gc.H_I.Reachable σ_w ∧
        (∃ σ_w', gc.H_I.step σ_w ℓ_w σ_w') ∧
        mkProj X σ₂_w = mkProj X σ_w ∧
        (¬∃ σ₂_w', gc.H_I.step σ₂_w ℓ_w σ₂_w') ∧
        observe σ_w d ≠ observe σ₂_w d)
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
