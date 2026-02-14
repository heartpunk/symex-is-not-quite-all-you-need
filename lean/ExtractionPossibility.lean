/-
# Extraction Possibility

End-to-end existence theorem: given a grammar-conformant implementation
with a faithful observation function over a finite dimension space,
there exist a projection π and oracle R forming a co-refinement
fixpoint — and hence yielding a simulation (via `simulation_at_coRefinement_fixpoint`).
-/

import CoRefinementConvergence

open Classical

/-! ## Extraction Pipeline Definitions

The co-refinement process in `extraction_possible` uses three concrete
constructions: a projection that observes tracked dimensions, an oracle
that projects symex claims through that projection, and a refinement
step that adds dimensions witnessing non-controllable transitions.
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

/-- Oracle witnessing transitions via a symbolic execution oracle
    projected through `extractionProjection`. Given a host-state-level
    symex oracle (sound approximation of H_I.step), the projected oracle
    claims R ℓ x x' when there exist concrete states σ, σ' with matching
    projections and the symex oracle relating them.

    In practice, the symex oracle is instantiated by:
    - ICTAC trace_correspondence: `symex ℓ σ σ' := PC ℓ σ ∧ Sub ℓ σ = σ'`
    - Lucanu et al.'s generic symbolic execution framework
    - Any symbolic execution engine with proved soundness -/
abbrev extractionOracle {HostState Dim Value : Type*}
    [DecidableEq Dim] [Inhabited Value] {L : Type*}
    (symex : L → HostState → HostState → Prop)
    (observe : HostState → Dim → Value)
    (X : Finset Dim) : L → (Dim → Value) → (Dim → Value) → Prop :=
  fun ℓ x x' =>
    ∃ σ σ', extractionProjection observe X σ = x ∧
      symex ℓ σ σ' ∧ extractionProjection observe X σ' = x'


/-- Refinement step: add dimensions witnessing non-controllable transition
    availability. Dimension d is added when there exist reachable state σ
    (which can take some transition ℓ) and state σ₂ (with the same
    projection but unable to take ℓ) that differ at d.

    In practice, these are the dimensions that differential causality
    testing at branch divergence points detects. -/
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

/-! ## End-to-End Extraction

The extraction pipeline combines:
- **Grammar conformance** (`GrammarConformant`): H_I's labels come from Γ.
- **Symbolic execution oracle** (`symex`): a sound approximation of H_I's
  transition relation. Soundness means every concrete transition is
  captured by the oracle.
- **Faithful observation**: the observation function captures all
  transition-relevant state (injective on reachable states).

Together these guarantee the existence of a projection π and oracle R
satisfying `IsCoRefinementFixpoint` — the symex oracle's claims are
projected through π to form R, and non-controllable transitions
preserve π.

The proof constructs a `CoRefinementProcess` with:
- **Config** = `Dim → Value` (dimension-indexed observations)
- **mkProjection X** = `extractionProjection`: observe tracked dimensions,
  default elsewhere
- **mkOracle X** = `extractionOracle`: project symex oracle through π_X
- **refineStep X** = `extractionRefineStep`: add dimensions witnessing
  non-controllable transition availability

At the fixpoint, no non-controllable transitions exist: any
counterexample σ₂ (same projection, can't take ℓ) agrees with σ on
all dimensions (tracked by projection equality, untracked by fixpoint
condition), so σ = σ₂ by faithfulness (σ is reachable) — contradicting
the assumption that σ₂ can't take ℓ while σ can.
-/


/-- End-to-end extraction possibility: given a grammar-conformant
    implementation, a sound symbolic execution oracle, and a faithful
    observation function over a finite dimension space, there exist a
    projection and oracle forming a co-refinement fixpoint — and hence
    yielding a simulation of H_I.

    The symex oracle is a sound approximation of H_I's transition
    relation, instantiated in practice by ICTAC's `trace_correspondence`
    or Lucanu et al.'s generic symbolic execution framework.

    The proof constructs a concrete `CoRefinementProcess` whose
    refinement step (`extractionRefineStep`) adds dimensions that witness
    why transitions are non-controllable. At fixpoint, faithfulness of
    `observe` on reachable states implies no non-controllable transitions
    remain, so the preservation condition holds vacuously.

    Faithfulness is only required on reachable states: the observation
    function need not distinguish unreachable states from each other. -/
theorem extraction_possible
    {HostState T Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      gc.H_I.Reachable σ₁ →
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    (symex : HTHLabel T gc.Γ.NT → HostState → HostState → Prop)
    (h_symex_sound : ∀ (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ' → symex ℓ σ σ')
    : ∃ (π : Projection HostState (Dim → Value))
        (R : HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop),
      IsCoRefinementFixpoint gc.H_I π R := by
  let mkProj := extractionProjection observe
  let mkOrc := extractionOracle symex observe
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
      exact ⟨σ, σ', rfl, h_symex_sound σ σ' ℓ hstep, rfl⟩
    non_ctrl_at_fixpoint := by
      intro X hfp σ σ' ℓ h_reach hstep h_not_ctrl
      -- At fixpoint, ¬IsXControllable is impossible:
      -- any counterexample σ₂ must equal σ by faithfulness.
      exfalso; apply h_not_ctrl
      intro σ₂ hproj_eq
      by_cases h_can : ∃ s', gc.H_I.step σ₂ ℓ s'
      · exact h_can
      · -- σ₂ can't take ℓ. Show σ = σ₂, contradicting this.
        have h_eq : σ = σ₂ := by
          apply h_faithful _ _ h_reach
          intro d
          by_cases hd : d ∈ X
          · -- d ∈ X: projection equality gives agreement
            have h_pe : (if d ∈ X then observe σ₂ d else (default : Value)) =
                (if d ∈ X then observe σ d else default) := congr_fun hproj_eq d
            rw [if_pos hd, if_pos hd] at h_pe
            exact h_pe.symm
          · -- d ∉ X: fixpoint ensures d would be in X if they differed
            by_contra h_ne
            have h_mem : d ∈ refStep X := by
              apply Finset.mem_union_right
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ d, σ, σ₂, ℓ, h_reach, ⟨σ', hstep⟩,
                     hproj_eq, h_can, h_ne⟩
            rw [show refStep X = X from hfp] at h_mem
            exact hd h_mem
        subst h_eq; exact ⟨σ', hstep⟩
  }
  -- Apply yields_fixpoint to get the co-refinement fixpoint
  obtain ⟨X, hfix⟩ := proc.yields_fixpoint ∅
  exact ⟨mkProj X, mkOrc X, hfix⟩

/-! ## End-to-End Pipeline: Inputs → Simulation

The pipeline theorem composes two independent results:
1. **`extraction_possible`**: co-refinement converges to a fixpoint
2. **`simulation_at_coRefinement_fixpoint`**: fixpoint yields simulation

The symex oracle captures how transitions transform state; the
co-refinement process discovers which dimensions to track.
-/


/-- End-to-end extraction pipeline: grammar conformance, a sound symex
    oracle, observation function, and faithfulness on reachable states
    yield a simulation of the implementation by an oracle-constructed LTS.

    Composes `extraction_possible` (co-refinement converges) with
    `simulation_at_coRefinement_fixpoint` (fixpoint yields simulation).
    The conclusion is the paper's main claim: given a sound symbolic
    execution oracle (instantiated by ICTAC trace_correspondence or
    Lucanu et al.'s generic framework), there exists G' that
    simulates H_I. -/
theorem extraction_pipeline
    {HostState T Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      gc.H_I.Reachable σ₁ →
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    (symex : HTHLabel T gc.Γ.NT → HostState → HostState → Prop)
    (h_symex_sound : ∀ (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ' → symex ℓ σ σ')
    : ∃ (π : Projection HostState (Dim → Value))
        (R : HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop),
      (LTS.ofOracle (π gc.H_I.init) R).Simulates gc.H_I (fun x σ => π σ = x) := by
  obtain ⟨π, R, h_fix⟩ :=
    extraction_possible gc observe h_faithful symex h_symex_sound
  exact ⟨π, R, simulation_at_coRefinement_fixpoint gc.H_I π R h_fix⟩

/-! ## Extraction Bisimulation

With an exact symbolic execution oracle (sound AND complete, i.e.,
biconditional with H_I.step), the extraction pipeline yields
bisimulation: G' simulates H_I and H_I simulates G'.

The proof uses a reachability refinement that tracks observation
disagreements among reachable states. At the resulting fixpoint,
the projection π is injective on reachable states: any two reachable
states with the same projection agree on all dimensions, so h_faithful
gives equality. This makes oracle completeness trivial: the oracle's
existential witness σ₀ equals the query state σ.

No observation-determinism or functional Sub hypothesis is needed —
the strengthened fixpoint does all the work. The only additional
hypothesis beyond `extraction_pipeline` is `h_symex_complete`.
-/


/-- End-to-end extraction bisimulation: with an exact symbolic execution
    oracle (biconditional with H_I.step), the extraction pipeline yields
    bisimulation between the oracle LTS and H_I.

    The only additional hypothesis beyond `extraction_pipeline` is
    `h_symex_complete`: every symex claim corresponds to a real step.
    Together with `h_symex_sound`, this makes symex an exact
    characterization of H_I.step. In the ICTAC setting, this follows
    directly from `trace_correspondence` (see
    `bisimulation_of_TraceCorrespondence_id`).

    The proof constructs a reachability-refined fixpoint where π is
    injective on reachable states, making oracle completeness trivial:
    the oracle's witness state equals the query state.

    The simulation relations thread reachability: both directions only
    involve states reachable from H_I.init. -/
theorem extraction_bisimulation
    {HostState T Dim Value : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      gc.H_I.Reachable σ₁ →
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    (symex : HTHLabel T gc.Γ.NT → HostState → HostState → Prop)
    (h_symex_sound : ∀ (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ' → symex ℓ σ σ')
    (h_symex_complete : ∀ (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      symex ℓ σ σ' → gc.H_I.step σ ℓ σ')
    : ∃ (π : Projection HostState (Dim → Value))
        (R : HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop),
      let G' := LTS.ofOracle (π gc.H_I.init) R
      G'.Simulates gc.H_I (fun x σ => π σ = x ∧ gc.H_I.Reachable σ) ∧
      gc.H_I.Simulates G' (fun σ x => π σ = x ∧ gc.H_I.Reachable σ) := by
  -- Reachability refinement: track dims where reachable states disagree
  let refStep : Finset Dim → Finset Dim := fun X =>
    X ∪ Finset.univ.filter (fun d =>
      ∃ (σ₁ σ₂ : HostState),
        gc.H_I.Reachable σ₁ ∧ gc.H_I.Reachable σ₂ ∧
        extractionProjection observe X σ₁ = extractionProjection observe X σ₂ ∧
        observe σ₁ d ≠ observe σ₂ d)
  have h_infl : DimInflationary refStep := fun X => Finset.subset_union_left
  obtain ⟨n, h_conv⟩ := dimRefinement_converges refStep h_infl ∅
  let X := refStep^[n] ∅
  have h_fp : refStep X = X := by
    show refStep (refStep^[n] ∅) = refStep^[n] ∅
    have : refStep^[n + 1] ∅ = refStep^[n] ∅ := h_conv.symm
    rwa [Function.iterate_succ_apply'] at this
  -- Definitions at fixpoint
  let π := extractionProjection observe X
  let R : HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop :=
    fun ℓ x x' =>
      ∃ σ σ', gc.H_I.Reachable σ ∧ π σ = x ∧ symex ℓ σ σ' ∧ π σ' = x'
  -- Key: reachable π-injectivity at fixpoint
  have h_π_inj : ∀ σ₁ σ₂ : HostState,
      gc.H_I.Reachable σ₁ → gc.H_I.Reachable σ₂ →
      π σ₁ = π σ₂ → σ₁ = σ₂ := by
    intro σ₁ σ₂ hr₁ hr₂ hπ
    apply h_faithful σ₁ σ₂ hr₁
    intro d
    by_cases hd : d ∈ X
    · have h_pe : (if d ∈ X then observe σ₁ d else (default : Value)) =
          (if d ∈ X then observe σ₂ d else default) := congr_fun hπ d
      rw [if_pos hd, if_pos hd] at h_pe
      exact h_pe
    · by_contra hne
      have h_mem : d ∈ refStep X := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ d, σ₁, σ₂, hr₁, hr₂, hπ, hne⟩)
      rw [h_fp] at h_mem
      exact hd h_mem
  -- Both simulation directions
  refine ⟨π, R, ?_, ?_⟩
  -- Forward: G' simulates H_I
  · exact {
      init := ⟨rfl, Relation.ReflTransGen.refl⟩
      step_match := by
        intro x σ ℓ σ' ⟨hrel, hr⟩ hstep
        subst hrel
        exact ⟨π σ',
          ⟨σ, σ', hr, rfl, h_symex_sound σ σ' ℓ hstep, rfl⟩,
          rfl, hr.step hstep⟩
    }
  -- Reverse: H_I simulates G'
  · exact {
      init := ⟨rfl, Relation.ReflTransGen.refl⟩
      step_match := by
        intro σ x ℓ x' ⟨hrel, hr⟩ hR
        subst hrel
        obtain ⟨σ₀, σ₀', hr₀, hπ₀, hsym, hπ₀'⟩ := hR
        have h_eq := h_π_inj σ₀ σ hr₀ hr hπ₀
        rw [h_eq] at hsym
        have h_real := h_symex_complete σ σ₀' ℓ hsym
        exact ⟨σ₀', h_real, hπ₀', hr.step h_real⟩
    }
