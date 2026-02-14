/-
# Co-Refinement Convergence

The paper's extraction technique involves co-refinement across three
dimensions: configuration refinement (π), region refinement (HTH), and
semantic refinement (R_ℓ). These refine together until all three
stabilize.

The convergence argument (main.tex §Remarks): the oracle O operates
at the full Σ level, so it can always make progress regardless of the
current π. Since the tracked dimension set X grows monotonically and
the dimension space is finite, the process must terminate.

This module proves the abstract convergence lemma and applies it to
the co-refinement setting.
-/

import ConditionalSimulation

/-! ## Monotone Finset Stabilization

A monotone increasing sequence of finsets over a finite type must
eventually stabilize: the cardinality is non-decreasing and bounded
by the cardinality of the type.
-/

/-- A monotone increasing sequence of finsets over a finite type
    eventually stabilizes: there exists `n` with `s n = s (n + 1)`. -/
theorem Finset.monotone_stabilizes {α : Type*} [DecidableEq α] [Fintype α]
    (s : ℕ → Finset α) (h_mono : ∀ n, s n ⊆ s (n + 1)) :
    ∃ n, s n = s (n + 1) := by
  by_contra h_all_ne
  push_neg at h_all_ne
  -- Every step is a strict superset
  have h_ssubset : ∀ n, s n ⊂ s (n + 1) :=
    fun n => (h_mono n).ssubset_of_ne (h_all_ne n)
  -- So cardinality strictly increases at each step
  have h_card_lt : ∀ n, (s n).card < (s (n + 1)).card :=
    fun n => Finset.card_lt_card (h_ssubset n)
  -- Therefore card grows at least linearly: n ≤ (s n).card
  have h_lower : ∀ n, n ≤ (s n).card := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (h_card_lt n))
  -- But card is bounded by the type's cardinality
  have h_upper := Finset.card_le_univ (s (Fintype.card α + 1))
  -- Contradiction: Fintype.card α + 1 ≤ card ≤ Fintype.card α
  exact absurd (Nat.le_trans (h_lower _) h_upper) (by omega)

/-! ## Iterated Function Fixpoints

When iterating a function, once we reach a fixpoint (f^[n] a = f^[n+1] a),
the iteration stays at that point forever.
-/

/-- Once an iterated function reaches a fixpoint, it stays there. -/
theorem Function.iterate_stable {α : Type*}
    (f : α → α) (a : α)
    {n : ℕ} (h_fix : f^[n] a = f^[n + 1] a) :
    ∀ m, f^[n + m] a = f^[n] a := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    -- f^[n + (m+1)] a = f^[(n+m) + 1] a = f (f^[n+m] a) = f (f^[n] a) = f^[n+1] a = f^[n] a
    have h_eq : n + (m + 1) = (n + m) + 1 := Nat.add_assoc n m 1
    conv_lhs => rw [h_eq]
    rw [Function.iterate_succ_apply', ih]
    rw [← Function.iterate_succ_apply' f n a]
    exact h_fix.symm

/-! ## Co-Refinement Convergence

The co-refinement process iteratively grows the tracked dimension set X.
At each step, the oracle O (operating at the full host-state Σ level)
may discover that a transition depends on state not currently in X,
triggering π-refinement (adding dimensions to X).

The key non-circularity property: O sees all of Σ, so its discoveries
are independent of which dimensions X currently tracks. The projection π
only determines what gets included in the extracted G', not what O can
discover.

We model the dimension refinement as an inflationary endofunction on
`Finset Dim`: the step function only adds dimensions, never removes.
Since `Dim` is finite, the iteration must stabilize.
-/

/-- A refinement step is inflationary on dimensions when it only adds
    tracked dimensions, never removes. -/
abbrev DimInflationary {Dim : Type*} [DecidableEq Dim]
    (step : Finset Dim → Finset Dim) : Prop :=
  ∀ s, s ⊆ step s

/-- An inflationary dimension refinement on a finite type converges
    when iterated: there exists `n` where the dimension set stabilizes.
    This formalizes the paper's convergence argument (main.tex,
    Section V-C "Bootstrapping and Co-Refinement" and Section V-E
    "Main Theorem"). -/
theorem dimRefinement_converges {Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    (step : Finset Dim → Finset Dim)
    (h_infl : DimInflationary step)
    (s₀ : Finset Dim) :
    ∃ n, step^[n] s₀ = step^[n + 1] s₀ :=
  Finset.monotone_stabilizes (fun n => step^[n] s₀) (fun n => by
    show step^[n] s₀ ⊆ step^[n + 1] s₀
    rw [Function.iterate_succ_apply']
    exact h_infl (step^[n] s₀))

/-- At convergence, the dimension set is a fixpoint of the step function
    and remains so at all subsequent iterations. -/
theorem dimRefinement_stable {Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    (step : Finset Dim → Finset Dim)
    (s₀ : Finset Dim)
    {n : ℕ} (h_fix : step^[n] s₀ = step^[n + 1] s₀) :
    ∀ m, step^[n + m] s₀ = step^[n] s₀ :=
  Function.iterate_stable step s₀ h_fix

/-! ## Co-Refinement Fixpoint

The abstract convergence above shows dimension refinement terminates.
At the fixpoint, two independent semantic properties hold:

1. **Oracle soundness**: R correctly captures every concrete transition
   through the stabilized π.
2. **Non-controllable preservation**: Transitions not controllable via
   projected state don't change the projection — they're invisible to G'.

A third property — **branch completeness** (every X-controllable branch
at a reachable branch point is in R's domain) — follows from soundness
alone: given any concrete step, soundness provides the R witness.

Together these ensure the extracted LTS faithfully represents H_I's
behavior at the granularity captured by π.
-/

/-- The co-refinement process has reached a fixpoint: the oracle is sound
    and non-X-controllable transitions preserve the projection.
    Branch completeness (X-controllable branches are in R's domain)
    is derived from soundness — see `branches_complete` below. -/
structure IsCoRefinementFixpoint {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop where
  /-- The oracle is sound: every concrete step is captured -/
  sound : OracleSoundFor H_I π R
  /-- Non-X-controllable transitions preserve the projection -/
  non_controllable_preserves : ∀ (σ σ' : HostState) (ℓ : L),
    H_I.Reachable σ → H_I.step σ ℓ σ' →
    ¬IsXControllable H_I π σ ℓ →
    π σ = π σ'

/-- X-controllable branch completeness follows from oracle soundness:
    given `H_I.step σ ℓ σ'`, soundness gives `R ℓ (π σ) (π σ')`,
    witnessing `∃ x', R ℓ (π σ) x'`. The reachability, branch point,
    and controllability hypotheses are unused — soundness alone suffices. -/
theorem IsCoRefinementFixpoint.branches_complete
    {HostState Config : Type*} {L : Type*}
    {H_I : LTS HostState L} {π : Projection HostState Config}
    {R : L → Config → Config → Prop}
    (h_fix : IsCoRefinementFixpoint H_I π R)
    (σ σ' : HostState) (ℓ : L)
    (h_reach : H_I.Reachable σ) (_h_bp : H_I.IsBranchPoint σ)
    (h_step : H_I.step σ ℓ σ') (_h_ctrl : IsXControllable H_I π σ ℓ) :
    ∃ (x' : Config), R ℓ (π σ) x' :=
  ⟨π σ', h_fix.sound σ σ' ℓ h_reach h_step⟩

/-- At a co-refinement fixpoint, non-X-controllable transitions from
    reachable states are implementation-internal: they fire but don't
    change the projected state, making them invisible to G'. -/
theorem IsCoRefinementFixpoint.non_controllable_internal
    {HostState Config : Type*} {L : Type*}
    {H_I : LTS HostState L} {π : Projection HostState Config}
    {R : L → Config → Config → Prop}
    (h_fix : IsCoRefinementFixpoint H_I π R)
    {σ σ' : HostState} {ℓ : L}
    (h_reach : H_I.Reachable σ) (h_step : H_I.step σ ℓ σ')
    (h_not_ctrl : ¬IsXControllable H_I π σ ℓ) :
    IsImplementationInternal H_I π σ σ' ℓ :=
  ⟨h_step, h_fix.non_controllable_preserves σ σ' ℓ h_reach h_step h_not_ctrl⟩

/-- At a co-refinement fixpoint, the oracle LTS simulates H_I.
    This connects the fixpoint characterization to the core simulation
    result: the fixpoint gives soundness, soundness gives simulation. -/
theorem simulation_at_coRefinement_fixpoint
    {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_fix : IsCoRefinementFixpoint H_I π R) :
    (LTS.ofOracle (π H_I.init) R).Simulates H_I
      (fun x σ => π σ = x ∧ H_I.Reachable σ) :=
  simulation_of_sound_oracle H_I π R h_fix.sound

/-- Specialization: at a co-refinement fixpoint for a grammar-conformant
    implementation, the oracle LTS simulates H_I. -/
theorem simulation_at_coRefinement_fixpoint_gc
    {HostState T : Type*}
    (gc : GrammarConformant HostState T)
    {Config : Type*} (π : Projection HostState Config)
    (R : HTHLabel T gc.Γ.NT → Config → Config → Prop)
    (h_fix : IsCoRefinementFixpoint gc.H_I π R) :
    (LTS.ofOracle (π gc.H_I.init) R).Simulates gc.H_I
      (fun x σ => π σ = x ∧ gc.H_I.Reachable σ) :=
  simulation_at_coRefinement_fixpoint gc.H_I π R h_fix

/-! ## Co-Refinement Process

The co-refinement process iteratively discovers which dimensions of the
host state matter for faithful simulation. At each step, the oracle
(operating at the full Σ level) may discover transitions that depend on
state not currently tracked, triggering dimension refinement.

A `CoRefinementProcess` bundles the LTS, the mapping from tracked dimensions
to projections and oracles, and the refinement step. The key axioms —
`sound_at_fixpoint` and `non_ctrl_at_fixpoint` — encode the paper's argument
that once dimensions stabilize, the oracle correctly captures all behavior
visible through the induced projection.
-/

/-- A co-refinement process: iteratively refines the tracked dimension set
    until the oracle stabilizes. The refinement step only adds dimensions
    (inflationary), and at a fixpoint the induced oracle is sound and
    non-controllable transitions preserve the projection. -/
structure CoRefinementProcess (HostState Config Dim : Type*) [DecidableEq Dim]
    (L : Type*) where
  /-- The underlying LTS -/
  H_I : LTS HostState L
  /-- Given tracked dimensions, produce a projection -/
  mkProjection : Finset Dim → Projection HostState Config
  /-- Given tracked dimensions, produce an oracle -/
  mkOracle : Finset Dim → (L → Config → Config → Prop)
  /-- The refinement step: run oracle, discover new dimensions -/
  refineStep : Finset Dim → Finset Dim
  /-- Refinement only adds dimensions -/
  refine_inflationary : DimInflationary refineStep
  /-- At a fixpoint, the induced oracle is sound -/
  sound_at_fixpoint : ∀ X, refineStep X = X →
    OracleSoundFor H_I (mkProjection X) (mkOracle X)
  /-- At a fixpoint, non-X-controllable transitions preserve projection -/
  non_ctrl_at_fixpoint : ∀ X, refineStep X = X →
    ∀ (σ σ' : HostState) (ℓ : L),
      H_I.Reachable σ → H_I.step σ ℓ σ' →
      ¬IsXControllable H_I (mkProjection X) σ ℓ →
      mkProjection X σ = mkProjection X σ'

/-- A co-refinement process over a finite dimension type yields a
    co-refinement fixpoint: iterate the refinement step from any initial
    dimension set until it stabilizes. At stabilization, the induced
    oracle and projection satisfy `IsCoRefinementFixpoint`. -/
theorem CoRefinementProcess.yields_fixpoint
    {HostState Config Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    {L : Type*}
    (proc : CoRefinementProcess HostState Config Dim L)
    (X₀ : Finset Dim) :
    ∃ X : Finset Dim,
      IsCoRefinementFixpoint proc.H_I (proc.mkProjection X) (proc.mkOracle X) := by
  obtain ⟨n, h_fix⟩ := dimRefinement_converges proc.refineStep proc.refine_inflationary X₀
  refine ⟨proc.refineStep^[n] X₀, ?_⟩
  have h_fp : proc.refineStep (proc.refineStep^[n] X₀) = proc.refineStep^[n] X₀ := by
    have : proc.refineStep^[n + 1] X₀ = proc.refineStep^[n] X₀ := h_fix.symm
    rwa [Function.iterate_succ_apply'] at this
  exact ⟨proc.sound_at_fixpoint _ h_fp, proc.non_ctrl_at_fixpoint _ h_fp⟩

/-- End-to-end: a co-refinement process over a finite dimension type
    yields a simulation — the oracle LTS at the stabilized dimension
    set simulates H_I. -/
theorem CoRefinementProcess.yields_simulation
    {HostState Config Dim : Type*} [DecidableEq Dim] [Fintype Dim]
    {L : Type*}
    (proc : CoRefinementProcess HostState Config Dim L)
    (X₀ : Finset Dim) :
    ∃ X : Finset Dim,
      (LTS.ofOracle (proc.mkProjection X proc.H_I.init) (proc.mkOracle X)).Simulates
        proc.H_I (fun x σ => proc.mkProjection X σ = x ∧ proc.H_I.Reachable σ) := by
  obtain ⟨X, h_fix⟩ := proc.yields_fixpoint X₀
  exact ⟨X, simulation_at_coRefinement_fixpoint proc.H_I _ _ h_fix⟩
