/-
# Co-Refinement Convergence

The paper's extraction technique involves co-refinement across three
dimensions: configuration refinement (π), region refinement (HTH), and
semantic refinement (R_ℓ). These refine together until all three
stabilize.

The convergence argument (scratch.tex §Remarks): the oracle O operates
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
    This formalizes the paper's convergence argument (scratch.tex line 230,
    line 323). -/
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
At the fixpoint, three semantic properties hold simultaneously:

1. **Oracle soundness**: R correctly captures every concrete transition
   through the stabilized π.
2. **Branch completeness**: Every X-controllable branch at a reachable
   branch point is in R's domain — the extraction has discovered all
   branches whose outcome depends on projected state.
3. **Non-controllable preservation**: Transitions not controllable via
   projected state don't change the projection — they're invisible to G'.

Together these ensure the extracted LTS faithfully represents H_I's
behavior at the granularity captured by π.
-/

/-- The co-refinement process has reached a fixpoint: the oracle is sound,
    all X-controllable branches are discovered, and non-X-controllable
    transitions preserve the projection. -/
structure IsCoRefinementFixpoint {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop where
  /-- The oracle is sound: every concrete step is captured -/
  sound : OracleSoundFor H_I π R
  /-- X-controllable branches are complete: every X-controllable label
      at a reachable branch point is in R's domain -/
  branches_complete : ∀ (σ σ' : HostState) (ℓ : L),
    H_I.Reachable σ → H_I.IsBranchPoint σ →
    H_I.step σ ℓ σ' → IsXControllable H_I π σ ℓ →
    ∃ (x' : Config), R ℓ (π σ) x'
  /-- Non-X-controllable transitions preserve the projection -/
  non_controllable_preserves : ∀ (σ σ' : HostState) (ℓ : L),
    H_I.Reachable σ → H_I.step σ ℓ σ' →
    ¬IsXControllable H_I π σ ℓ →
    π σ = π σ'

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
    (LTS.ofOracle (π H_I.init) R).Simulates H_I (fun x σ => π σ = x) :=
  simulation_of_sound_oracle H_I π R h_fix.sound
