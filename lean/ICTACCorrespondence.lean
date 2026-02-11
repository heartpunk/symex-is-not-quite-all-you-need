/-
# ICTAC Correspondence

Bridge between the ICTAC Rocq mechanization of symbolic execution
correctness and our simulation framework. The ICTAC proof establishes
a trace correspondence theorem (Theorem 1):

  denot_fun t V = Some V' ↔ (V |= PC t) ∧ denot_sub (Sub t) V = V'

This biconditional folds guard evaluation and value transformation into
a single statement. We show it implies our split OracleSoundFor +
OracleCompleteFor, connecting the ICTAC proof to the simulation framework.

Reference: ~/code/ICTAC-DenotSymbEx/ (Traces.v, Theorem trace_correspondence)
-/

import ConditionalSimulation

/-! ## Oracle from Trace Decomposition

The ICTAC approach decomposes each trace label ℓ into:
- A **substitution** `Sub ℓ : Config → Config` (the state transformation)
- A **path condition** `PC ℓ : Config → Prop` (the feasibility guard)

The induced oracle says: R ℓ x x' iff x satisfies the path condition
and applying the substitution yields x'.
-/

/-- The oracle induced by an ICTAC-style trace decomposition:
    `R ℓ x x'` holds iff `x` satisfies the path condition of `ℓ` and
    applying the substitution of `ℓ` to `x` yields `x'`. -/
abbrev oracleOfTraceDecomp {Config : Type*} {L : Type*}
    (Sub : L → Config → Config) (PC : L → Config → Prop) :
    L → Config → Config → Prop :=
  fun ℓ x x' => PC ℓ x ∧ Sub ℓ x = x'

/-! ## Trace Correspondence

The ICTAC biconditional relates concrete execution to the symbolic
decomposition: stepping from σ to σ' via label ℓ is equivalent to
the path condition holding at π σ and the substitution mapping π σ
to π σ'. This is the abstract shape of ICTAC Theorem 1.
-/

/-- ICTAC-style trace correspondence: concrete execution of label ℓ
    from σ to σ' is equivalent to the path condition holding at π σ
    and the substitution mapping π σ to π σ'.
    Corresponds to ICTAC Theorem 1 (`trace_correspondence`). -/
abbrev TraceCorrespondence {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.step σ ℓ σ' ↔ (PC ℓ (π σ) ∧ Sub ℓ (π σ) = π σ')

/-! ## Trace Correspondence implies Oracle Soundness

The forward direction of the biconditional gives soundness: every
concrete step is captured by the induced oracle.
-/

/-- The forward direction of trace correspondence gives oracle soundness:
    every concrete step `H_I.step σ ℓ σ'` implies `R ℓ (π σ) (π σ')`. -/
theorem OracleSoundFor_of_TraceCorrespondence {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I π Sub PC) :
    OracleSoundFor H_I π (oracleOfTraceDecomp Sub PC) :=
  fun σ σ' ℓ hstep => (h_tc σ σ' ℓ).mp hstep

/-! ## Trace Correspondence implies Oracle Completeness

The backward direction gives completeness, but needs a witness σ' with
π σ' = x'. In general this requires π to be surjective. When π = id
(the ICTAC setting), surjectivity is trivial.
-/

/-- Trace correspondence + surjective π gives oracle completeness.
    Given `R ℓ (π σ) x'`, surjectivity provides `σ'` with `π σ' = x'`,
    and the backward direction of the biconditional gives the step. -/
theorem OracleCompleteFor_of_TraceCorrespondence {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I π Sub PC)
    (h_surj : Function.Surjective π) :
    OracleCompleteFor H_I π (oracleOfTraceDecomp Sub PC) := by
  intro σ x' ℓ ⟨hpc, hsub⟩
  obtain ⟨σ', hπ⟩ := h_surj x'
  exact ⟨σ', (h_tc σ σ' ℓ).mpr ⟨hpc, by rw [hsub, hπ]⟩, hπ⟩

/-! ## ICTAC Setting: π = id

In the ICTAC mechanization, HostState = Config (valuations) and π = id.
Surjectivity is trivial, so trace correspondence alone gives both
soundness and completeness. We prove completeness directly for a
cleaner proof term.
-/

/-- In the ICTAC setting (π = id), trace correspondence directly gives
    oracle completeness: take σ' = x' and apply the backward direction. -/
theorem OracleCompleteFor_of_TraceCorrespondence_id {Config : Type*} {L : Type*}
    (H_I : LTS Config L)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I id Sub PC) :
    OracleCompleteFor H_I id (oracleOfTraceDecomp Sub PC) :=
  fun σ x' ℓ ⟨hpc, hsub⟩ => ⟨x', (h_tc σ x' ℓ).mpr ⟨hpc, hsub⟩, rfl⟩
