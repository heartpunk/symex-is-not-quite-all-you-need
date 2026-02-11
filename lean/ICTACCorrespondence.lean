/-
# ICTAC Correspondence

Bridge between the ICTAC Rocq mechanization of symbolic execution
correctness and our oracle-based simulation framework.

The ICTAC proof establishes a trace correspondence theorem (Theorem 1):
  `denot_fun t V = Some V' ↔ (V |= PC t) ∧ denot_sub (Sub t) V = V'`
which folds guard evaluation (path condition) and value transformation
(substitution) into a single biconditional. We show this implies our
split OracleSoundFor + OracleCompleteFor.

Reference: `~/code/ICTAC-DenotSymbEx/Traces.v`
-/

import ConditionalSimulation

/-! ## Oracle from Trace Decomposition

Given a substitution function `Sub : L → Config → Config` and a path
condition predicate `PC : L → Config → Prop`, the induced oracle
relates x to x' under label ℓ iff x satisfies the path condition
and applying the substitution yields x'.
-/

/-- The oracle induced by ICTAC-style trace decomposition:
    `R ℓ x x'` holds iff `x` satisfies the path condition of `ℓ`
    and applying the substitution of `ℓ` to `x` yields `x'`. -/
abbrev oracleOfTraceDecomp {Config : Type*} {L : Type*}
    (Sub : L → Config → Config) (PC : L → Config → Prop) :
    L → Config → Config → Prop :=
  fun ℓ x x' => PC ℓ x ∧ Sub ℓ x = x'

/-! ## Trace Correspondence

The ICTAC biconditional: concrete execution of label ℓ from σ to σ'
is equivalent to the path condition holding at π σ and the substitution
mapping π σ to π σ'. This is Theorem 1 of the ICTAC mechanization,
lifted to our generic LTS/projection framework.
-/

/-- ICTAC-style trace correspondence: concrete execution is equivalent
    to path condition satisfaction plus substitution application.
    Corresponds to ICTAC `trace_correspondence` (Theorem 1). -/
abbrev TraceCorrespondence {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.step σ ℓ σ' ↔ (PC ℓ (π σ) ∧ Sub ℓ (π σ) = π σ')

/-! ## Trace Correspondence implies Oracle Soundness

The forward direction of the biconditional gives soundness:
every concrete step is captured by the induced oracle.
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

The backward direction gives completeness, but we need to realize the
target configuration x' as π σ' for some concrete σ'. This requires
π to be surjective. In the ICTAC setting (π = id), this is automatic.
-/

/-- Trace correspondence + surjective projection gives oracle completeness:
    if `R ℓ (π σ) x'`, there exists `σ'` with `H_I.step σ ℓ σ' ∧ π σ' = x'`. -/
theorem OracleCompleteFor_of_TraceCorrespondence {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I π Sub PC)
    (h_surj : Function.Surjective π) :
    OracleCompleteFor H_I π (oracleOfTraceDecomp Sub PC) := by
  intro σ x' ℓ ⟨hpc, hsub⟩
  obtain ⟨σ', hπ⟩ := h_surj x'
  exact ⟨σ', (h_tc σ σ' ℓ).mpr ⟨hpc, by rw [hsub, hπ]⟩, hπ⟩

/-- When π = id (the ICTAC setting), trace correspondence gives oracle
    completeness without surjectivity: take `σ' = x'` directly. -/
theorem OracleCompleteFor_of_TraceCorrespondence_id {Config : Type*} {L : Type*}
    (H_I : LTS Config L)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I id Sub PC) :
    OracleCompleteFor H_I id (oracleOfTraceDecomp Sub PC) := by
  intro σ x' ℓ ⟨hpc, hsub⟩
  exact ⟨x', (h_tc σ x' ℓ).mpr ⟨hpc, hsub⟩, rfl⟩
