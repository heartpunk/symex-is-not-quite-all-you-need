/-
# ICTAC Correspondence

Bridge between the ICTAC Rocq mechanization of symbolic execution
correctness and our extraction framework. The ICTAC proof establishes
a trace correspondence theorem (Theorem 1):

  denot_fun t V = Some V' ↔ (V |= PC t) ∧ denot_sub (Sub t) V = V'

This biconditional folds guard evaluation and value transformation into
a single statement. We show it implies:
1. Our split OracleSoundFor + OracleCompleteFor (simulation framework)
2. A host-state-level symex oracle suitable for `extraction_possible`
   (extraction framework)

The second connection is the key bridge: ICTAC/Lucanu-style symbolic
execution results instantiate the `symex` parameter in the extraction
pipeline, closing the loop from "symex is sound" to "simulation exists."

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

/-! ## Host-State-Level Symex Oracle

The extraction pipeline (`extraction_possible`) takes a host-state-level
symex oracle: `symex : L → HostState → HostState → Prop` with soundness
`∀ σ σ' ℓ, step σ ℓ σ' → symex ℓ σ σ'`.

Trace correspondence provides such an oracle via the Guard + Update
decomposition. This bridges ICTAC/Lucanu-style symbolic execution
results to the extraction framework.
-/

/-- The host-state-level symex oracle induced by trace correspondence:
    `symex ℓ σ σ'` holds iff the path condition holds at `π σ` and
    applying the substitution to `π σ` yields `π σ'`.

    When π = id (the ICTAC setting), this reduces to the direct
    Guard + Update decomposition on host states. For general π,
    it captures what symbolic execution reveals about state
    transformations at the abstraction level of π. -/
abbrev symexOfTraceDecomp {HostState Config : Type*} {L : Type*}
    (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop) :
    L → HostState → HostState → Prop :=
  fun ℓ σ σ' => PC ℓ (π σ) ∧ Sub ℓ (π σ) = π σ'

/-- Trace correspondence implies symex oracle soundness: every concrete
    step is captured by the Guard + Update decomposition. This is the
    bridge that lets ICTAC/Lucanu-style symbolic execution results
    instantiate the `symex` parameter in `extraction_possible`.

    The chain: Lucanu et al. (generic symex soundness) or ICTAC
    (trace_correspondence) → this theorem → extraction_possible →
    co-refinement fixpoint → simulation. -/
theorem symexOfTraceDecomp_sound {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (Sub : L → Config → Config) (PC : L → Config → Prop)
    (h_tc : TraceCorrespondence H_I π Sub PC) :
    ∀ (σ σ' : HostState) (ℓ : L),
      H_I.step σ ℓ σ' → symexOfTraceDecomp π Sub PC ℓ σ σ' :=
  fun σ σ' ℓ hstep => (h_tc σ σ' ℓ).mp hstep
