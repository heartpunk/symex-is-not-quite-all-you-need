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
