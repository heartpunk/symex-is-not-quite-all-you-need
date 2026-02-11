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
