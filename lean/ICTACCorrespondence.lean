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
