/-
# Extraction Possibility

End-to-end existence theorem: given a grammar-conformant implementation
with label determinism, an adequate covering set, and a sound reachability
oracle, there exist a projection π and oracle R forming a co-refinement
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
- **Sound reachability oracle**: host-level dataflow claims are backed by
  actual execution paths.

Together these guarantee the existence of a projection π and oracle R
satisfying `IsCoRefinementFixpoint` — the oracle captures every concrete
transition, and non-controllable transitions preserve π.
-/

/-- End-to-end extraction possibility: given a grammar-conformant
    implementation with label determinism, an adequate covering set,
    and a sound reachability oracle, there exist a projection and
    oracle forming a co-refinement fixpoint — and hence yielding
    a simulation of H_I. -/
theorem extraction_possible
    {HostState T : Type*}
    (gc : GrammarConformant HostState T)
    (h_label_det : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.step σ ℓ σ₁ → gc.H_I.step σ ℓ σ₂ → σ₁ = σ₂)
    (templates : List (Template T gc.Γ.NT))
    (h_adequate : AdequateCoveringSet gc.Γ.rules templates)
    (reach : ReachabilityOracle HostState)
    (h_reach_sound : ReachabilityOracleSoundFor gc.H_I reach)
    : ∃ (Config : Type*) (π : Projection HostState Config)
        (R : HTHLabel T gc.Γ.NT → Config → Config → Prop),
      IsCoRefinementFixpoint gc.H_I π R :=
  sorry -- SCAFFOLD: requires pipeline construction from J1 + co-refinement
