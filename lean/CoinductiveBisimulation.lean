/-
# Coinductive Bisimulation via Learnability

The projection relation induced by the learnability framework is a bisimulation.

Key insight: the same oracle soundness/completeness properties that power the
inductive fixpoint proof also directly witness the one-step matching property
needed for bisimulation. The "coinductive" proof obligation reduces to:
projection commutes with transitions.

Forward direction: oracle soundness gives grammar matches for implementation steps.
Backward direction: extractionDims_deproject gives implementation matches for grammar steps.
Relevance threading: relevant_closed ensures the projection relation is closed under steps.

The witness for any bisimulation step is always constructive: take one more
implementation step, project the result. That's the witness. All the work was
already done by the learnability framework.
-/

import Learnability

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Classical

section CoinductiveBisimulation

variable {State Label Dim Value : Type*}
  [DecidableEq Dim] [Fintype Dim] [Inhabited Value]

/-! ## Grammar LTS

The extracted model is an LTS whose states are projected observations (Dim → Value)
and whose transitions are given by the relevance-restricted projected oracle at
the extraction fixpoint. The relevance restriction is essential: the backward
direction uses injectivity, which only holds on relevant states.
-/

/-- A bisimulation between implementation states and projected grammar states.
    Scoped to relevant implementation states — bisimulation characterizes the
    behavior of reachable states, not the full state space. -/
def IsBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (R : State → (Dim → Value) → Prop) : Prop :=
  ∀ s g, R s g → lp.relevant s →
    -- Forward: every implementation step has a matching grammar step
    (∀ ℓ s', lp.behavior s ℓ s' →
      relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g (project lp.observe lp.extractionDims s') ∧
      R s' (project lp.observe lp.extractionDims s')) ∧
    -- Backward: every grammar step has a matching implementation step
    (∀ ℓ g', relevantProjectedOracle lp.relevant lp.oracle lp.observe
        lp.extractionDims ℓ g g' →
      ∃ s', lp.behavior s ℓ s' ∧ R s' g')

/-- The projection relation: implementation state s is related to grammar state g
    when s is relevant and projects to g under the extraction fixpoint. -/
def projectionRelation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    State → (Dim → Value) → Prop :=
  fun s g => lp.relevant s ∧ project lp.observe lp.extractionDims s = g

/-- The projection relation is a bisimulation.

    This is the main theorem: the inductive fixpoint construction already gives
    us everything we need for bisimulation. The coinductive proof obligation
    (show the relation is preserved by one step) is discharged by:
    - Forward: relevantProjectedOracle_sound
    - Backward: extractionDims_deproject
    - Threading: relevant_closed

    No additional work beyond what the learnability framework already provides. -/
theorem projectionRelation_isBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    IsBisimulation lp (projectionRelation lp) := by
  intro s g ⟨hr, hg⟩ _
  subst hg
  constructor
  · -- Forward direction: implementation step → grammar step
    intro ℓ s' hbeh
    exact ⟨lp.relevantProjectedOracle_sound lp.extractionDims s s' ℓ hr hbeh,
           lp.relevant_closed s s' ℓ hr hbeh,
           rfl⟩
  · -- Backward direction: grammar step → implementation step
    intro ℓ g' hclaim
    obtain ⟨s', hbeh, hproj⟩ := lp.extractionDims_deproject hr hclaim
    exact ⟨s', hbeh, lp.relevant_closed s s' ℓ hr hbeh, hproj⟩

/-! ## Bisimilarity as Greatest Fixpoint

In the absence of native coinductive propositions (Lean 4 uses inductive types),
bisimilarity is defined relationally as the union of all bisimulations.
This is the standard Milner construction and is equivalent to the coinductive
greatest fixpoint in classical logic.
-/

/-- Two states are bisimilar if they are related by some bisimulation. -/
def Bisimilar
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (g : Dim → Value) : Prop :=
  ∃ R, IsBisimulation lp R ∧ R s g

/-- Bisimilarity itself is a bisimulation (it's the union of all bisimulations). -/
theorem bisimilar_isBisimulation
    (lp : LearnabilityPreconditionsComplete State Label Dim Value) :
    IsBisimulation lp (Bisimilar lp) := by
  intro s g ⟨R, hR_bisim, hRsg⟩ hr
  obtain ⟨hfwd, hbwd⟩ := hR_bisim s g hRsg hr
  constructor
  · intro ℓ s' hbeh
    obtain ⟨hgram, hRs'⟩ := hfwd ℓ s' hbeh
    exact ⟨hgram, R, hR_bisim, hRs'⟩
  · intro ℓ g' hclaim
    obtain ⟨s', hbeh, hRs'g'⟩ := hbwd ℓ g' hclaim
    exact ⟨s', hbeh, R, hR_bisim, hRs'g'⟩

/-- The projection relation is contained in bisimilarity:
    every relevant state is bisimilar to its projection. -/
theorem projection_bisimilar
    (lp : LearnabilityPreconditionsComplete State Label Dim Value)
    (s : State) (hr : lp.relevant s) :
    Bisimilar lp s (project lp.observe lp.extractionDims s) :=
  ⟨projectionRelation lp, projectionRelation_isBisimulation lp, hr, rfl⟩

end CoinductiveBisimulation
