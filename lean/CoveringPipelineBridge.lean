import ExtractionPossibility

/-
# Covering Pipeline Bridge

Minimal formal bridge from an iterator-style covering workflow to the
`h_symex_sound` hypothesis required by `extraction_pipeline`.

This does not mechanize a concrete covering-set algorithm. Instead, it
abstracts over:

- an on-demand iterator (`next?`)
- a target-rule map for templates
- adequacy ("every grammar rule eventually has a template")
- a per-template symbolic-execution soundness assumption

This is the intended "composition chain" formalized as a theorem schema.
-/

open Classical

/-! ## Iterator-style covering interface -/

/-- One iterator transition emits a template `p` and moves to `it'`. -/
abbrev IteratorStep {Iter Prog : Type*}
    (next? : Iter → Option (Prog × Iter)) (it it' : Iter) : Prop :=
  ∃ p, next? it = some (p, it')

/-- Template `p` is eventually emitted by repeatedly calling `next?`
    from initial iterator state `it0`. -/
abbrev Emits {Iter Prog : Type*}
    (next? : Iter → Option (Prog × Iter)) (it0 : Iter) (p : Prog) : Prop :=
  ∃ it it',
    Relation.ReflTransGen (IteratorStep next?) it0 it ∧
    next? it = some (p, it')

/-- Coverage adequacy for an iterator-style template generator:
    every rule in `Γ` eventually has an emitted template targeting it. -/
def CoveringAdequate
    {Iter Prog T : Type*}
    (Γ : ContextFreeGrammar T)
    (next? : Iter → Option (Prog × Iter))
    (it0 : Iter)
    (targetRule : Prog → ContextFreeRule T Γ.NT) : Prop :=
  ∀ r, r ∈ Γ.rules →
    ∃ p, Emits next? it0 p ∧ targetRule p = r

/-! ## Bridge theorems -/

/-- Coverage adequacy plus grammar conformance gives a template witness
    for each reachable concrete step's source rule. -/
theorem template_of_reachable_step
    {HostState T Iter Prog : Type*}
    (gc : GrammarConformant HostState T)
    (next? : Iter → Option (Prog × Iter))
    (it0 : Iter)
    (targetRule : Prog → ContextFreeRule T gc.Γ.NT)
    (h_cov : CoveringAdequate gc.Γ next? it0 targetRule)
    {σ σ' : HostState} {ℓ : HTHLabel T gc.Γ.NT}
    (h_reach : gc.H_I.Reachable σ)
    (h_step : gc.H_I.step σ ℓ σ') :
    ∃ p, Emits next? it0 p ∧ targetRule p = ℓ.srcRule := by
  obtain ⟨hsrc, _hdst⟩ := gc.labels_from_grammar σ σ' ℓ h_step h_reach
  simpa using h_cov ℓ.srcRule hsrc

/-- Minimal composition chain:
    if emitted templates are adequate and per-template symbolic summaries
    are sound/parametric for their targeted rule, then we get the reachable
    `h_symex_sound` hypothesis required by `extraction_pipeline`. -/
theorem h_symex_sound_of_covering_pipeline
    {HostState T Iter Prog : Type*}
    (gc : GrammarConformant HostState T)
    (next? : Iter → Option (Prog × Iter))
    (it0 : Iter)
    (targetRule : Prog → ContextFreeRule T gc.Γ.NT)
    (symex : HTHLabel T gc.Γ.NT → HostState → HostState → Prop)
    (h_cov : CoveringAdequate gc.Γ next? it0 targetRule)
    (h_template_sound :
      ∀ (p : Prog) (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
        Emits next? it0 p →
        targetRule p = ℓ.srcRule →
        gc.H_I.Reachable σ →
        gc.H_I.step σ ℓ σ' →
        symex ℓ σ σ') :
    ∀ (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
      gc.H_I.Reachable σ →
      gc.H_I.step σ ℓ σ' →
      symex ℓ σ σ' := by
  intro σ σ' ℓ h_reach h_step
  obtain ⟨p, hp_emit, hp_target⟩ :=
    template_of_reachable_step gc next? it0 targetRule h_cov h_reach h_step
  exact h_template_sound p σ σ' ℓ hp_emit hp_target h_reach h_step

/-- End-to-end bridge theorem: instantiate `extraction_pipeline`
    from an iterator-style covering workflow and per-template symbolic
    soundness assumptions. -/
theorem extraction_pipeline_from_covering_pipeline
    {HostState T Dim Value Iter Prog : Type*}
    [DecidableEq Dim] [Fintype Dim] [Inhabited Value]
    (gc : GrammarConformant HostState T)
    (observe : HostState → Dim → Value)
    (h_faithful : ∀ (σ₁ σ₂ : HostState),
      gc.H_I.Reachable σ₁ →
      (∀ d, observe σ₁ d = observe σ₂ d) → σ₁ = σ₂)
    (next? : Iter → Option (Prog × Iter))
    (it0 : Iter)
    (targetRule : Prog → ContextFreeRule T gc.Γ.NT)
    (symex : HTHLabel T gc.Γ.NT → HostState → HostState → Prop)
    (h_cov : CoveringAdequate gc.Γ next? it0 targetRule)
    (h_template_sound :
      ∀ (p : Prog) (σ σ' : HostState) (ℓ : HTHLabel T gc.Γ.NT),
        Emits next? it0 p →
        targetRule p = ℓ.srcRule →
        gc.H_I.Reachable σ →
        gc.H_I.step σ ℓ σ' →
        symex ℓ σ σ') :
    ∃ (π : Projection HostState (Dim → Value))
        (R : HTHLabel T gc.Γ.NT → (Dim → Value) → (Dim → Value) → Prop),
      (LTS.ofOracle (π gc.H_I.init) R).Simulates gc.H_I
        (fun x σ => π σ = x ∧ gc.H_I.Reachable σ) := by
  apply extraction_pipeline gc observe h_faithful symex
  exact h_symex_sound_of_covering_pipeline gc next? it0 targetRule symex h_cov h_template_sound
