/-
# Information Sufficiency

Proves that at each pipeline stage, sufficient information exists
to correctly invoke the next stage.
-/

import ConditionalSimulation

/-! ## Covering Set Generation

The extraction pipeline begins by generating a **covering set** of test
templates — one per grammar rule. Each template exercises a specific
production rule by assigning sentinel values to every RHS position.
Running these templates through the implementation produces HTH-labeled
traces, one per rule, which downstream stages analyze.
-/

variable {T : Type*}

/-- A template for a grammar rule: the rule being exercised, plus
    sentinel assignments for each position in the RHS. -/
structure Template (T N : Type*) where
  /-- The grammar rule being exercised. -/
  rule : ContextFreeRule T N
  /-- Sentinel value for each position in the rule's RHS. -/
  sentinels : Fin rule.output.length → T

/-- Generate a covering set: one template per grammar rule, using
    the provided sentinel-choosing function. The algorithm maps each
    rule to a template pairing it with chosen sentinels. -/
def coveringSet {N : Type*} (rules : List (ContextFreeRule T N))
    (chooseSentinels : (r : ContextFreeRule T N) → Fin r.output.length → T) :
    List (Template T N) :=
  rules.map fun r => ⟨r, chooseSentinels r⟩

/-! ## Covering Set Adequacy

A covering set is adequate when every rule in the target collection has
a template exercising it. The `coveringSet` algorithm is adequate by
construction: it generates one template per input rule.
-/

/-- A covering set is adequate for a collection of rules when every
    rule in the collection has a template exercising it. -/
abbrev AdequateCoveringSet {T N : Type*}
    (rules : List (ContextFreeRule T N))
    (templates : List (Template T N)) : Prop :=
  ∀ r ∈ rules, ∃ t ∈ templates, t.rule = r

/-- `coveringSet` produces an adequate covering set: every input rule
    has a corresponding template in the output. -/
theorem coveringSet_adequate {N : Type*}
    (rules : List (ContextFreeRule T N))
    (chooseSentinels : (r : ContextFreeRule T N) → Fin r.output.length → T) :
    AdequateCoveringSet rules (coveringSet rules chooseSentinels) :=
  fun r hr => ⟨⟨r, chooseSentinels r⟩, List.mem_map_of_mem _ hr, rfl⟩

/-- Sentinels are distinct: different positions get different values.
    Required for differential causality testing (J1), not for adequacy. -/
abbrev DistinctSentinels {T N : Type*} (t : Template T N) : Prop :=
  Function.Injective t.sentinels

/-! ## Reachability Oracle

The extraction pipeline uses a **reachability oracle** to determine host-level
dataflow: whether state at one point causally influences a specific dimension
at another point. This is the third oracle alongside branching (symex) and
value transformation (symex) — instantiated by K framework specifications
via reachability logic.

The reachability oracle is dimension-aware: K framework reachability logic
operates on configuration patterns that constrain specific cells/components,
providing per-dimension causal information. This drives differential causality
testing (J1): by knowing which dimensions are causally connected, we determine
which dimensions belong in the projection π.
-/

/-- A reachability oracle provides dimension-aware host-level dataflow
    information: whether state at one point causally influences a specific
    dimension at another point. Instantiated by K framework specs via
    reachability logic, which operates on configuration patterns
    constraining specific cells. -/
abbrev ReachabilityOracle (HostState Dim : Type*) :=
  HostState → HostState → Dim → Prop

/-- A reachability oracle is sound when claimed causal influence implies
    an actual execution path: if the oracle says σ causally influences
    dimension d at σ', then there is an execution path from σ to σ'
    in H_I. -/
abbrev ReachabilityOracleSoundFor {HostState Dim : Type*} {L : Type*}
    (H_I : LTS HostState L) (reach : ReachabilityOracle HostState Dim) : Prop :=
  ∀ σ σ' d, reach σ σ' d → Relation.ReflTransGen H_I.canStep σ σ'

/-! ## Template Execution

A template execution witnesses running a covering-set template through
the implementation LTS. It bundles the template with the resulting trace
(start state, end state, label sequence, and the `IsTrace` witness).

The relationship between the template's rule and the trace labels is
semantic — the trace exercises the rule by construction of the covering
set — but formalizing that precisely requires the full template-trace
connection. For now, the structure is the raw bundle; constraints
relating labels to the template appear as hypotheses in downstream
theorems (differential causality).
-/

/-- A template execution: running a template through H_I produces a
    trace. Bundles the template, start/end host states, label sequence,
    and the trace witness through the LTS. -/
structure TemplateExecution {HostState T N : Type*}
    (H_I : LTS HostState (HTHLabel T N)) where
  /-- The template being executed. -/
  template : Template T N
  /-- The starting host state. -/
  σ_start : HostState
  /-- The ending host state. -/
  σ_end : HostState
  /-- The sequence of HTH labels along the trace. -/
  labels : List (HTHLabel T N)
  /-- The trace witness: valid execution through H_I. -/
  trace : H_I.IsTrace σ_start labels σ_end

/-! ## Differential Causality Testing

Differential causality testing compares two template executions that follow
the same control flow (same label sequence) but use different sentinel values.
If a specific dimension of the host state differs between the two end states,
that dimension was causally influenced by the changed sentinel — revealing
a dimension that belongs in the projection π.

Key insight: if changing a sentinel causes a BRANCH difference (different
labels), that's branch discovery, not causality testing. Differential
causality only applies when both traces follow identical control flow.
-/

/-- Two template executions differ at a specific host-state dimension.
    This is the per-dimension observable outcome of differential testing:
    changing a sentinel value and observing which dimensions of the
    final state change. Requires an observation function mapping host
    states to per-dimension values. -/
abbrev DimensionDiffers {HostState T N Dim Value : Type*}
    {H_I : LTS HostState (HTHLabel T N)}
    (observe : HostState → Dim → Value)
    (exec₁ exec₂ : TemplateExecution H_I)
    (d : Dim) : Prop :=
  observe exec₁.σ_end d ≠ observe exec₂.σ_end d

/-- Differential causality testing correctly identifies causal influence:
    if two template executions for the same rule follow the same control
    flow (same labels) but differ only at sentinel position `h`, then
    a dimension differs between the end states iff the reachability oracle
    witnesses causal influence from `σ_h` to that dimension.

    The state `σ_h` represents where hole `h`'s sentinel value enters
    execution. Both traces must follow identical label sequences — if
    changing a sentinel causes a branch difference, that's branch discovery,
    not causality testing.

    Both directions:
    - (→) If changing the sentinel changes dimension `d`, the reachability
      oracle witnesses the causal chain from `σ_h` to `d` at the end state.
    - (←) If the oracle claims `σ_h` causally influences `d`, label
      determinism guarantees the sentinel change propagates to `d`. -/
theorem differential_causality_identifies_projection
    {HostState T N Dim Value : Type*}
    {H_I : LTS HostState (HTHLabel T N)}
    (observe : HostState → Dim → Value)
    (h_label_det : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T N),
      H_I.step σ ℓ σ₁ → H_I.step σ ℓ σ₂ → σ₁ = σ₂)
    (reach : ReachabilityOracle HostState Dim)
    (h_sound : ReachabilityOracleSoundFor H_I reach)
    (r : ContextFreeRule T N) (s₁ s₂ : Fin r.output.length → T)
    (exec₁ : TemplateExecution H_I) (h_t₁ : exec₁.template = ⟨r, s₁⟩)
    (exec₂ : TemplateExecution H_I) (h_t₂ : exec₂.template = ⟨r, s₂⟩)
    (h_same_labels : exec₁.labels = exec₂.labels)
    (h : Fin r.output.length)
    (h_differ : s₁ h ≠ s₂ h)
    (h_agree : ∀ i, i ≠ h → s₁ i = s₂ i)
    (σ_h : HostState)
    (h_on_path : Relation.ReflTransGen H_I.canStep exec₁.σ_start σ_h)
    (d : Dim)
    : DimensionDiffers observe exec₁ exec₂ d ↔ reach σ_h exec₁.σ_end d :=
  sorry -- SCAFFOLD: requires template-trace connection formalization