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
dataflow: whether state at one point can causally influence state at another.
This is the third oracle alongside branching (symex) and value transformation
(symex) — instantiated by K framework specifications via reachability logic.

The reachability oracle drives differential causality testing (J1): by knowing
which state positions are causally connected, we can determine which dimensions
belong in the projection π.
-/

/-- A reachability oracle provides host-level dataflow information:
    whether one host state can causally influence another through
    execution. Instantiated by K framework specs via reachability logic. -/
abbrev ReachabilityOracle (HostState : Type*) :=
  HostState → HostState → Prop

/-- A reachability oracle is sound when it only claims pairs connected
    by the reflexive-transitive closure of the LTS step relation.
    That is, if the oracle says σ can reach σ', then there is an
    actual execution path from σ to σ' in H_I. -/
abbrev ReachabilityOracleSoundFor {HostState : Type*} {L : Type*}
    (H_I : LTS HostState L) (reach : ReachabilityOracle HostState) : Prop :=
  ∀ σ σ', reach σ σ' → Relation.ReflTransGen H_I.canStep σ σ'

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

Differential causality testing compares two template executions that start
from the same state but use different sentinel values. If the end states
differ, some dimension of the host state was causally influenced by the
changed sentinel — revealing a dimension that belongs in the projection π.
-/

/-- Two template executions exhibit a trace difference: they start from
    the same host state but reach different end states. This is the
    observable outcome of differential testing — changing a sentinel
    value and observing whether the final state changes. -/
abbrev TraceDiffers {HostState T N : Type*}
    {H_I : LTS HostState (HTHLabel T N)}
    (exec₁ exec₂ : TemplateExecution H_I) : Prop :=
  exec₁.σ_start = exec₂.σ_start ∧ exec₁.σ_end ≠ exec₂.σ_end

/-- Differential causality testing correctly identifies causal influence:
    if two template executions for the same rule start from the same state
    and differ only at sentinel position `h`, then trace differences
    (different end states) are equivalent to causal reachability from `h`'s
    evaluation point `σ_h` to the end state.

    The state `σ_h` represents where hole `h`'s sentinel value enters
    execution. Connecting `σ_h` to the template and trace structure
    requires the template-trace connection (deferred).

    Both directions:
    - (→) If changing the sentinel changes the outcome, the reachability
      oracle witnesses the causal chain from `σ_h` to the end state.
    - (←) If `σ_h` causally reaches the end state, `h_label_det`
      (determinism within HTH regions) guarantees the sentinel change
      propagates. -/
theorem differential_causality_identifies_projection
    {HostState T N : Type*}
    {H_I : LTS HostState (HTHLabel T N)}
    (h_label_det : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T N),
      H_I.step σ ℓ σ₁ → H_I.step σ ℓ σ₂ → σ₁ = σ₂)
    (reach : ReachabilityOracle HostState)
    (h_sound : ReachabilityOracleSoundFor H_I reach)
    (r : ContextFreeRule T N) (s₁ s₂ : Fin r.output.length → T)
    (exec₁ : TemplateExecution H_I) (h_t₁ : exec₁.template = ⟨r, s₁⟩)
    (exec₂ : TemplateExecution H_I) (h_t₂ : exec₂.template = ⟨r, s₂⟩)
    (h_same_start : exec₁.σ_start = exec₂.σ_start)
    (h : Fin r.output.length)
    (h_differ : s₁ h ≠ s₂ h)
    (h_agree : ∀ i, i ≠ h → s₁ i = s₂ i)
    (σ_h : HostState)
    (h_on_path : Relation.ReflTransGen H_I.canStep exec₁.σ_start σ_h)
    : TraceDiffers exec₁ exec₂ ↔ reach σ_h exec₁.σ_end :=
  sorry -- SCAFFOLD: requires template-trace connection formalization