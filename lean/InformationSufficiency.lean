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
