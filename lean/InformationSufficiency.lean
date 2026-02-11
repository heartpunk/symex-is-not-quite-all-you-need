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

/-! ## Structured Language

A **structured language** is a grammar-conformant implementation whose HTH-level
transitions satisfy three structural axioms. These characterize the class of
languages to which the extraction technique applies — languages where control
flow is determined by grammar structure.

1. **Label-deterministic**: Same state + same HTH label → same target.
   An HTH region is straight-line code; given the same starting state and
   region, execution arrives at the same place.

2. **Branching at same hole**: All outgoing transitions from a state share
   `(srcRule, fromPos)`. At any point in execution, you're at a definite
   grammar position. Branching (if it occurs) is over which continuation
   follows — different `(dstRule, toPos)`, same source position.

3. **Adjacent-compatible**: Consecutive transitions have compatible labels —
   the destination of one step equals the source of the next. Execution
   follows grammar structure without teleporting to unrelated positions.
-/

/-- A structured language: a grammar-conformant implementation satisfying
    three structural axioms on HTH-level transitions. These characterize
    languages where control flow is grammar-determined. -/
structure StructuredLanguage (HostState T : Type*) extends GrammarConformant HostState T where
  /-- An HTH region is straight-line: same state + same label → same target. -/
  label_deterministic : ∀ (σ σ₁ σ₂ : HostState) (ℓ : HTHLabel T Γ.NT),
    H_I.step σ ℓ σ₁ → H_I.step σ ℓ σ₂ → σ₁ = σ₂
  /-- All outgoing transitions share source position: at any state,
      execution is at a definite grammar position. -/
  branching_at_same_hole : ∀ (σ σ₁ σ₂ : HostState) (ℓ₁ ℓ₂ : HTHLabel T Γ.NT),
    H_I.step σ ℓ₁ σ₁ → H_I.step σ ℓ₂ σ₂ →
    ℓ₁.srcRule = ℓ₂.srcRule ∧ ℓ₁.fromPos = ℓ₂.fromPos
  /-- Consecutive transitions are compatible: destination of one step
      matches source of the next. -/
  adjacent_compatible : ∀ (σ₁ σ₂ σ₃ : HostState) (ℓ₁ ℓ₂ : HTHLabel T Γ.NT),
    H_I.step σ₁ ℓ₁ σ₂ → H_I.step σ₂ ℓ₂ σ₃ →
    ℓ₁.dstRule = ℓ₂.srcRule ∧ ℓ₁.toPos = ℓ₂.fromPos
