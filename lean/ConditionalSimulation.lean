/-
# Conditional Simulation Theorem

Formalization of "Symbolic Execution is (Not Quite) All You Need"
-/

import Mathlib.Logic.Relation
import Mathlib.Computability.ContextFreeGrammar

/-! ## Labeled Transition Systems

An LTS over states `S` and labels `L`: an initial state and a transition
relation. Well-formedness (types match, step is of the right sort) is
enforced by Lean's type system—the analog of `→ ⊆ S × L × S` and `s₀ ∈ S`
in the set-theoretic definition.
-/

/-- A labeled transition system (relational encoding). -/
structure LTS (S : Type*) (L : Type*) where
  init : S
  step : S → L → S → Prop

namespace LTS

variable {S L : Type*}

/-- The step relation `S → L → S → Prop` is definitionally `S → L → Set S`
    (the powerset monad / Kleisli arrow). No conversion needed—just
    a change of perspective. -/
example (lts : LTS S L) : S → L → Set S := lts.step

/-- Build an LTS from a deterministic partial-function encoding.
    Embeds `Option S` into the relational form. -/
def ofOption (init : S) (f : S → L → Option S) : LTS S L where
  init := init
  step := fun s l s' => f s l = some s'

/-! ### Reachability

We erase labels to get a binary relation on states, then use Mathlib's
`Relation.ReflTransGen` for the reflexive-transitive closure. This gives
us transitivity, single-step lifting, and induction principles for free.
-/

/-- The label-erased step relation: `s` can step to `s'` via some label. -/
def canStep (lts : LTS S L) (s s' : S) : Prop :=
  ∃ l, lts.step s l s'

/-- A state is reachable if it is in the reflexive-transitive closure
    of `canStep` from `init`. Corresponds to `Reach(H_I)` in the paper. -/
def Reachable (lts : LTS S L) (s : S) : Prop :=
  Relation.ReflTransGen lts.canStep lts.init s

theorem Reachable.init (lts : LTS S L) : lts.Reachable lts.init :=
  Relation.ReflTransGen.refl

theorem Reachable.step {lts : LTS S L} {s s' : S} {l : L}
    (hr : lts.Reachable s) (hs : lts.step s l s') : lts.Reachable s' :=
  hr.tail ⟨l, hs⟩

theorem Reachable.extend {lts : LTS S L} {s₁ s₂ : S}
    (h₁ : lts.Reachable s₁) (h₂ : Relation.ReflTransGen lts.canStep s₁ s₂) :
    lts.Reachable s₂ :=
  h₁.trans h₂

/-! ### Traces

A trace is a list of labels witnessing a path between two states.
This is the labeled counterpart to reachability — where `Reachable`
forgets labels, `IsTrace` retains them. Corresponds to the paper's τ ∈ T.
-/

/-- A valid trace: a list of labels witnessing a step-by-step path. -/
inductive IsTrace (lts : LTS S L) : S → List L → S → Prop where
  | nil (s : S) : IsTrace lts s [] s
  | cons (l : L) {s₁ s₂ s₃ : S} (ls : List L) :
      lts.step s₁ l s₂ → IsTrace lts s₂ ls s₃ → IsTrace lts s₁ (l :: ls) s₃

theorem IsTrace.append {lts : LTS S L} {s₁ s₂ s₃ : S} {ls₁ ls₂ : List L}
    (h₁ : IsTrace lts s₁ ls₁ s₂) (h₂ : IsTrace lts s₂ ls₂ s₃) :
    IsTrace lts s₁ (ls₁ ++ ls₂) s₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons l ls hs _ ih => exact .cons l (ls ++ ls₂) hs (ih h₂)

/-- Any trace witnesses a `ReflTransGen` path (label-erased). -/
theorem IsTrace.toReflTransGen {lts : LTS S L} {s₁ s₂ : S} {ls : List L}
    (h : IsTrace lts s₁ ls s₂) : Relation.ReflTransGen lts.canStep s₁ s₂ := by
  induction h with
  | nil => exact .refl
  | cons l _ hs _ ih => exact .head ⟨l, hs⟩ ih

/-- A trace from `init` witnesses reachability of the endpoint. -/
theorem IsTrace.toReachable {lts : LTS S L} {ls : List L} {s : S}
    (h : IsTrace lts lts.init ls s) : lts.Reachable s :=
  h.toReflTransGen

/-! ### Simulation

`simulating` simulates `simulated` via relation `R` when initial states are
related and every step of `simulated` from a related pair can be matched by
`simulating` preserving `R`.

The paper's `G' ≼ H_I` is simulation between LTS with different state spaces
(X for G', Σ for H_I) mediated by the projection π. We define simulation
generically over any witness relation `R : S₁ → S₂ → Prop`.

Simulation forms a preorder: it is reflexive (via `Eq`) and transitive
(via relational composition).
-/

/-- `simulating` simulates `simulated` via witness relation `R`:
    initial states are related, and every step of `simulated` from a
    related pair can be matched by `simulating` preserving `R`. -/
structure Simulates {S₁ S₂ : Type*}
    (simulating : LTS S₁ L) (simulated : LTS S₂ L)
    (R : S₁ → S₂ → Prop) : Prop where
  init : R simulating.init simulated.init
  step_match : ∀ (s₁ : S₁) (s₂ : S₂) (l : L) (s₂' : S₂),
      R s₁ s₂ → simulated.step s₂ l s₂' →
      ∃ s₁' : S₁, simulating.step s₁ l s₁' ∧ R s₁' s₂'

/-- Simulation is reflexive: any LTS simulates itself via `Eq`. -/
theorem Simulates.refl (lts : LTS S L) : lts.Simulates lts Eq where
  init := rfl
  step_match := by
    intro s₁ s₂ l s₂' heq hstep
    subst heq
    exact ⟨s₂', hstep, rfl⟩

/-- Simulation is transitive: compose witness relations. -/
theorem Simulates.trans {S₁ S₂ S₃ : Type*}
    {lts₁ : LTS S₁ L} {lts₂ : LTS S₂ L} {lts₃ : LTS S₃ L}
    {R₁₂ : S₁ → S₂ → Prop} {R₂₃ : S₂ → S₃ → Prop}
    (h₁₂ : lts₁.Simulates lts₂ R₁₂) (h₂₃ : lts₂.Simulates lts₃ R₂₃) :
    lts₁.Simulates lts₃ (fun s₁ s₃ => ∃ s₂, R₁₂ s₁ s₂ ∧ R₂₃ s₂ s₃) where
  init := ⟨lts₂.init, h₁₂.init, h₂₃.init⟩
  step_match := by
    intro s₁ s₃ l s₃' ⟨s₂, hr₁₂, hr₂₃⟩ hstep₃
    obtain ⟨s₂', hstep₂, hr₂₃'⟩ := h₂₃.step_match s₂ s₃ l s₃' hr₂₃ hstep₃
    obtain ⟨s₁', hstep₁, hr₁₂'⟩ := h₁₂.step_match s₁ s₂ l s₂' hr₁₂ hstep₂
    exact ⟨s₁', hstep₁, s₂', hr₁₂', hr₂₃'⟩

/-- Existential simulation: some witness relation exists.
    Corresponds to `G' ≼ H_I` in the paper. -/
def Sim {S₁ S₂ : Type*} (simulating : LTS S₁ L) (simulated : LTS S₂ L) : Prop :=
  ∃ R : S₁ → S₂ → Prop, simulating.Simulates simulated R

theorem Sim.refl (lts : LTS S L) : lts.Sim lts :=
  ⟨Eq, Simulates.refl lts⟩

theorem Sim.trans {S₁ S₂ S₃ : Type*}
    {lts₁ : LTS S₁ L} {lts₂ : LTS S₂ L} {lts₃ : LTS S₃ L}
    (h₁₂ : lts₁.Sim lts₂) (h₂₃ : lts₂.Sim lts₃) : lts₁.Sim lts₃ := by
  obtain ⟨R₁₂, hsim₁₂⟩ := h₁₂
  obtain ⟨R₂₃, hsim₂₃⟩ := h₂₃
  exact ⟨_, hsim₁₂.trans hsim₂₃⟩

end LTS

/-! ## Grammar, Holes, and HTH Labels

We use Mathlib's `ContextFreeGrammar` for Γ. Holes in a production γ are
the nonterminal positions in γ's RHS. HTH (Hole-to-Hole) labels identify
straight-line execution regions between consecutive holes.
-/

variable {T N : Type*}

/-- The hole positions in a production rule: indices where nonterminal
    symbols appear in the RHS. Corresponds to `holes(γ)` in the paper. -/
def ContextFreeRule.holePositions (r : ContextFreeRule T N) :
    List (Fin r.output.length) :=
  (List.finRange r.output.length).filter fun i =>
    match r.output.get i with
    | .nonterminal _ => true
    | .terminal _ => false

/-- An HTH (Hole-to-Hole) label: identifies the straight-line execution
    region between two hole positions in a production.
    Corresponds to `ℓ = (γ, h_i, h_j)` in the paper. -/
structure HTHLabel (T N : Type*) where
  rule : ContextFreeRule T N
  fromPos : Nat
  toPos : Nat

/-! ## Projection

The projection π : Σ → X maps the full host state to the program-relevant
configuration. X is the transitive closure of AST-bound state—everything
causally influenced by program structure. For lexically scoped languages,
the scope structure coincides with grammar nesting, so π's domain is
determined by Γ and differential causality testing.
-/

/-- The projection from host state to program-relevant configuration. -/
abbrev Projection (HostState Config : Type*) := HostState → Config

/-! ## Oracles: Value Transformation and Branching

The paper's extraction relies on two oracles:

1. **Value-transformation oracle** (R): for each HTH label ℓ, a relation
   R_ℓ(x, x') capturing the state transformation of the region.
   Soundness: every concrete step is captured. Completeness: R claims
   no transitions beyond what H_I exhibits.

2. **Branching oracle** (B): for each configuration x, the set of
   feasible HTH labels B(x). Soundness: claimed labels are feasible.
   Completeness: all feasible labels are claimed.

**Dependency chain**: The simulation theorems below only require R to be
sound/complete—they don't mention B. However, *constructing* a sound R
requires complete branching discovery: if the branching oracle misses a
label ℓ, then R_ℓ will be wrong/absent, violating `OracleSoundFor`.
So branching oracle completeness is a prerequisite for value oracle
soundness, not a separate theorem hypothesis.

**B–R relationship**: The canonical B is the domain of R:
`B x ℓ := ∃ x', R ℓ x x'`. Under this definition,
`OracleSoundFor R` implies `BranchOracleCompleteFor B`, and
`OracleCompleteFor R` implies `BranchOracleSoundFor B`.
-/

/-- An oracle is sound for an LTS through a projection when every
    concrete step is captured by the corresponding relation on
    projected states. -/
abbrev OracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.step σ ℓ σ' → R ℓ (π σ) (π σ')

/-- An oracle is complete for an LTS through a projection when every
    claimed transition is realizable from any concrete state projecting
    to the source. This captures that π contains all state relevant to
    transition behavior: non-projected state cannot block a transition
    that R claims is possible. -/
abbrev OracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop) : Prop :=
  ∀ (σ : HostState) (x' : Config) (ℓ : L),
    R ℓ (π σ) x' → ∃ (σ' : HostState), H_I.step σ ℓ σ' ∧ π σ' = x'

/-- A branching oracle: for each configuration, which labels are feasible. -/
abbrev BranchingOracle (Config L : Type*) := Config → L → Prop

/-- A branching oracle is sound when every claimed label is feasible
    from any concrete state projecting to that configuration. -/
abbrev BranchOracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (B : BranchingOracle Config L) : Prop :=
  ∀ (σ : HostState) (ℓ : L),
    B (π σ) ℓ → ∃ (σ' : HostState), H_I.step σ ℓ σ'

/-- A branching oracle is complete when every feasible label is claimed. -/
abbrev BranchOracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (B : BranchingOracle Config L) : Prop :=
  ∀ (σ σ' : HostState) (ℓ : L),
    H_I.step σ ℓ σ' → B (π σ) ℓ

/-- The canonical branching oracle induced by a value oracle:
    label ℓ is feasible from x iff R claims some transition. -/
abbrev BranchingOracle.ofValueOracle {Config : Type*} {L : Type*}
    (R : L → Config → Config → Prop) : BranchingOracle Config L :=
  fun x ℓ => ∃ x', R ℓ x x'

/-- A sound value oracle induces a complete branching oracle. -/
theorem BranchOracleCompleteFor_of_OracleSoundFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_sound : OracleSoundFor H_I π R) :
    BranchOracleCompleteFor H_I π (BranchingOracle.ofValueOracle R) :=
  fun σ σ' ℓ hstep => ⟨π σ', h_sound σ σ' ℓ hstep⟩

/-- A complete value oracle induces a sound branching oracle. -/
theorem BranchOracleSoundFor_of_OracleCompleteFor {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_complete : OracleCompleteFor H_I π R) :
    BranchOracleSoundFor H_I π (BranchingOracle.ofValueOracle R) := by
  intro σ ℓ ⟨x', hR⟩
  obtain ⟨σ', hstep, _⟩ := h_complete σ x' ℓ hR
  exact ⟨σ', hstep⟩

/-! ## Oracle-Induced Simulation and Bisimulation

Given a sound oracle R, the oracle LTS simulates H_I (forward simulation).
Given a complete oracle R, H_I simulates the oracle LTS (reverse simulation).
Together, soundness + completeness give bisimulation. The non-trivial content
of the paper lies in *establishing* these oracle properties (extraction
pipeline, co-refinement fixpoint), not in these implications themselves.
-/

/-- The LTS over configurations induced by an oracle: transitions are
    exactly the oracle's relational summaries. -/
def LTS.ofOracle {Config : Type*} {L : Type*}
    (init : Config) (R : L → Config → Config → Prop) : LTS Config L where
  init := init
  step := fun x ℓ x' => R ℓ x x'

/-- A sound oracle induces a forward simulation: the oracle LTS
    simulates H_I via `fun x σ => π σ = x`. -/
theorem simulation_of_sound_oracle {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_sound : OracleSoundFor H_I π R) :
    (LTS.ofOracle (π H_I.init) R).Simulates H_I (fun x σ => π σ = x) where
  init := rfl
  step_match := by
    intro x σ ℓ σ' hrel hstep
    subst hrel
    exact ⟨π σ', h_sound σ σ' ℓ hstep, rfl⟩

/-- A complete oracle induces a reverse simulation: H_I simulates
    the oracle LTS via `fun σ x => π σ = x`. -/
theorem simulation_of_complete_oracle {HostState Config : Type*} {L : Type*}
    (H_I : LTS HostState L) (π : Projection HostState Config)
    (R : L → Config → Config → Prop)
    (h_complete : OracleCompleteFor H_I π R) :
    H_I.Simulates (LTS.ofOracle (π H_I.init) R) (fun σ x => π σ = x) where
  init := rfl
  step_match := by
    intro σ x ℓ x' hrel hstep
    subst hrel
    obtain ⟨σ', hstep', hproj⟩ := h_complete σ x' ℓ hstep
    exact ⟨σ', hstep', hproj⟩
