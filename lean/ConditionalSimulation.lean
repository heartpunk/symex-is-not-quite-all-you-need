/-
# Conditional Simulation Theorem

Formalization of "Symbolic Execution is (Not Quite) All You Need"
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

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

theorem init_reachable (lts : LTS S L) : lts.Reachable lts.init :=
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

end LTS
