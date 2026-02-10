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

end LTS
