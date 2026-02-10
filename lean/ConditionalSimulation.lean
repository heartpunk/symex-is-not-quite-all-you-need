/-
# Conditional Simulation Theorem

Formalization of "Symbolic Execution is (Not Quite) All You Need"
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

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

end LTS
