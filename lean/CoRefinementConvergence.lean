/-
# Co-Refinement Convergence

The paper's extraction technique involves co-refinement across three
dimensions: configuration refinement (π), region refinement (HTH), and
semantic refinement (R_ℓ). These refine together until all three
stabilize.

The convergence argument (scratch.tex §Remarks): the oracle O operates
at the full Σ level, so it can always make progress regardless of the
current π. Since the tracked dimension set X grows monotonically and
the dimension space is finite, the process must terminate.

This module proves the abstract convergence lemma and applies it to
the co-refinement setting.
-/

import ConditionalSimulation

/-! ## Monotone Finset Stabilization

A monotone increasing sequence of finsets over a finite type must
eventually stabilize: the cardinality is non-decreasing and bounded
by the cardinality of the type.
-/

/-- A monotone increasing sequence of finsets over a finite type
    eventually stabilizes: there exists `n` with `s n = s (n + 1)`. -/
theorem Finset.monotone_stabilizes {α : Type*} [DecidableEq α] [Fintype α]
    (s : ℕ → Finset α) (h_mono : ∀ n, s n ⊆ s (n + 1)) :
    ∃ n, s n = s (n + 1) := by
  by_contra h_all_ne
  push_neg at h_all_ne
  -- Every step is a strict superset
  have h_ssubset : ∀ n, s n ⊂ s (n + 1) :=
    fun n => (h_mono n).ssubset_of_ne (h_all_ne n)
  -- So cardinality strictly increases at each step
  have h_card_lt : ∀ n, (s n).card < (s (n + 1)).card :=
    fun n => Finset.card_lt_card (h_ssubset n)
  -- Therefore card grows at least linearly: n ≤ (s n).card
  have h_lower : ∀ n, n ≤ (s n).card := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (h_card_lt n))
  -- But card is bounded by the type's cardinality
  have h_upper := Finset.card_le_univ (s (Fintype.card α + 1))
  -- Contradiction: Fintype.card α + 1 ≤ card ≤ Fintype.card α
  exact absurd (Nat.le_trans (h_lower _) h_upper) (by omega)
