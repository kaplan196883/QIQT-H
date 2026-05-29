/-
  Sub-theorem B — Operational frequency no-go.

  GPT-5.5-pro fifth audit:

      "Operational frequency constraints determine only the pushforward
       measure on the operational event algebra, not the full IC
       measure.  Operational data only sees the pushforward of the
       IC measure through measurement maps."

  Strategic content: the Canonical IC Measure Principle cannot be
  solved purely by operational axioms.  Some structural / dynamical
  input (Mackey-Gleason noncontextuality from sub-theorem A,
  Goldstein-Struyve naturality from sub-theorem C) is required to
  pick out a unique μ.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

namespace QIQTH
namespace OperationalNoGo

open Classical

/-- Outcome marginal of a measure on a 3-element IC space mapping to
    a 2-element outcome space. -/
noncomputable def marginal3to2
    (μ : Fin 3 → ℝ) (outcome : Fin 3 → Fin 2) (k : Fin 2) : ℝ :=
  ∑ i, if outcome i = k then μ i else 0

/-- The outcome map: 0 ↦ 0, 1 ↦ 0, 2 ↦ 1. Outcome 0 has two pre-images. -/
def outcomeMap : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- First measure: (1/4, 1/4, 1/2) — spreads mass over both preimages of 0. -/
noncomputable def μ₁ : Fin 3 → ℝ
  | 0 => 1/4
  | 1 => 1/4
  | 2 => 1/2

/-- Second measure: (1/2, 0, 1/2) — concentrates all of outcome-0's mass on IC 0. -/
noncomputable def μ₂ : Fin 3 → ℝ
  | 0 => 1/2
  | 1 => 0
  | 2 => 1/2

/-- **Both measures have the same outcome marginal `(1/2, 1/2)`.** -/
theorem marginals_agree (k : Fin 2) :
    marginal3to2 μ₁ outcomeMap k = marginal3to2 μ₂ outcomeMap k := by
  unfold marginal3to2
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases k <;> simp [outcomeMap, μ₁, μ₂] <;> norm_num

/-- **μ₁ and μ₂ are distinct functions.** -/
theorem measures_distinct : μ₁ ≠ μ₂ := by
  intro h
  have := congr_fun h 1
  -- μ₁ 1 = 1/4, μ₂ 1 = 0, so they cannot be equal.
  show False
  have h1 : μ₁ 1 = 1/4 := rfl
  have h2 : μ₂ 1 = 0 := rfl
  rw [h1, h2] at this
  linarith

/-- **Sub-theorem B — operational data insufficient (concrete witness).**

    There exist two distinct IC measures `μ₁`, `μ₂` on `Fin 3` with
    the same outcome marginal under `outcomeMap`.  Operational
    frequency data therefore cannot distinguish them.  Hence operational
    axioms alone cannot pick out a canonical IC measure. -/
theorem operational_data_insufficient :
    ∃ (outcome : Fin 3 → Fin 2) (ν₁ ν₂ : Fin 3 → ℝ),
      (∀ k, marginal3to2 ν₁ outcome k = marginal3to2 ν₂ outcome k) ∧
      ν₁ ≠ ν₂ :=
  ⟨outcomeMap, μ₁, μ₂, marginals_agree, measures_distinct⟩

end OperationalNoGo
end QIQTH
