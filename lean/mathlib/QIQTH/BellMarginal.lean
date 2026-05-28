/-
  Bell / POVM marginalization identity.

  Standard AQFT/Bell-scenario no-signaling proof:  for commuting local
  POVMs `E : α → R` (Alice) and `F : β → R` (Bob) with `Σ_b F_b = 1`,

      Σ_b ω(E_a · F_b)  =  ω(E_a).

  This is the algebraic-identity content of no-signaling, independent
  of channel language — what's left after AQFT microcausality has
  already been used to make the products `E_a · F_b` commute.

  We prove the *algebraic* marginal identity here.  Positivity of
  `E_a · F_b` for commuting positives is a C*-algebra theorem
  requiring Mathlib-level positive-cone infrastructure; we don't
  formalize it here.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic

namespace QIQTH
namespace BellMarginal

/-- An abstract *state* on a ring `R`: an additive functional `R → ℝ`. -/
structure BellState (R : Type*) [Ring R] where
  act : R → ℝ
  map_add : ∀ x y : R, act (x + y) = act x + act y
  map_zero : act (0 : R) = 0

/-- Auxiliary: BellState is additive over Finset sums. -/
private theorem state_sum_linear {R : Type*} [Ring R]
    {ι : Type*} [DecidableEq ι] (ω : BellState R) (g : ι → R) :
    ∀ t : Finset ι, ∑ k ∈ t, ω.act (g k) = ω.act (∑ k ∈ t, g k) := by
  intro t
  induction t using Finset.induction_on with
  | empty => simp [ω.map_zero]
  | insert head t' hhead_notin ih =>
      rw [Finset.sum_insert hhead_notin, Finset.sum_insert hhead_notin,
          ω.map_add, ih]

/-- **Algebraic marginal identity.**
    For any state ω, any Alice element `E_a`, and any finite family
    `F : ι → R` with `Σ F_b = 1`:
        Σ_b ω(E_a · F_b)  =  ω(E_a). -/
theorem marginal_sum {R : Type*} [Ring R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (ω : BellState R)
    (E_a : R) (F : ι → R) (hF_complete : ∑ b ∈ s, F b = 1) :
    ∑ b ∈ s, ω.act (E_a * F b) = ω.act E_a := by
  rw [state_sum_linear ω (fun b => E_a * F b) s]
  congr 1
  rw [← Finset.mul_sum, hF_complete, mul_one]

/-- **Bell-scenario no-signaling, algebraic form.**
    The same Alice element gives the same marginal under any Bob POVM
    family that sums to 1 — independence of Alice's marginal from
    Bob's choice. -/
theorem bell_no_signaling {R : Type*} [Ring R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (ω : BellState R)
    (E_a : R) (F_y F_y' : ι → R)
    (hF_y_complete : ∑ b ∈ s, F_y b = 1)
    (hF_y'_complete : ∑ b ∈ s, F_y' b = 1) :
    (∑ b ∈ s, ω.act (E_a * F_y b)) =
    (∑ b ∈ s, ω.act (E_a * F_y' b)) := by
  rw [marginal_sum s ω E_a F_y hF_y_complete,
      marginal_sum s ω E_a F_y' hF_y'_complete]

end BellMarginal
end QIQTH
