/-
  Capacity packing + Markov-style multi-record suppression.

  These are the deterministic and probabilistic finite-record
  consequences of the framework's H2-style additivity postulate
  ("instantiating N macroscopic records costs at least N · I_0")
  and the regional cap Q_R.

  Important caveat (from the GPT-5.5 audit):
  *Exponential* multi-record suppression is **not** a consequence of
  the information bound alone — it requires an additional
  Gibbs/large-deviation/independence postulate.  The Markov-type
  bound proved here is the honest theorem.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace CapacityPacking

/-- **Deterministic capacity-packing bound.**
    If N simultaneous macroscopic records cost at least `N · I_0`
    in modular information, and the regional cap is `Q_R`, then

        N · I_0 ≤ Q_R   ⇒   N ≤ ⌊Q_R / I_0⌋.

    This is the precise form of "at most N_max records fit". -/
theorem packing_bound
    (N : ℕ) (I_0 Q_R : ℝ) (hI_pos : 0 < I_0)
    (hCost : (N : ℝ) * I_0 ≤ Q_R) :
    N ≤ ⌊Q_R / I_0⌋₊ := by
  have hN_le : (N : ℝ) ≤ Q_R / I_0 := by
    rw [le_div_iff₀ hI_pos]; linarith
  exact Nat.le_floor hN_le

/-- **Saturation count.**  The maximum N permitted is exactly
    `⌊Q_R / I_0⌋`. -/
noncomputable def N_max (I_0 Q_R : ℝ) : ℕ := ⌊Q_R / I_0⌋₊

theorem N_max_spec (I_0 Q_R : ℝ) (hI_pos : 0 < I_0) (N : ℕ)
    (hCost : (N : ℝ) * I_0 ≤ Q_R) :
    N ≤ N_max I_0 Q_R := packing_bound N I_0 Q_R hI_pos hCost

/-- **Markov-style suppression — expectation form.**
    If the total modular slack above the H2-additive baseline is
    `δ ≥ 0`, the expected number of *extra* records (beyond the
    saturation count) is at most `δ / I_0`.

    This is the honest probabilistic bound: it follows from
    Markov's inequality applied to the per-record cost.  No
    exponential decay claim is made — that would need an extra
    independence/Gibbs postulate. -/
theorem markov_expectation
    (I_0 δ E_extra : ℝ) (hI_pos : 0 < I_0) (hδ_nn : 0 ≤ δ)
    (hMarkov_premise : E_extra * I_0 ≤ δ) :
    E_extra ≤ δ / I_0 := by
  rw [le_div_iff₀ hI_pos]; linarith

/-- **Markov-style suppression — tail form.**
    For any threshold m ≥ 1, the probability of having at least
    `m` extra records is bounded by `δ / (m · I_0)`. -/
theorem markov_tail
    (I_0 δ m P_geq_m : ℝ) (hI_pos : 0 < I_0) (hm_pos : 0 < m)
    (hδ_nn : 0 ≤ δ) (hP_nn : 0 ≤ P_geq_m)
    (hMarkov_premise : P_geq_m * m * I_0 ≤ δ) :
    P_geq_m ≤ δ / (m * I_0) := by
  have hmI : 0 < m * I_0 := mul_pos hm_pos hI_pos
  rw [le_div_iff₀ hmI]
  linarith

/-- The packing bound is monotone in the regional cap. -/
theorem N_max_monotone
    (I_0 Q₁ Q₂ : ℝ) (hI_pos : 0 < I_0) (hQ : Q₁ ≤ Q₂) :
    N_max I_0 Q₁ ≤ N_max I_0 Q₂ := by
  unfold N_max
  exact Nat.floor_le_floor (by exact div_le_div_of_nonneg_right hQ (le_of_lt hI_pos))

end CapacityPacking
end QIQTH
