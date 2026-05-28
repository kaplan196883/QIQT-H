/-
  Resolution-floor monotonicity + units calculus.
  Extends `Resolution.lean` with quantitative comparison and
  bits/nats conversion — protects downstream bounds from hidden
  `log 2` mistakes.
-/

import QIQTH.Resolution
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace Resolution

/-- **Monotonicity of the resolution floor.**  More information bits
    means finer resolution: Q_1 ≤ Q_2 ⇒ eps(Q_2) ≤ eps(Q_1). -/
theorem eps_antitone : ∀ {Q₁ Q₂ : ℕ}, Q₁ ≤ Q₂ → eps Q₂ ≤ eps Q₁ := by
  intro Q₁ Q₂ h
  unfold eps
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- For Q = 0 (no information bits) the resolution floor is 1 —
    no amplitudes are distinguishable. -/
theorem eps_zero : eps 0 = 1 := rfl

/-- Strict positivity in stronger form: `eps Q ≥ (1/2)^Q`. -/
theorem eps_geq_half_pow (Q : ℕ) : eps Q ≥ (1/2 : ℝ) ^ Q := by
  unfold eps
  exact le_refl _

/-- **Bits to nats conversion.**  An information bound `B` expressed
    in bits equals `B * log 2` nats. -/
noncomputable def bitsToNats (B : ℝ) : ℝ := B * Real.log 2

/-- **Nats to bits conversion.** -/
noncomputable def natsToBits (N : ℝ) : ℝ := N / Real.log 2

/-- The conversions are mutually inverse on positive reals. -/
theorem bitsToNats_natsToBits (N : ℝ) : bitsToNats (natsToBits N) = N := by
  unfold bitsToNats natsToBits
  field_simp

theorem natsToBits_bitsToNats (B : ℝ) : natsToBits (bitsToNats B) = B := by
  unfold bitsToNats natsToBits
  field_simp

/-- Both conversions are strictly positive (`log 2 > 0`). -/
theorem bitsToNats_pos {B : ℝ} (hB : 0 < B) : 0 < bitsToNats B := by
  unfold bitsToNats
  exact mul_pos hB (Real.log_pos (by norm_num : (1:ℝ) < 2))

theorem natsToBits_pos {N : ℝ} (hN : 0 < N) : 0 < natsToBits N := by
  unfold natsToBits
  exact div_pos hN (Real.log_pos (by norm_num : (1:ℝ) < 2))

/-- **Complement lemma.**  If a probability `p ≤ eps Q`, its
    complement satisfies `1 − p ≥ 1 − eps Q`.  Used in FQ-floor
    arguments where a near-extreme amplitude implies its complement
    is also near-extreme. -/
theorem complement_ge {Q : ℕ} {p : ℝ} (hp : p ≤ eps Q) :
    (1 : ℝ) - eps Q ≤ 1 - p := by
  linarith

end Resolution
end QIQTH
