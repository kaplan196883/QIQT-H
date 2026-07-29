/-
  SmoothCutoff — a smooth radial cutoff on `Point n` (sup-norm coordinate space).

  `Point n = Fin n → ℝ` carries the sup norm, which is NOT smooth, so a radial cutoff cannot be
  built directly from `‖·‖`.  Instead we compose Mathlib's 1D smooth transition
  `Real.smoothTransition` with an affine function of the SMOOTH squared radial coordinate
  `rncRadialSq v = ∑ᵢ (vⁱ)²` (a global polynomial, hence `C∞`; in fact analytic).

  For radii `0 < a < b` we set
    `radialCutoff a b v = Real.smoothTransition ((b² − rncRadialSq v) / (b² − a²))`,
  giving a function that is
    * `≡ 1` on the near ball `rncRadialSq v ≤ a²`  (argument `≥ 1`),
    * `≡ 0` outside the far ball `rncRadialSq v ≥ b²`  (argument `≤ 0`),
    * `C∞` (smooth) — smooth transition composed with an affine function of `rncRadialSq`,
    * valued in `[0, 1]`.

  This is the FOUNDATIONAL primitive of the C4c cutoff-parametrix construction toward the
  far-field residual bound (`residual_global_baseKernelW_of_gaussianCofactor`) and the
  unconditional `a₁ = R/6` heat-kernel coefficient.  It is NOT itself `a₁ = R/6`.

  NB on smoothness order: `rncRadialSq` is analytic (`ContDiff ℝ ⊤` = `ω`), but `smoothTransition`
  is `C∞` and NOT analytic, so the cutoff is stated at `∞` (= `(⊤ : ℕ∞)`), not `ω`.  `C∞` is all
  the downstream `Δ_g`-based far-field estimate needs.
-/

import Mathlib
import QIQTH.Curvature
import QIQTH.RadialDistance

set_option maxHeartbeats 800000

open QIQTH.Curvature QIQTH.RadialDistance
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- Smooth radial cutoff on `Point n`.  For `0 < a < b` it is `≡ 1` on `rncRadialSq ≤ a²`,
`≡ 0` on `rncRadialSq ≥ b²`, smooth, and valued in `[0,1]`.  Built as `Real.smoothTransition`
of the affine-in-`rncRadialSq` argument `(b² − r²)/(b² − a²)`. -/
noncomputable def radialCutoff (a b : ℝ) (v : Point n) : ℝ :=
  Real.smoothTransition ((b ^ 2 - rncRadialSq v) / (b ^ 2 - a ^ 2))

/-- The radial cutoff is `C∞` (smooth), for any radii `a b`.  No positivity hypotheses are needed
for smoothness: `Real.smoothTransition` is `C∞` and the argument is an affine (division by the
constant `b² − a²`, possibly `0`) function of the smooth `rncRadialSq`. -/
theorem radialCutoff_contDiff (a b : ℝ) :
    ContDiff ℝ ∞ (radialCutoff a b : Point n → ℝ) := by
  have hr : ContDiff ℝ ∞ (rncRadialSq : Point n → ℝ) :=
    (rncRadialSq_contDiff).of_le le_top
  have harg : ContDiff ℝ ∞ (fun v : Point n => (b ^ 2 - rncRadialSq v) / (b ^ 2 - a ^ 2)) :=
    ((contDiff_const.sub hr).div_const (b ^ 2 - a ^ 2))
  exact (Real.smoothTransition.contDiff).comp harg

/-- On the near ball `rncRadialSq v ≤ a²` the cutoff is identically `1`.  Requires `0 < a < b`
(so the denominator `b² − a² > 0` and the argument is `≥ 1`). -/
theorem radialCutoff_eq_one {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (h : rncRadialSq v ≤ a ^ 2) : radialCutoff a b v = 1 := by
  have hd : 0 < b ^ 2 - a ^ 2 := by nlinarith
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div hd]
  linarith

/-- Outside the far ball `rncRadialSq v ≥ b²` the cutoff is identically `0`.  Requires `0 < a < b`
(so the denominator `b² − a² > 0`; the numerator `b² − r² ≤ 0`, so the argument is `≤ 0`). -/
theorem radialCutoff_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (h : b ^ 2 ≤ rncRadialSq v) : radialCutoff a b v = 0 := by
  have hd : 0 < b ^ 2 - a ^ 2 := by nlinarith
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_iff.mpr (Or.inr ⟨by linarith, hd.le⟩)

/-- The cutoff is nonnegative. -/
theorem radialCutoff_nonneg (a b : ℝ) (v : Point n) : 0 ≤ radialCutoff a b v :=
  Real.smoothTransition.nonneg _

/-- The cutoff is bounded above by `1`. -/
theorem radialCutoff_le_one (a b : ℝ) (v : Point n) : radialCutoff a b v ≤ 1 :=
  Real.smoothTransition.le_one _

end QIQTH.HeatResidualBound
