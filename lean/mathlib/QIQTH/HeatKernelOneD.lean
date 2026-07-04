/-
  Track A (increment A2) — the FIRST DERIVED heat-kernel coefficient.

  WHAT IS DERIVED HERE (and why it matters). Every heat-kernel / Seeley–DeWitt coefficient used so
  far in this repository (`SakharovRatio.lean`'s `1/48π, 1/12π`, `InducedNewtonConstant.lean`'s
  per-species `c_i`) is **CITED, hand-entered data**. This file contains the first such coefficient
  that is *derived — not cited*: the 1D free heat-trace density

      (1/2π) ∫ dk e^{-t k²} = 1/√(4πt)

  is proved from Mathlib's Gaussian integral `integral_gaussian` (∫ e^{-b x²} = √(π/b)), i.e. the
  coefficient `1/√(4πt)` — the d = 1 instance of the universal `(4πt)^{-d/2}` — comes out of the
  analysis, not out of a literature lookup. Second, the `Λ²` in the held induced-gravity relation
  `1/G = N_eff Λ²` (`inducedInvG`) is realized as a genuine momentum-space cutoff integral
  `∫₀^Λ 2k dk = Λ²` (`integral_id`), so the quadratic cutoff dependence is *computed*, not decreed.

  ⚠ HONEST SCOPE. This is the 1D, free, flat (pure Gaussian) case — the `a₀` (identity) term only.
  The 4D per-species coefficients `c_i` (the curvature `a₁` Seeley–DeWitt data feeding `effSpeciesN`)
  remain **CITED** inputs in `InducedNewtonConstant.lean`; nothing here upgrades them. And, as
  before, NO claim is made that the numerical value of `G` is derived — `inducedInvG_as_integral`
  only re-expresses the held `Λ²` bookkeeping as the integral it abbreviates.
-/
import Mathlib
import QIQTH.InducedNewtonConstant

namespace QIQTH.HeatKernelOneD

open Real MeasureTheory QIQTH.InducedG

/-- **The 1D heat-trace density — the first DERIVED heat-kernel coefficient in the repository.**
    `(1/2π) ∫ dk e^{-t k²} = 1/√(4πt)`: the momentum-space trace density of `e^{tΔ}` on a line,
    the `d = 1` instance of `(4πt)^{-d/2}`, proved from Mathlib's Gaussian integral (not cited). -/
theorem heatDensity_oneD (t : ℝ) (ht : 0 < t) :
    (1 / (2 * Real.pi)) * ∫ k : ℝ, Real.exp (-(t * k ^ 2)) = 1 / Real.sqrt (4 * Real.pi * t) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the Gaussian integral: ∫ e^{-t k²} = √(π/t)
  have hg : (∫ k : ℝ, Real.exp (-(t * k ^ 2))) = Real.sqrt (Real.pi / t) := by
    simpa [neg_mul] using integral_gaussian t
  -- √(4πt) = 2·√π·√t
  have h4 : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4 : ℝ) * Real.pi * t = (2 * Real.sqrt Real.pi * Real.sqrt t) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hπ.le, Real.sq_sqrt ht.le]; norm_num]
    exact Real.sqrt_sq (by positivity)
  rw [hg, h4, Real.sqrt_div hπ.le]
  have hsπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hπ.le
  field_simp
  nlinarith [hππ, hsπ, hst]

/-- **The cutoff moment** `∫₀^Λ 2k dk = Λ²` — the quadratic cutoff integral behind the induced
    `1/G ∝ Λ²`, computed (via `integral_id`), not decreed. -/
theorem cutoff_moment (Λ : ℝ) (_hΛ : 0 ≤ Λ) :
    (∫ k in (0 : ℝ)..Λ, 2 * k) = Λ ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- **The held `Λ²` of `inducedInvG` realized as a momentum-space integral**:
    `1/G = N_eff · ∫₀^Λ 2k dk`. This re-expresses (does NOT numerically derive) the induced
    inverse Newton constant as the cutoff integral its `Λ²` abbreviates; the per-species
    coefficients inside `effSpeciesN` remain cited Seeley–DeWitt data. -/
theorem inducedInvG_as_integral (S : SpeciesContent) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    inducedInvG S Λ = effSpeciesN S * ∫ k in (0 : ℝ)..Λ, 2 * k := by
  rw [cutoff_moment Λ hΛ]
  rfl

end QIQTH.HeatKernelOneD
