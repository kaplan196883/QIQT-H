/-
  Campaign A1/A2 — the flat-space Gaussian moments of the position-space heat kernel.

  WHAT IS DERIVED HERE (the honest boundary — read it).
  This file proves the *analysis half* of the a₁ Seeley–DeWitt heat-kernel coefficient: the
  flat-space Gaussian moments of the 1-D position-space heat kernel

      G_t(x) = (√(4πt))⁻¹ · exp(−x²/(4t))          (`heatKernel1D`)

  namely the load-bearing SECOND moment

      ∫ G_t(x) · x² dx = 2t                         (`gaussianSecondMoment_oneD`)

  together with the zeroth moment (normalization, `= 1`) and the first moment (`= 0`). These are
  proved from Mathlib's Gaussian machinery via the EXACT bridge
  `G_t(x) = gaussianPDFReal 0 (2t) x` (`heatKernel1D_eq_pdf`): the second moment is the variance
  `Var[id; gaussianReal 0 (2t)] = 2t`.

  ⚠ HONEST SCOPE. This is FLAT-SPACE ANALYSIS ONLY. The `2t` second moment supplies exactly the
  `∑_{αβ} R_{αβ}·(2t δ^{αβ}) = 2t·R` contraction machinery — it does NOT and CANNOT produce the
  curvature coefficient value κ = 1/6. The Riemann-normal-coordinate covariant metric/measure
  expansion (√g = 1 − (1/6)R_{αβ}x^αx^β + …) and the assembled value κ = 1/6 are CARRIED, CITED
  textbook data (Vassilevich / Parker–Toms / Gilkey), never produced here. No Riemannian heat
  kernel, no Seeley–DeWitt recursion, no derivation of κ, and no numerical value of G lives in
  this file. This is the derived-analysis half of one coefficient, not the curved-space geometry.
-/
import Mathlib

namespace QIQTH.HeatKernelA1

open Real MeasureTheory ProbabilityTheory

/-- **The 1-D position-space heat kernel** `G_t(x) = (√(4πt))⁻¹ · exp(−x²/(4t))`, the
    fundamental solution of `∂_t u = ∂²_x u`. Equal to the Gaussian pdf of mean `0` and variance
    `2t` (see `heatKernel1D_eq_pdf`). -/
noncomputable def heatKernel1D (t x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))

/-- **The pdf bridge (EXACT).** `G_t(x) = gaussianPDFReal 0 (2t) x`: the position-space heat
    kernel is precisely the Gaussian probability density of mean `0` and variance `2t`, since
    `2π·(2t) = 4πt` and `2·(2t) = 4t`. This is what lets Mathlib's Gaussian moments compute the
    heat-kernel moments. -/
theorem heatKernel1D_eq_pdf (t x : ℝ) (ht : 0 < t) :
    heatKernel1D t x = gaussianPDFReal 0 ((2 * t).toNNReal) x := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  rw [heatKernel1D, gaussianPDFReal, Real.coe_toNNReal (2 * t) h2t.le]
  have e1 : 2 * Real.pi * (2 * t) = 4 * Real.pi * t := by ring
  have e2 : (2 : ℝ) * (2 * t) = 4 * t := by ring
  rw [e1, e2, sub_zero]

/-- **★ THE LOAD-BEARING ANALYSIS — the 1-D Gaussian second moment.**
    `∫ G_t(x) · x² dx = 2t`. Proved as the variance `Var[id; gaussianReal 0 (2t)] = 2t` via the
    pdf bridge. This `2t` is the derived nugget that supplies the `2t·R` curvature contraction;
    the coefficient κ = 1/6 it multiplies is carried, cited geometry, NOT produced here. -/
theorem gaussianSecondMoment_oneD (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, heatKernel1D t x * x ^ 2 = 2 * t := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hcoe : ((2 * t).toNNReal : ℝ) = 2 * t := Real.coe_toNNReal (2 * t) h2t.le
  have hv : (2 * t).toNNReal ≠ 0 := by rw [Ne, Real.toNNReal_eq_zero]; linarith
  have hint : ∀ x : ℝ, heatKernel1D t x * x ^ 2
      = gaussianPDFReal 0 ((2 * t).toNNReal) x • x ^ 2 := by
    intro x; rw [heatKernel1D_eq_pdf t x ht, smul_eq_mul]
  rw [integral_congr_ae (ae_of_all _ hint), ← integral_gaussianReal_eq_integral_smul hv]
  have hvar := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (2 * t).toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simp only [integral_id_gaussianReal, sub_zero] at hvar
  rw [hvar, hcoe]

/-- **The zeroth moment (normalization).** `∫ G_t(x) dx = 1`: the heat kernel integrates to one,
    since it is the Gaussian pdf of a probability measure. -/
theorem gaussianZerothMoment_oneD (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, heatKernel1D t x = 1 := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hv : (2 * t).toNNReal ≠ 0 := by rw [Ne, Real.toNNReal_eq_zero]; linarith
  rw [integral_congr_ae (ae_of_all _ (fun x => heatKernel1D_eq_pdf t x ht))]
  exact integral_gaussianPDFReal_eq_one 0 hv

/-- **The first moment (mean).** `∫ G_t(x) · x dx = 0`: the heat kernel is centered at the
    origin, so its first moment vanishes (mean of `gaussianReal 0 (2t)` is `0`). -/
theorem gaussianFirstMoment_oneD (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, heatKernel1D t x * x = 0 := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hv : (2 * t).toNNReal ≠ 0 := by rw [Ne, Real.toNNReal_eq_zero]; linarith
  have hint : ∀ x : ℝ, heatKernel1D t x * x
      = gaussianPDFReal 0 ((2 * t).toNNReal) x • x := by
    intro x; rw [heatKernel1D_eq_pdf t x ht, smul_eq_mul]
  rw [integral_congr_ae (ae_of_all _ hint), ← integral_gaussianReal_eq_integral_smul hv,
    integral_id_gaussianReal]

end QIQTH.HeatKernelA1
