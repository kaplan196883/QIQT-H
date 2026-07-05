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

/-- **★ A4 — THE CONDITIONAL a₁ ASSEMBLY.** Given the Riemann-normal-coordinate curvature data
    as CARRIED hypotheses — the Ricci components `Rμν`, the scalar `Rscl = ∑ᵢ Rμν i i`, the
    Gaussian second-moment matrix `Mmatrix i j = 2t·δ_{ij}` (the `2t` is the DERIVED nugget
    `gaussianSecondMoment_oneD`; for `d = 1` it is exactly that lemma, see
    `heat_a1_moment_from_secondMoment`), and the assembled conformal-coupling coefficient value
    `κ = 1/6` (CARRIED, CITED textbook data) — the Gaussian-averaged `t¹` coefficient assembles
    to the scalar `a₁ = (1/6 − ξ)R − m²`.

    ⚠ HONESTY (binding): the `(1/2t)·κ·(2t·R) = κ·R` step shows the Gaussian moment supplies the
    `2t·R` contraction and the **carried** `κ = 1/6` supplies the value. The moment does NOT and
    CANNOT produce the `1/6`; that is cited curved-space geometry. This is the analysis-half
    assembly of one coefficient, not a derivation of `κ` or of the numerical value of `G`. -/
theorem heat_a1_of_RNC {d : ℕ} (t : ℝ) (ht : 0 < t) (ξ m : ℝ)
    (Rμν : Fin d → Fin d → ℝ)
    (κ : ℝ) (hκ : κ = 1 / 6)
    (Mmatrix : Fin d → Fin d → ℝ)
    (hM : ∀ i j, Mmatrix i j = 2 * t * (if i = j then 1 else 0))
    (Rscl : ℝ) (hR : Rscl = ∑ i, Rμν i i) :
    (1 / (2 * t)) * (κ * ∑ i, ∑ j, Rμν i j * Mmatrix i j) - ξ * Rscl - m ^ 2
      = (1 / 6 - ξ) * Rscl - m ^ 2 := by
  have ht0 : (2 * t) ≠ 0 := by positivity
  have key : (∑ i, ∑ j, Rμν i j * Mmatrix i j) = 2 * t * Rscl := by
    rw [hR, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [hM, if_pos rfl]; ring
    · intro j _ hji
      rw [hM, if_neg (fun h => hji h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [key, hκ]
  field_simp

/-- **The `d = 1` connection to the derived analysis.** In one dimension the carried moment-matrix
    hypothesis `hM` of `heat_a1_of_RNC` is exactly the load-bearing lemma
    `gaussianSecondMoment_oneD` (`∫ G_t x² = 2t`): the single moment entry `∫ G_t x² = 2t` fills
    the `Mmatrix 0 0 = 2t·δ_{00} = 2t` slot. So for `d = 1` the a₁ assembly rests on the DERIVED
    Gaussian second moment, with only the curved-space `κ = 1/6` and the Ricci datum carried. -/
theorem heat_a1_moment_from_secondMoment (t : ℝ) (ht : 0 < t) :
    (fun _ _ : Fin 1 => ∫ x : ℝ, heatKernel1D t x * x ^ 2)
      = (fun i j : Fin 1 => 2 * t * (if i = j then 1 else 0)) := by
  funext i j
  have hij : i = j := Subsingleton.elim i j
  rw [gaussianSecondMoment_oneD t ht, if_pos hij, mul_one]

end QIQTH.HeatKernelA1
