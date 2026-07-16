/-
  GaussianConvolution — the flat Gaussian heat kernel forms a convolution SEMIGROUP
  (Chapman–Kolmogorov): spatial convolution of the fundamental solutions at times `t` and `s`
  is the fundamental solution at time `t + s`. Concretely, "variances add":

      ∫ heatKernel1D t (x − z) · heatKernel1D s (z − y) dz = heatKernel1D (t + s) (x − y).

  This is Phase C1 of the convergence-infrastructure campaign
  (docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md): the foundational Gaussian estimate on
  which Levi/Duhamel heat-kernel convergence is built.

  ROUTE (a) — direct completion of the square. The integrand is
  `A_t A_s · exp(−(x−z)²/(4t) − (z−y)²/(4s))`; completing the square in `z` (leading coefficient
  `1/(4t)+1/(4s) = (t+s)/(4ts)`) pulls out a `z`-independent Gaussian in `(x−y)` of variance
  `4(t+s)`, leaving a shifted Gaussian in `z` evaluated by `integral_gaussian`
  (`∫ e^{−b z²} = √(π/b)`) plus translation invariance. The `(4π·)^{−1/2}` normalizations
  combine exactly: `A_t A_s √(π/((t+s)/(4ts))) = A_{t+s}`.

  ⚠ HONEST SCOPE. This is the FLAT (leading) parametrix term ONLY. It is a genuine Gaussian
  analysis fact — the convolution semigroup of the flat kernel — and is a FOUNDATION for the
  Levi/Duhamel convergence machinery, NOT a claim about the true curved heat kernel, the
  Seeley–DeWitt recursion, or `a₁ = R/6` (phases C5/C6). No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.FlatHeatEquation

open Real MeasureTheory ProbabilityTheory
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation

namespace QIQTH.GaussianConvolution

set_option maxHeartbeats 1600000

/-! ### Helper positivity / integrability of the flat kernel. -/

/-- **The flat 1-D kernel is strictly positive** for `t > 0`: a positive prefactor times a
    (strictly positive) exponential. -/
theorem heatKernel1D_pos (t x : ℝ) (ht : 0 < t) : 0 < heatKernel1D t x := by
  rw [heatKernel1D]
  positivity

/-- **The flat 1-D kernel is integrable** (Lebesgue) for `t > 0`: a constant multiple of the
    Gaussian `exp(−(1/4t)·x²)`. -/
theorem heatKernel1D_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => heatKernel1D t x) volume := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (4 * Real.pi * t))⁻¹
  refine h.congr (ae_of_all _ (fun x => ?_))
  simp only [heatKernel1D]
  rw [show (-(1 / (4 * t)) * x ^ 2 : ℝ) = -x ^ 2 / (4 * t) from by ring]

/-! ### The 1-D convolution semigroup (the core deliverable). -/

/-- **★ THE 1-D GAUSSIAN CONVOLUTION SEMIGROUP (Chapman–Kolmogorov).**
    `∫ G_t(x − z) · G_s(z − y) dz = G_{t+s}(x − y)` for `t, s > 0`. Proved by completing the
    square in `z`: the integrand equals `[A_t A_s exp(−(x−y)²/(4(t+s)))] · exp(−b (z − z₀)²)`
    with `b = (t+s)/(4ts)`, `z₀ = (sx+ty)/(s+t)`; the `z`-Gaussian integrates to `√(π/b)` by
    `integral_gaussian` + translation invariance, and the normalizations combine to `A_{t+s}`. -/
theorem heatKernel1D_conv (t s x y : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ∫ z : ℝ, heatKernel1D t (x - z) * heatKernel1D s (z - y)
      = heatKernel1D (t + s) (x - y) := by
  have htne : t ≠ 0 := ht.ne'
  have hsne : s ≠ 0 := hs.ne'
  have hts : (0 : ℝ) < t + s := by linarith
  have htsne : (t + s) ≠ 0 := hts.ne'
  have hstne : (s + t) ≠ 0 := by rw [add_comm]; exact htsne
  have hpi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := hpi.ne'
  set b : ℝ := (t + s) / (4 * t * s) with hb_def
  set z₀ : ℝ := (s * x + t * y) / (s + t) with hz₀_def
  set D : ℝ := (x - y) ^ 2 / (4 * (t + s)) with hD_def
  -- the pointwise completion of the square
  have hpt : ∀ z : ℝ, heatKernel1D t (x - z) * heatKernel1D s (z - y)
      = (Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (-D)
          * Real.exp (-b * (z - z₀) ^ 2) := by
    intro z
    have key : Real.exp (-(x - z) ^ 2 / (4 * t)) * Real.exp (-(z - y) ^ 2 / (4 * s))
        = Real.exp (-D) * Real.exp (-b * (z - z₀) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hD_def, hb_def, hz₀_def]
      field_simp
      ring
    simp only [heatKernel1D]
    rw [show ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x - z) ^ 2 / (4 * t)))
          * ((Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (-(z - y) ^ 2 / (4 * s)))
        = (Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt (4 * Real.pi * s))⁻¹
            * (Real.exp (-(x - z) ^ 2 / (4 * t)) * Real.exp (-(z - y) ^ 2 / (4 * s))) from by ring]
    rw [key]
    ring
  -- rewrite the integrand
  simp only [hpt]
  -- pull out the z-independent constant
  rw [integral_const_mul]
  -- translation invariance: ∫ exp(−b (z − z₀)²) = ∫ exp(−b z²)
  have hshift : (∫ z : ℝ, Real.exp (-b * (z - z₀) ^ 2)) = ∫ z : ℝ, Real.exp (-b * z ^ 2) := by
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun w : ℝ => Real.exp (-b * w ^ 2)) z₀
    simpa using this
  rw [hshift, integral_gaussian]
  -- the sqrt normalizations combine to A_{t+s}
  have hsqrt_id : (Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt (4 * Real.pi * s))⁻¹
      * Real.sqrt (Real.pi / b) = (Real.sqrt (4 * Real.pi * (t + s)))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv]
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hb_def]
    field_simp
  -- assemble
  simp only [heatKernel1D]
  have hDexp : Real.exp (-D) = Real.exp (-(x - y) ^ 2 / (4 * (t + s))) := by
    rw [hD_def]; congr 1; ring
  calc (Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (-D)
          * Real.sqrt (Real.pi / b)
      = ((Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt (4 * Real.pi * s))⁻¹
            * Real.sqrt (Real.pi / b)) * Real.exp (-D) := by ring
    _ = (Real.sqrt (4 * Real.pi * (t + s)))⁻¹ * Real.exp (-D) := by rw [hsqrt_id]
    _ = (Real.sqrt (4 * Real.pi * (t + s)))⁻¹ * Real.exp (-(x - y) ^ 2 / (4 * (t + s))) := by
          rw [hDexp]

/-! ### The `d`-dimensional convolution semigroup. -/

/-- **★ THE `d`-DIMENSIONAL GAUSSIAN CONVOLUTION SEMIGROUP.**
    `∫ G_t(x − z) · G_s(z − y) dz = G_{t+s}(x − y)` on `Point n = Fin n → ℝ` for `t, s > 0`,
    where `G = gaussDdim`. The `Point n` integral FACTORS as a product of 1-D integrals
    (`integral_fintype_prod_eq_prod` over the Pi/Lebesgue measure), each closed by
    `heatKernel1D_conv`. -/
theorem gaussDdim_conv {n : ℕ} (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x y : Point n) :
    ∫ z : Point n, gaussDdim t (x - z) * gaussDdim s (z - y)
      = gaussDdim (t + s) (x - y) := by
  simp only [gaussDdim]
  -- combine the two coordinate products into one product of per-coordinate integrands
  have hpt : ∀ z : Point n,
      (∏ k, heatKernel1D t ((x - z) k)) * (∏ k, heatKernel1D s ((z - y) k))
        = ∏ k, (heatKernel1D t (x k - z k) * heatKernel1D s (z k - y k)) := by
    intro z
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => by rw [Pi.sub_apply, Pi.sub_apply])
  simp only [hpt]
  -- factor the Pi-integral into a product of 1-D integrals
  rw [show (volume : Measure (Point n)) = Measure.pi (fun _ => (volume : Measure ℝ)) from
        volume_pi]
  rw [integral_fintype_prod_eq_prod
        (fun k (w : ℝ) => heatKernel1D t (x k - w) * heatKernel1D s (w - y k))]
  -- each factor is a 1-D convolution
  exact Finset.prod_congr rfl (fun k _ => by
    rw [heatKernel1D_conv t s (x k) (y k) ht hs, Pi.sub_apply])

end QIQTH.GaussianConvolution
