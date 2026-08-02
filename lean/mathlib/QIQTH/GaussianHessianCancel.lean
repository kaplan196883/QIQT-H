/-
  GaussianHessianCancel — J4-124: the Gaussian-Hessian cancellation library.

  WHAT IS DERIVED HERE (the honest boundary — read it).
  The reusable analytic core behind the `hDaLim`/`LapTrunc` limit of the `a₁ = R/6` campaign.
  The second-`x`-derivative of the heat sliver `∫∫ ∂ᵢ²G_τ(z−x)·q(z)` diverges absolutely like
  `1/τ`, but the exact second-moment cancellation `∫_z ∂ᵢ²G_τ = 0` lets one subtract `q(x)` and
  turn the divergence into an integrable `Lip(q)·C·τ^{−1/2}` bound.  This file proves those
  identities/bounds at the flat product Gaussian `gaussDdim t z = ∏ₖ G_t(zₖ)`:

    • (G1)  the coordinate second partial in coefficient form (reused from `FlatHeatEquation`);
    • (G2)  the EXACT cancellation identity `∫_z ((zᵢ)²−2t)/(4t²)·G_t(z) = 0`;
    • (G3)  the 1-D weighted moment bounds
              `∫ |((y)²−2t)/(4t²)|·G_t ≤ t⁻¹`,  `∫ |y|·G_t ≤ (3/2)√t`,
              `∫ |((y)²−2t)/(4t²)|·|y|·G_t ≤ (15/2)/√t`;
    • (G4)  THE CANCELLATION LEMMA `gaussian_hessian_cancel`: for `q` Lipschitz (const `L ≥ 0`,
              bounded, measurable),
              `|∫_z ((zᵢ)²−2t)/(4t²)·G_t(z)·q(z)| ≤ L·(15/2·n)/√t`.

  ⚠ HONEST FIREWALL.
    LANDED: G1, G2, G3 (all three 1-D moment bounds), the n-D per-coordinate bound
      `hk_coord_integral_le`, and G4 (`gaussian_hessian_cancel`) — UNCONDITIONALLY, at the origin.
    DELIBERATE SCOPE: G2/G4 are proved at the base point `x = 0` ONLY (the shifted `z−x` form is
      not taken); this is exactly what the capstone needs — every quantity is evaluated at the RNC
      center (the origin).  The `x = 0` restriction is a deliberate, documented choice, NOT a gap in
      disguise.
    DEFERRED (NOT attempted here): the first-derivative (gradient, odd-moment) analogue
      `gaussian_grad_cancel`, and the G5 sliver-integral corollary `∫₀^ε τ^{−1/2} = 2√ε`.  These
      are straightforward variants of the same pattern but are not part of this brick.
    The Lipschitz/boundedness/measurability hypotheses on `q` are genuine, load-bearing, non-vacuous
      (the bound FAILS without them; `L ≥ 0` is the standard Lipschitz-constant sign).  This is a
      reusable analytic BRICK; it is NOT `a₁ = R/6`.
    No `sorry`, no new axioms, no `expRho` in statements.
-/
import Mathlib
import QIQTH.GaussianPolyBound
import QIQTH.GaussianConvolution

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianPolyBound QIQTH.GaussianConvolution

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Foundation: re-derived light facts (avoid heavy imports). -/

/-- `heatKernel1D t` is continuous. -/
theorem hk_continuous (t : ℝ) : Continuous (fun y : ℝ => heatKernel1D t y) := by
  simp only [heatKernel1D]; fun_prop

/-- `gaussDdim t ≥ 0` (product of nonnegative 1-D kernels). -/
theorem gaussDdim_nonneg' (t : ℝ) (v : Point n) : 0 ≤ gaussDdim t v := by
  rw [gaussDdim]
  exact Finset.prod_nonneg (fun k _ => by rw [heatKernel1D]; positivity)

/-- **(M1) TOTAL MASS ONE.**  `∫ z, gaussDdim t z = 1` for `t > 0`. -/
theorem gaussDdim_mass_one (t : ℝ) (ht : 0 < t) :
    ∫ z : Point n, gaussDdim t z = 1 := by
  simp only [gaussDdim]
  rw [integral_fintype_prod_volume_eq_pow (fun (y : ℝ) => heatKernel1D t y),
      gaussianZerothMoment_oneD t ht, one_pow]

/-- `gaussDdim t` is integrable for `t > 0`. -/
theorem gaussDdim_integrable' (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : Point n => gaussDdim t z) volume :=
  integrable_of_integral_eq_one (gaussDdim_mass_one t ht)

/-! ### 1-D integrability workhorses. -/

/-- `heatKernel1D t y · (y²)^m` is integrable: dominated by the widened Gaussian via C4a. -/
theorem hk_mul_sq_pow_integrable (t : ℝ) (ht : 0 < t) (m : ℕ) :
    Integrable (fun y : ℝ => heatKernel1D t y * (y ^ 2) ^ m) volume := by
  have hb : (0 : ℝ) < 1 / (8 * t) := by positivity
  set C : ℝ := (Real.sqrt (4 * Real.pi * t))⁻¹ * (8 ^ m * (m.factorial : ℝ) * t ^ m) with hC
  have hgint : Integrable (fun y : ℝ => C * Real.exp (-y ^ 2 / (8 * t))) volume := by
    refine ((integrable_exp_neg_mul_sq hb).const_mul C).congr (ae_of_all _ (fun y => ?_))
    show C * Real.exp (-(1 / (8 * t)) * y ^ 2) = C * Real.exp (-y ^ 2 / (8 * t))
    rw [show (-(1 / (8 * t)) * y ^ 2 : ℝ) = -y ^ 2 / (8 * t) from by ring]
  refine hgint.mono' ?_ (ae_of_all _ (fun y => ?_))
  · exact ((hk_continuous t).mul (by fun_prop)).aestronglyMeasurable
  · have hknn : 0 ≤ heatKernel1D t y := (heatKernel1D_pos t y ht).le
    have hpnn : (0 : ℝ) ≤ (y ^ 2) ^ m := by positivity
    have hAnn : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
    have habsorb : (y ^ 2) ^ m * Real.exp (-y ^ 2 / (4 * t))
        ≤ 8 ^ m * (m.factorial : ℝ) * t ^ m * Real.exp (-y ^ 2 / (8 * t)) := by
      simpa using gaussian_poly_absorb m ht y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hknn, abs_of_nonneg hpnn, heatKernel1D, hC]
    calc (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y ^ 2 / (4 * t)) * (y ^ 2) ^ m
        = (Real.sqrt (4 * Real.pi * t))⁻¹
            * ((y ^ 2) ^ m * Real.exp (-y ^ 2 / (4 * t))) := by ring
      _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹
            * (8 ^ m * (m.factorial : ℝ) * t ^ m * Real.exp (-y ^ 2 / (8 * t))) :=
          mul_le_mul_of_nonneg_left habsorb hAnn
      _ = (Real.sqrt (4 * Real.pi * t))⁻¹ * (8 ^ m * (m.factorial : ℝ) * t ^ m)
            * Real.exp (-y ^ 2 / (8 * t)) := by ring

/-- Integrability of `heatKernel1D t · w` for a weight `w` dominated by a quartic-in-`y²`
    polynomial with NONNEGATIVE coefficients. -/
theorem hk_mul_integrable_of_poly (t : ℝ) (ht : 0 < t) (w : ℝ → ℝ)
    (hwmeas : AEStronglyMeasurable w volume) (a b c : ℝ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hw : ∀ y, |w y| ≤ a + b * (y ^ 2) + c * (y ^ 2) ^ 2) :
    Integrable (fun y : ℝ => heatKernel1D t y * w y) volume := by
  have hdom : Integrable
      (fun y : ℝ => a * (heatKernel1D t y * (y ^ 2) ^ 0)
        + b * (heatKernel1D t y * (y ^ 2) ^ 1) + c * (heatKernel1D t y * (y ^ 2) ^ 2)) volume :=
    (((hk_mul_sq_pow_integrable t ht 0).const_mul a).add
      ((hk_mul_sq_pow_integrable t ht 1).const_mul b)).add
      ((hk_mul_sq_pow_integrable t ht 2).const_mul c)
  refine hdom.mono' ((hk_continuous t).aestronglyMeasurable.mul hwmeas) (ae_of_all _ (fun y => ?_))
  have hknn : 0 ≤ heatKernel1D t y := (heatKernel1D_pos t y ht).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hknn]
  have heq : a * (heatKernel1D t y * (y ^ 2) ^ 0) + b * (heatKernel1D t y * (y ^ 2) ^ 1)
        + c * (heatKernel1D t y * (y ^ 2) ^ 2)
      = heatKernel1D t y * (a + b * (y ^ 2) + c * (y ^ 2) ^ 2) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hw y) hknn

/-- Continuity/measurability of the hessian weight `|((y)²−2t)/(4t²)|`. -/
theorem hessW_aemeas (t : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => |(y ^ 2 - 2 * t) / (4 * t ^ 2)|) volume := by
  fun_prop

/-- `heatKernel1D t · |((y)²−2t)/(4t²)|` is integrable. -/
theorem hk_absHess_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|) volume := by
  refine hk_mul_integrable_of_poly t ht _ (hessW_aemeas t) (1 / (2 * t)) (1 / (4 * t ^ 2)) 0
    (by positivity) (by positivity) le_rfl (fun y => ?_)
  rw [abs_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
  have hnum : |y ^ 2 - 2 * t| ≤ y ^ 2 + 2 * t := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, ht.le]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * t ^ 2)]
  have htne : t ≠ 0 := ht.ne'
  have hexp : (1 / (2 * t) + 1 / (4 * t ^ 2) * y ^ 2 + 0 * (y ^ 2) ^ 2) * (4 * t ^ 2)
      = 2 * t + y ^ 2 := by field_simp; ring
  rw [hexp]; linarith [hnum]

/-- `heatKernel1D t · |y|` is integrable. -/
theorem hk_absY_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => heatKernel1D t y * |y|) volume := by
  refine hk_mul_integrable_of_poly t ht _ (by fun_prop) 1 1 0
    (by norm_num) (by norm_num) le_rfl (fun y => ?_)
  rw [abs_abs]
  nlinarith [sq_nonneg (|y| - 1), abs_nonneg y, sq_abs y]

/-- `heatKernel1D t · (|((y)²−2t)/(4t²)|·|y|)` is integrable. -/
theorem hk_absHess_absY_integrable (t : ℝ) (ht : 0 < t) :
    Integrable
      (fun y : ℝ => heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|)) volume := by
  refine hk_mul_integrable_of_poly t ht _ (by fun_prop)
    (1 / (2 * t)) (1 / (2 * t) + 1 / (4 * t ^ 2)) (1 / (4 * t ^ 2))
    (by positivity) (by positivity) (by positivity) (fun y => ?_)
  have htne : t ≠ 0 := ht.ne'
  rw [abs_mul, abs_abs, abs_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
  have hnum : |y ^ 2 - 2 * t| ≤ y ^ 2 + 2 * t := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, ht.le]
  have hy : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), abs_nonneg y, sq_abs y]
  have hstep : |y ^ 2 - 2 * t| / (4 * t ^ 2) * |y| ≤ (y ^ 2 + 2 * t) / (4 * t ^ 2) * (1 + y ^ 2) := by
    apply mul_le_mul _ hy (abs_nonneg _) (by positivity)
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * t ^ 2)]
    exact hnum
  refine hstep.trans (le_of_eq ?_)
  field_simp; ring

/-! ### G2 — the exact cancellation identity (at the origin). -/

/-- **(G1) coordinate second partial (coefficient form).**  For `t>0`,
    `∂ᵢ² G(z) = ((zᵢ)²−2t)/(4t²)·G(z)` — the `((zᵢ)²/(4t²) − 1/(2t))·G` of
    `gaussDdim_pd_pd_i` over the common denominator `4t²`. -/
theorem gaussDdim_pd_pd_i_coeff (t : ℝ) (ht : 0 < t) (z : Point n) (i : Fin n) :
    pd (fun y => pd (fun w => gaussDdim t w) i y) i z
      = ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z := by
  rw [gaussDdim_pd_pd_i t ht z i]
  have htne : t ≠ 0 := ht.ne'
  congr 1; field_simp; ring

/-- **(★ G2) THE EXACT CANCELLATION IDENTITY.**  For `t>0`,
    `∫_z ((zᵢ)²−2t)/(4t²)·G_t(z) = 0`: the coordinate-`i` factor gives
    `∫((y²−2t)/(4t²))·G_t = (2t−2t)/(4t²) = 0` (second moment `2t` minus mass-one `2t`). -/
theorem gaussian_hessian_moment_zero (t : ℝ) (ht : 0 < t) (i : Fin n) :
    ∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z = 0 := by
  have htne : t ≠ 0 := ht.ne'
  have hsq_int : Integrable (fun z : Point n => (z i) ^ 2 * gaussDdim t z) volume := by
    have hpt : (fun z : Point n => (z i) ^ 2 * gaussDdim t z)
        = fun z => ∏ k, heatKernel1D t (z k) * (if k = i then (z k) ^ 2 else 1) := by
      funext z
      simp only [gaussDdim]
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
    have hf : ∀ k : Fin n,
        Integrable (fun y : ℝ => heatKernel1D t y * (if k = i then y ^ 2 else 1)) volume := by
      intro k
      by_cases hk : k = i
      · subst hk; simp only [if_pos rfl]
        exact (hk_mul_sq_pow_integrable t ht 1).congr (ae_of_all _ (fun y => by simp))
      · simp only [if_neg hk, mul_one]; exact heatKernel1D_integrable t ht
    rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
    exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf
  have hG_int : Integrable (fun z : Point n => gaussDdim t z) volume := gaussDdim_integrable' t ht
  -- ∫ (zᵢ)²·G = 2t
  have hsq : (∫ z : Point n, (z i) ^ 2 * gaussDdim t z) = 2 * t := by
    have h := gaussianMoment_diag n t ht i i
    rw [if_pos rfl, mul_one] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    simp only [gaussDdim]; ring
  -- ∫ G = 1
  have hG : (∫ z : Point n, gaussDdim t z) = 1 := gaussDdim_mass_one t ht
  -- split
  have hAeq : (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z)
      = fun z => (4 * t ^ 2)⁻¹ * ((z i) ^ 2 * gaussDdim t z)
          - (4 * t ^ 2)⁻¹ * (2 * t) * gaussDdim t z := by
    funext z; rw [div_eq_mul_inv]; ring
  have hsplit : (∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z)
      = (4 * t ^ 2)⁻¹ * (∫ z : Point n, (z i) ^ 2 * gaussDdim t z)
          - (4 * t ^ 2)⁻¹ * (2 * t) * ∫ z : Point n, gaussDdim t z := by
    rw [hAeq, integral_sub (hsq_int.const_mul _) (hG_int.const_mul _),
        integral_const_mul, integral_const_mul]
  rw [hsplit, hsq, hG]; ring

/-! ### G3 — the 1-D weighted moment bounds. -/

/-- **(G3, M3) the odd first absolute moment (√t honestly).**  For `t>0`,
    `∫ y, G_t(y)·|y| ≤ (3/2)·√t`.  Via AM-GM `|y| ≤ (y²+t)/(2√t)`, then the 2t second moment
    and the mass-one zeroth moment. -/
theorem hk_absY_moment_le (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |y| ≤ 3 / 2 * Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hamgm : ∀ y : ℝ, |y| ≤ (y ^ 2 + t) / (2 * Real.sqrt t) := by
    intro y
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|y| - Real.sqrt t), sq_abs y, hsq, abs_nonneg y]
  have hAeq : (fun y : ℝ => heatKernel1D t y * ((y ^ 2 + t) / (2 * Real.sqrt t)))
      = fun y => (2 * Real.sqrt t)⁻¹ * (heatKernel1D t y * y ^ 2 + t * heatKernel1D t y) := by
    funext y; rw [div_eq_mul_inv]; ring
  have hy2_int : Integrable (fun y : ℝ => heatKernel1D t y * y ^ 2) volume :=
    (hk_mul_sq_pow_integrable t ht 1).congr (ae_of_all _ (fun y => by simp))
  have hdom_int : Integrable
      (fun y : ℝ => heatKernel1D t y * ((y ^ 2 + t) / (2 * Real.sqrt t))) volume := by
    rw [hAeq]; exact (hy2_int.add ((heatKernel1D_integrable t ht).const_mul t)).const_mul _
  have hmono : (∫ y : ℝ, heatKernel1D t y * |y|)
      ≤ ∫ y : ℝ, heatKernel1D t y * ((y ^ 2 + t) / (2 * Real.sqrt t)) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun y => ?_)) hdom_int (ae_of_all _ (fun y => ?_))
    · exact mul_nonneg (heatKernel1D_pos t y ht).le (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hamgm y) (heatKernel1D_pos t y ht).le
  have hval : (∫ y : ℝ, heatKernel1D t y * ((y ^ 2 + t) / (2 * Real.sqrt t)))
      = 3 / 2 * Real.sqrt t := by
    rw [hAeq, integral_const_mul,
        integral_add hy2_int ((heatKernel1D_integrable t ht).const_mul t),
        integral_const_mul, gaussianSecondMoment_oneD t ht, gaussianZerothMoment_oneD t ht,
        show (2 * t + t * 1 : ℝ) = 3 * (Real.sqrt t * Real.sqrt t) from by rw [hsq]; ring]
    field_simp
  linarith [hmono, le_of_eq hval]

/-- **(G3, M1) the raw hessian moment.**  For `t>0`,
    `∫ y, G_t(y)·|((y)²−2t)/(4t²)| ≤ t⁻¹`.  Via `|y²−2t| ≤ y²+2t`, the 2t second moment and mass. -/
theorem hk_absHess_moment_le (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)| ≤ t⁻¹ := by
  have htne : t ≠ 0 := ht.ne'
  have hbound : ∀ y : ℝ, |(y ^ 2 - 2 * t) / (4 * t ^ 2)| ≤ (y ^ 2 + 2 * t) / (4 * t ^ 2) := by
    intro y
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
    gcongr
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, ht.le]
  have hAeq : (fun y : ℝ => heatKernel1D t y * ((y ^ 2 + 2 * t) / (4 * t ^ 2)))
      = fun y => (4 * t ^ 2)⁻¹ * (heatKernel1D t y * y ^ 2 + 2 * t * heatKernel1D t y) := by
    funext y; rw [div_eq_mul_inv]; ring
  have hy2_int : Integrable (fun y : ℝ => heatKernel1D t y * y ^ 2) volume :=
    (hk_mul_sq_pow_integrable t ht 1).congr (ae_of_all _ (fun y => by simp))
  have hdom_int : Integrable
      (fun y : ℝ => heatKernel1D t y * ((y ^ 2 + 2 * t) / (4 * t ^ 2))) volume := by
    rw [hAeq]; exact (hy2_int.add ((heatKernel1D_integrable t ht).const_mul (2 * t))).const_mul _
  have hmono : (∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|)
      ≤ ∫ y : ℝ, heatKernel1D t y * ((y ^ 2 + 2 * t) / (4 * t ^ 2)) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun y => ?_)) hdom_int (ae_of_all _ (fun y => ?_))
    · exact mul_nonneg (heatKernel1D_pos t y ht).le (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hbound y) (heatKernel1D_pos t y ht).le
  have hval : (∫ y : ℝ, heatKernel1D t y * ((y ^ 2 + 2 * t) / (4 * t ^ 2))) = t⁻¹ := by
    rw [hAeq, integral_const_mul,
        integral_add hy2_int ((heatKernel1D_integrable t ht).const_mul (2 * t)),
        integral_const_mul, gaussianSecondMoment_oneD t ht, gaussianZerothMoment_oneD t ht]
    field_simp; ring
  linarith [hmono, le_of_eq hval]

/-- The widened Gaussian is a scaled kernel at width `2t`:
    `exp(−y²/(8t)) = √(8πt)·G_{2t}(y)`. -/
theorem exp_eighth_eq (t : ℝ) (ht : 0 < t) (y : ℝ) :
    Real.exp (-y ^ 2 / (8 * t)) = Real.sqrt (8 * Real.pi * t) * heatKernel1D (2 * t) y := by
  have hsne : Real.sqrt (8 * Real.pi * t) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [heatKernel1D, show 4 * Real.pi * (2 * t) = 8 * Real.pi * t from by ring,
      show -y ^ 2 / (4 * (2 * t)) = -y ^ 2 / (8 * t) from by ring, ← mul_assoc,
      mul_inv_cancel₀ hsne, one_mul]

/-- **(G3, M2) the weighted hessian moment (√t honestly).**  For `t>0`,
    `∫ y, G_t(y)·(|((y)²−2t)/(4t²)|·|y|) ≤ (15/2)/√t`.  Via the C4b second-derivative Gaussian
    bound `|∂²G_t| ≤ (5/2)t⁻¹(√(4πt))⁻¹e^{−y²/8t}`, then the first absolute moment at width `2t`. -/
theorem hk_absHess_absY_moment_le (t : ℝ) (ht : 0 < t) :
    ∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|)
      ≤ 15 / 2 / Real.sqrt t := by
  have htne : t ≠ 0 := ht.ne'
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hpt : ∀ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|)
      ≤ (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * (Real.exp (-y ^ 2 / (8 * t)) * |y|) := by
    intro y
    have hkey : |(y ^ 2 - 2 * t) / (4 * t ^ 2)| * heatKernel1D t y
        ≤ 5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y ^ 2 / (8 * t)) := by
      have hd2 := heatKernel1D_deriv2_x_abs_le t y ht
      rw [heatKernel1D_deriv2_x_eq t y ht, abs_mul,
          abs_of_nonneg (heatKernel1D_pos t y ht).le] at hd2
      exact hd2
    calc heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|)
        = (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * heatKernel1D t y) * |y| := by ring
      _ ≤ (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y ^ 2 / (8 * t))) * |y| :=
          mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
      _ = (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
            * (Real.exp (-y ^ 2 / (8 * t)) * |y|) := by ring
  have hDint : Integrable
      (fun y : ℝ => (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
        * (Real.exp (-y ^ 2 / (8 * t)) * |y|)) volume := by
    have hb : Integrable
        (fun y : ℝ => Real.sqrt (8 * Real.pi * t) * (heatKernel1D (2 * t) y * |y|)) volume :=
      (hk_absY_integrable (2 * t) h2t).const_mul _
    refine (hb.const_mul (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)).congr
      (ae_of_all _ (fun y => ?_))
    show (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
        * (Real.sqrt (8 * Real.pi * t) * (heatKernel1D (2 * t) y * |y|))
      = (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * (Real.exp (-y ^ 2 / (8 * t)) * |y|)
    rw [exp_eighth_eq t ht y]; ring
  have hmono : (∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|))
      ≤ ∫ y : ℝ, (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
          * (Real.exp (-y ^ 2 / (8 * t)) * |y|) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun y => ?_)) hDint (ae_of_all _ hpt)
    exact mul_nonneg (heatKernel1D_pos t y ht).le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hRHS : (∫ y : ℝ, (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
        * (Real.exp (-y ^ 2 / (8 * t)) * |y|))
      = (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t)
          * (∫ y : ℝ, heatKernel1D (2 * t) y * |y|) := by
    have heq : (fun y : ℝ => Real.exp (-y ^ 2 / (8 * t)) * |y|)
        = fun y => Real.sqrt (8 * Real.pi * t) * (heatKernel1D (2 * t) y * |y|) := by
      funext y; rw [exp_eighth_eq t ht y]; ring
    rw [integral_const_mul, heq, integral_const_mul]; ring
  have hM3 : (∫ y : ℝ, heatKernel1D (2 * t) y * |y|) ≤ 3 / 2 * Real.sqrt (2 * t) :=
    hk_absY_moment_le (2 * t) h2t
  have hM3nn : 0 ≤ ∫ y : ℝ, heatKernel1D (2 * t) y * |y| :=
    integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos (2 * t) y h2t).le (abs_nonneg _))
  have hKnn : 0 ≤ (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t) := by
    positivity
  have hconst : (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t)
        * (3 / 2 * Real.sqrt (2 * t)) = 15 / 2 / Real.sqrt t := by
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have hs2t : Real.sqrt (2 * t) = Real.sqrt 2 * Real.sqrt t := Real.sqrt_mul (by norm_num) t
    have hA : (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.sqrt (8 * Real.pi * t) = Real.sqrt 2 := by
      rw [← div_eq_inv_mul, ← Real.sqrt_div (by positivity : (0 : ℝ) ≤ 8 * Real.pi * t),
          show 8 * Real.pi * t / (4 * Real.pi * t) = 2 from by
            rw [show (8 : ℝ) * Real.pi * t = 2 * (4 * Real.pi * t) from by ring, mul_div_assoc,
                div_self (by positivity), mul_one]]
    have hts : t⁻¹ * Real.sqrt t = (Real.sqrt t)⁻¹ := by
      field_simp; linear_combination htt
    calc (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t)
          * (3 / 2 * Real.sqrt (2 * t))
        = 5 / 2 * t⁻¹ * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.sqrt (8 * Real.pi * t))
            * (3 / 2 * Real.sqrt (2 * t)) := by ring
      _ = 5 / 2 * t⁻¹ * Real.sqrt 2 * (3 / 2 * (Real.sqrt 2 * Real.sqrt t)) := by rw [hA, hs2t]
      _ = 15 / 4 * (Real.sqrt 2 * Real.sqrt 2) * (t⁻¹ * Real.sqrt t) := by ring
      _ = 15 / 4 * 2 * (t⁻¹ * Real.sqrt t) := by rw [h2]
      _ = 15 / 2 * (t⁻¹ * Real.sqrt t) := by ring
      _ = 15 / 2 / Real.sqrt t := by rw [hts]; ring
  calc (∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|))
      ≤ (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t)
          * (∫ y : ℝ, heatKernel1D (2 * t) y * |y|) := by rw [← hRHS]; exact hmono
    _ ≤ (5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) * Real.sqrt (8 * Real.pi * t)
          * (3 / 2 * Real.sqrt (2 * t)) := by
        exact mul_le_mul_of_nonneg_left hM3 hKnn
    _ = 15 / 2 / Real.sqrt t := hconst

/-- `t⁻¹·√t = (√t)⁻¹` for `t>0`. -/
theorem invT_mul_sqrt (t : ℝ) (ht : 0 < t) : t⁻¹ * Real.sqrt t = (Real.sqrt t)⁻¹ := by
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  field_simp; linear_combination htt

/-! ### G4 — the n-D per-coordinate integrability + bound, and the cancellation lemma. -/

/-- `(zᵢ)²·G_t(z)` is integrable on `Point n`. -/
theorem coordSq_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i : Fin n) :
    Integrable (fun z : Point n => (z i) ^ 2 * gaussDdim t z) volume := by
  have hpt : (fun z : Point n => (z i) ^ 2 * gaussDdim t z)
      = fun z => ∏ k, heatKernel1D t (z k) * (if k = i then (z k) ^ 2 else 1) := by
    funext z; simp only [gaussDdim]; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']; ring
  have hf : ∀ k : Fin n,
      Integrable (fun y : ℝ => heatKernel1D t y * (if k = i then y ^ 2 else 1)) volume := by
    intro k
    by_cases hk : k = i
    · subst hk; simp only [if_pos rfl]
      exact (hk_mul_sq_pow_integrable t ht 1).congr (ae_of_all _ (fun y => by simp))
    · simp only [if_neg hk, mul_one]; exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- `|((zᵢ)²−2t)/(4t²)|·G_t(z)·|z_k|` is integrable on `Point n`. -/
theorem hessAbs_coord_gaussDdim_integrable (t : ℝ) (ht : 0 < t) (i k : Fin n) :
    Integrable
      (fun z : Point n => |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|) volume := by
  have hpt : (fun z : Point n => |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|)
      = fun z => ∏ m, heatKernel1D t (z m)
          * ((if m = i then |(z m ^ 2 - 2 * t) / (4 * t ^ 2)| else 1)
              * (if m = k then |z m| else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq',
        Fintype.prod_ite_eq']
    ring
  have hf : ∀ m : Fin n, Integrable (fun y : ℝ => heatKernel1D t y
      * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = k then |y| else 1)))
      volume := by
    intro m
    by_cases hmi : m = i
    · by_cases hmk : m = k
      · simp only [if_pos hmi, if_pos hmk]; exact hk_absHess_absY_integrable t ht
      · simp only [if_pos hmi, if_neg hmk, mul_one]; exact hk_absHess_integrable t ht
    · by_cases hmk : m = k
      · simp only [if_neg hmi, if_pos hmk, one_mul]; exact hk_absY_integrable t ht
      · simp only [if_neg hmi, if_neg hmk, mul_one, one_mul]
        exact heatKernel1D_integrable t ht
  rw [hpt, show (volume : Measure (Point n)) = Measure.pi (fun _ => volume) from volume_pi]
  exact Integrable.fin_nat_prod (μ := fun _ => (volume : Measure ℝ)) hf

/-- **(★ G3 → n-D) THE PER-COORDINATE BOUND.**  For `t>0` and any `i,k`,
    `∫_z |((zᵢ)²−2t)/(4t²)|·G_t(z)·|z_k| ≤ (15/2)/√t`.  Factorizes coordinatewise: the diagonal
    `k=i` gives the weighted hessian moment `M2`, off-diagonal gives `M1·M3`; both `≤ (15/2)/√t`. -/
theorem hk_coord_integral_le (t : ℝ) (ht : 0 < t) (i k : Fin n) :
    ∫ z : Point n, |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|
      ≤ 15 / 2 / Real.sqrt t := by
  have hpt : (fun z : Point n => |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|)
      = fun z => ∏ m, heatKernel1D t (z m)
          * ((if m = i then |(z m ^ 2 - 2 * t) / (4 * t ^ 2)| else 1)
              * (if m = k then |z m| else 1)) := by
    funext z; simp only [gaussDdim]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_eq',
        Fintype.prod_ite_eq']
    ring
  rw [hpt, integral_fintype_prod_volume_eq_prod
    (fun m (y : ℝ) => heatKernel1D t y
      * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = k then |y| else 1)))]
  by_cases hik : k = i
  · simp only [hik]
    have hprodeq : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
          * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = i then |y| else 1)))
        = ∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|) := by
      calc (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
            * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = i then |y| else 1)))
          = ∏ m : Fin n, (if m = i
              then (∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|)) else 1) := by
            refine Finset.prod_congr rfl (fun m _ => ?_)
            by_cases hm : m = i
            · simp [hm]
            · simp only [if_neg hm, one_mul, mul_one]; exact gaussianZerothMoment_oneD t ht
        _ = ∫ y : ℝ, heatKernel1D t y * (|(y ^ 2 - 2 * t) / (4 * t ^ 2)| * |y|) :=
            Fintype.prod_ite_eq' i _
    rw [hprodeq]; exact hk_absHess_absY_moment_le t ht
  · have hik' : i ≠ k := fun h => hik h.symm
    have hout : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({i, k} : Finset (Fin n)) →
        (if m = i then (∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|)
          else if m = k then (∫ y : ℝ, heatKernel1D t y * |y|) else 1) = 1 := by
      intro m _ hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      push_neg at hm
      simp only [if_neg hm.1, if_neg hm.2]
    have hprodeq : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
          * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = k then |y| else 1)))
        = (∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|)
          * (∫ y : ℝ, heatKernel1D t y * |y|) := by
      have hstep : (∏ m : Fin n, ∫ y : ℝ, heatKernel1D t y
            * ((if m = i then |(y ^ 2 - 2 * t) / (4 * t ^ 2)| else 1) * (if m = k then |y| else 1)))
          = ∏ m : Fin n, (if m = i
              then (∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|)
              else if m = k then (∫ y : ℝ, heatKernel1D t y * |y|) else 1) := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        by_cases hmi : m = i
        · have hmk : ¬ m = k := by rw [hmi]; exact hik'
          simp only [if_pos hmi, if_neg hmk, mul_one]
        · by_cases hmk : m = k
          · simp only [if_neg hmi, if_pos hmk, one_mul]
          · simp only [if_neg hmi, if_neg hmk, one_mul, mul_one]
            exact gaussianZerothMoment_oneD t ht
      rw [hstep, ← Finset.prod_subset (Finset.subset_univ ({i, k} : Finset (Fin n))) hout,
          Finset.prod_pair hik', if_pos rfl, if_neg hik, if_pos rfl]
    rw [hprodeq]
    have hM1 := hk_absHess_moment_le t ht
    have hM3 := hk_absY_moment_le t ht
    have hM3nn : 0 ≤ ∫ y : ℝ, heatKernel1D t y * |y| :=
      integral_nonneg (fun y => mul_nonneg (heatKernel1D_pos t y ht).le (abs_nonneg _))
    calc (∫ y : ℝ, heatKernel1D t y * |(y ^ 2 - 2 * t) / (4 * t ^ 2)|)
            * (∫ y : ℝ, heatKernel1D t y * |y|)
        ≤ t⁻¹ * (3 / 2 * Real.sqrt t) := mul_le_mul hM1 hM3 hM3nn (by positivity)
      _ = 3 / 2 * (t⁻¹ * Real.sqrt t) := by ring
      _ = 3 / 2 * (Real.sqrt t)⁻¹ := by rw [invT_mul_sqrt t ht]
      _ ≤ 15 / 2 * (Real.sqrt t)⁻¹ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 15 / 2 / Real.sqrt t := (div_eq_mul_inv _ _).symm

/-- **★ G4 — THE GAUSSIAN-HESSIAN CANCELLATION LEMMA.**  For `t>0`, `i : Fin n`, and `q` Lipschitz
    with constant `L ≥ 0` (bounded, measurable),
      `|∫_z ((zᵢ)²−2t)/(4t²)·G_t(z)·q(z)| ≤ L·(15/2·n)/√t`.
    Proof: subtract `q 0` via the exact cancellation `gaussian_hessian_moment_zero`, then
    `|∫ …·(q−q 0)| ≤ ∫ ‖…‖ ≤ ∫ L·Σₖ |hess|·G·|z_k| = L·Σₖ(…) ≤ L·(n·(15/2)/√t)` via the
    per-coordinate bound `hk_coord_integral_le`.  Evaluated at the origin `x = 0` (the RNC center). -/
theorem gaussian_hessian_cancel (t : ℝ) (ht : 0 < t) (i : Fin n) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (hqbdd : ∃ M, ∀ z, |q z| ≤ M) :
    |∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z|
      ≤ L * (15 / 2 * n) / Real.sqrt t := by
  obtain ⟨M, hM⟩ := hqbdd
  have hHessG_int : Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z) volume := by
    have heq : (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z)
        = fun z => (4 * t ^ 2)⁻¹ * ((z i) ^ 2 * gaussDdim t z)
            - (4 * t ^ 2)⁻¹ * (2 * t) * gaussDdim t z := by
      funext z; rw [div_eq_mul_inv]; ring
    rw [heq]
    exact ((coordSq_gaussDdim_integrable t ht i).const_mul _).sub
      ((gaussDdim_integrable' t ht).const_mul _)
  have hHessGq_int : Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z) volume :=
    hHessG_int.mul_bdd hqmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hM z))
  have hHessGq0_int : Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q 0) volume :=
    hHessG_int.mul_const (q 0)
  have hred : (∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z)
      = ∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0) := by
    have hsub : (∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0))
        = (∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z)
          - ∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q 0 := by
      rw [← integral_sub hHessGq_int hHessGq0_int]
      refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
    rw [hsub, integral_mul_const, gaussian_hessian_moment_zero t ht i, zero_mul, sub_zero]
  have hbound_pt : ∀ z : Point n,
      ‖((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖
        ≤ ∑ k, L * (|(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' t z)]
    have hdist : |q z - q 0| ≤ L * ∑ k, |z k| := by
      refine (hq z 0).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_pi_le_iff (Finset.sum_nonneg (fun k _ => abs_nonneg _))]
      intro j
      rw [Real.dist_eq]
      simp only [Pi.zero_apply, sub_zero]
      exact Finset.single_le_sum (f := fun k => |z k|) (fun k _ => abs_nonneg (z k))
        (Finset.mem_univ j)
    calc |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |q z - q 0|
        ≤ |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * (L * ∑ k, |z k|) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg' t z))
      _ = ∑ k, L * (|(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
  have hB_int : Integrable
      (fun z : Point n => ∑ k, L * (|(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|))
      volume :=
    integrable_finsetSum _ (fun k _ => (hessAbs_coord_gaussDdim_integrable t ht i k).const_mul L)
  rw [hred]
  calc |∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)|
      = ‖∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Point n, ‖((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * (q z - q 0)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z : Point n, ∑ k, L * (|(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k|) :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hB_int
          (ae_of_all _ hbound_pt)
    _ = ∑ k, L * ∫ z : Point n, |(z i ^ 2 - 2 * t) / (4 * t ^ 2)| * gaussDdim t z * |z k| := by
        rw [integral_finsetSum _
          (fun k _ => (hessAbs_coord_gaussDdim_integrable t ht i k).const_mul L)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [integral_const_mul]
    _ ≤ ∑ _k : Fin n, L * (15 / 2 / Real.sqrt t) :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hk_coord_integral_le t ht i k) hL)
    _ = L * (15 / 2 * n) / Real.sqrt t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussian_hessian_moment_zero
#print axioms QIQTH.HeatResidualBound.hk_absHess_absY_moment_le
#print axioms QIQTH.HeatResidualBound.hk_coord_integral_le
#print axioms QIQTH.HeatResidualBound.gaussian_hessian_cancel
