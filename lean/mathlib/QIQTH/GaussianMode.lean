/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-3-C2 — the concrete calibrated reference profile (Gaussian wave packet)

`LocalizedMode.localized_mode_hTkk` reduced the per-generator `hTkk` to one universal mode-calibration
constant: a profile `g₀` with `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`.  This file EXHIBITS such a `g₀` — the Gaussian
wave packet `g₀(θ) = C·exp(−θ²/2 − iθ)` with `C = (ℏ√π)^{−1/2}` — and proves the calibration, closing the last
analytic input of the localization map (`hcal`).

Only the IMAGINARY part of the boost-charge integral enters the calibration, and `Im(∫f) = ∫ Im(f)` discards
the real part (a total derivative), so the computation needs only the Gaussian normalization `∫e^{−θ²} = √π` —
no odd moment.  Axiom-free.
-/
import QIQTH.LocalizedMode

namespace QIQTH.WedgeKMSToGR

open Complex MeasureTheory Real

/-- Normalization constant `C = (ℏ√π)^{−1/2}` of the Gaussian reference profile. -/
noncomputable def gaussC (hbar : ℝ) : ℝ := (Real.sqrt (hbar * Real.sqrt Real.pi))⁻¹

/-- The Gaussian wave-packet reference profile `g₀(θ) = C·exp(−θ²/2 − iθ)`. -/
noncomputable def gaussMode (hbar : ℝ) (θ : ℝ) : ℂ :=
  (gaussC hbar : ℂ) * Complex.exp (((-θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I)

/-- Its derivative profile `g₀'(θ) = g₀(θ)·(−θ − i)`. -/
noncomputable def gaussMode' (hbar : ℝ) (θ : ℝ) : ℂ :=
  gaussMode hbar θ * (-(θ : ℂ) - Complex.I)

/-- `C²·√π = 1/ℏ` for `ℏ > 0` — the calibration arithmetic. -/
theorem gaussC_sq_mul_sqrt (hbar : ℝ) (hb : 0 < hbar) :
    gaussC hbar ^ 2 * Real.sqrt Real.pi = 1 / hbar := by
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hbπ : 0 < hbar * Real.sqrt Real.pi := mul_pos hb hsπ
  unfold gaussC
  rw [inv_pow, Real.sq_sqrt hbπ.le]
  field_simp

/-- `normSq(g₀ θ) = C²·e^{−θ²}` — the Gaussian envelope. -/
theorem gaussMode_normSq (hbar : ℝ) (θ : ℝ) :
    Complex.normSq (gaussMode hbar θ) = gaussC hbar ^ 2 * Real.exp (-θ ^ 2) := by
  have hexp : Real.exp (-θ ^ 2 / 2) ^ 2 = Real.exp (-θ ^ 2) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hwre : (((-θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I).re = -θ ^ 2 / 2 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  unfold gaussMode
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp, hwre, hexp]
  ring

/-- The pointwise boost-charge density: `conj(g₀ θ)·g₀'(θ) = ↑(C²·e^{−θ²})·(−θ − i)`. -/
theorem gaussMode_conj_mul (hbar : ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ
      = ((gaussC hbar ^ 2 * Real.exp (-θ ^ 2) : ℝ) : ℂ) * (-(θ : ℂ) - Complex.I) := by
  unfold gaussMode'
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (gaussMode hbar θ)) (gaussMode hbar θ),
    Complex.mul_conj, gaussMode_normSq]

/-- The boost-charge integrand is integrable (Gaussian × polynomial). -/
theorem gaussMode_integrable (hbar : ℝ) :
    Integrable (fun θ => (starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ)
      (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => Real.exp (-θ ^ 2)) volume := by
    have := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    simpa [one_mul] using this
  have hxg : Integrable (fun θ : ℝ => θ * Real.exp (-θ ^ 2)) volume := by
    have := integrable_mul_exp_neg_mul_sq (b := 1) (by norm_num)
    simpa [one_mul] using this
  have hint : Integrable
      (fun θ => ((gaussC hbar ^ 2 * Real.exp (-θ ^ 2) : ℝ) : ℂ) * (-(θ : ℂ) - Complex.I)) volume := by
    have h1 : Integrable
        (fun θ : ℝ => (((-(gaussC hbar ^ 2 * (θ * Real.exp (-θ ^ 2)))) : ℝ) : ℂ)) volume :=
      Integrable.ofReal ((hxg.const_mul (gaussC hbar ^ 2)).neg)
    have h2 : Integrable
        (fun θ : ℝ => (((gaussC hbar ^ 2 * Real.exp (-θ ^ 2)) : ℝ) : ℂ) * (-Complex.I)) volume :=
      (Integrable.ofReal (hg.const_mul (gaussC hbar ^ 2))).mul_const _
    refine (h1.add h2).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.add_apply, Complex.ofReal_neg, Complex.ofReal_mul]; ring
  exact hint.congr (Filter.Eventually.of_forall (fun θ => (gaussMode_conj_mul hbar θ).symm))

/-- **★ The Gaussian profile satisfies the calibration** `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`.  Combined with
    `localized_mode_hTkk`, the per-generator `hTkk` is fully discharged for the canonical Gaussian
    localization. -/
theorem gaussMode_calibration (hbar : ℝ) (hb : 0 < hbar) :
    (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ
        ∂(volume : Measure ℝ))).im = 2 * Real.pi / hbar := by
  -- only the imaginary part survives: Im(∫f) = ∫ Im(f), and Im of the density is −C²e^{−θ²}.
  have himInt : (∫ θ, (starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ ∂(volume : Measure ℝ)).im
      = ∫ θ, ((starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ).im ∂(volume : Measure ℝ) :=
    (Complex.imCLM.integral_comp_comm (gaussMode_integrable hbar)).symm
  have hdens : ∀ θ : ℝ, ((starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ).im
      = -(gaussC hbar ^ 2 * Real.exp (-θ ^ 2)) := by
    intro θ
    rw [gaussMode_conj_mul]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.neg_im, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.I_re]
    ring
  have hgauss : (∫ θ : ℝ, Real.exp (-θ ^ 2)) = Real.sqrt Real.pi := by
    have := integral_gaussian 1
    simpa [one_mul] using this
  have hintval : (∫ θ, ((starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ).im
      ∂(volume : Measure ℝ)) = -(gaussC hbar ^ 2 * Real.sqrt Real.pi) := by
    simp only [hdens]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, hgauss]
  have hpiim : ∀ z : ℂ, (-(2 * Real.pi * z)).im = -(2 * Real.pi * z.im) := by
    intro z
    simp only [Complex.neg_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hpiim, himInt, hintval, gaussC_sq_mul_sqrt hbar hb]
  ring

/-! ### Regularity of the Gaussian mode (for the capstone's `ff` requirements). -/

theorem gaussC_pos (hbar : ℝ) (hb : 0 < hbar) : 0 < gaussC hbar :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/-- `‖g₀(θ)‖ = C·e^{−θ²/2}` (from `normSq = C²e^{−θ²}`). -/
theorem gaussMode_norm (hbar : ℝ) (hb : 0 < hbar) (θ : ℝ) :
    ‖gaussMode hbar θ‖ = gaussC hbar * Real.exp (-θ ^ 2 / 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussMode hbar θ)), ← Complex.normSq_eq_norm_sq, gaussMode_normSq,
    show gaussC hbar ^ 2 * Real.exp (-θ ^ 2) = (gaussC hbar * Real.exp (-θ ^ 2 / 2)) ^ 2 by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring]
  exact Real.sqrt_sq (mul_nonneg (gaussC_pos hbar hb).le (Real.exp_pos _).le)

theorem gaussMode_continuous (hbar : ℝ) : Continuous (gaussMode hbar) := by
  unfold gaussMode; fun_prop

theorem gaussMode_hasDerivAt (hbar : ℝ) (θ : ℝ) :
    HasDerivAt (gaussMode hbar) (gaussMode' hbar θ) θ := by
  have hpoly : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-θ) θ := by
    have h := (hasDerivAt_pow 2 θ).const_mul (-1 / 2 : ℝ)
    convert h using 1
    · funext y; ring
    · push_cast; ring
  have h1 : HasDerivAt (fun y : ℝ => ((-y ^ 2 / 2 : ℝ) : ℂ)) ((-θ : ℝ) : ℂ) θ := hpoly.ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I θ := by
    have := ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
    simpa using this
  have hu : HasDerivAt (fun y : ℝ => ((-y ^ 2 / 2 : ℝ) : ℂ) - (y : ℂ) * Complex.I)
      (-(θ : ℂ) - Complex.I) θ := by
    have := h1.sub h2; simpa using this
  have hcexp := (hu.cexp).const_mul (gaussC hbar : ℂ)
  have heq : gaussMode' hbar θ
      = (gaussC hbar : ℂ) * (Complex.exp (((-θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I)
          * (-(θ : ℂ) - Complex.I)) := by
    unfold gaussMode' gaussMode; ring
  rw [heq]; exact hcexp

theorem gaussMode'_continuous (hbar : ℝ) : Continuous (gaussMode' hbar) := by
  unfold gaussMode'; exact (gaussMode_continuous hbar).mul (by fun_prop)

/-- `‖g₀'(θ)‖ ≤ C`, via `1 + θ² ≤ e^{θ²}` so `e^{−θ²/2}√(θ²+1) ≤ 1`. -/
theorem gaussMode'_norm_le (hbar : ℝ) (hb : 0 < hbar) (θ : ℝ) :
    ‖gaussMode' hbar θ‖ ≤ gaussC hbar := by
  unfold gaussMode'
  rw [norm_mul, gaussMode_norm hbar hb]
  have hnI : ‖-(θ : ℂ) - Complex.I‖ = Real.sqrt (θ ^ 2 + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg (-(θ : ℂ) - Complex.I)), ← Complex.normSq_eq_norm_sq]
    congr 1
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnI]
  have hb1 : Real.sqrt (θ ^ 2 + 1) ≤ Real.exp (θ ^ 2 / 2) := by
    have h2 : Real.exp (θ ^ 2 / 2) ^ 2 = Real.exp (θ ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← Real.sqrt_sq (Real.exp_pos (θ ^ 2 / 2)).le, h2]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp (θ ^ 2)])
  calc gaussC hbar * Real.exp (-θ ^ 2 / 2) * Real.sqrt (θ ^ 2 + 1)
      ≤ gaussC hbar * Real.exp (-θ ^ 2 / 2) * Real.exp (θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hb1 (mul_nonneg (gaussC_pos hbar hb).le (Real.exp_pos _).le)
    _ = gaussC hbar := by
        rw [mul_assoc, ← Real.exp_add, show -θ ^ 2 / 2 + θ ^ 2 / 2 = 0 by ring, Real.exp_zero,
          mul_one]

theorem gaussMode_sq_integrable (hbar : ℝ) :
    Integrable (fun θ => ‖gaussMode hbar θ‖ ^ 2) (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => gaussC hbar ^ 2 * Real.exp (-θ ^ 2)) volume := by
    have := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
    refine (this.const_mul (gaussC hbar ^ 2)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp
  refine hg.congr (Filter.Eventually.of_forall (fun θ => ?_))
  show gaussC hbar ^ 2 * Real.exp (-θ ^ 2) = ‖gaussMode hbar θ‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, gaussMode_normSq]

theorem gaussMode_memLp (hbar : ℝ) : MemLp (gaussMode hbar) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq_norm (gaussMode_continuous hbar).aestronglyMeasurable).mpr
    (gaussMode_sq_integrable hbar)

theorem gaussMode_integrable_fn (hbar : ℝ) (hb : 0 < hbar) :
    Integrable (gaussMode hbar) (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => gaussC hbar * Real.exp (-θ ^ 2 / 2)) volume := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine (this.const_mul (gaussC hbar)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    show gaussC hbar * Real.exp (-(1 / 2) * θ ^ 2) = gaussC hbar * Real.exp (-θ ^ 2 / 2)
    rw [show -(1 / 2 : ℝ) * θ ^ 2 = -θ ^ 2 / 2 by ring]
  exact Integrable.mono' hg (gaussMode_continuous hbar).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ => le_of_eq (gaussMode_norm hbar hb θ)))

end QIQTH.WedgeKMSToGR
