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

/-- The pointwise boost-charge density: `conj(g₀ θ)·g₀'(θ) = ↑(C²·e^{−θ²})·(−θ − i)`. -/
theorem gaussMode_conj_mul (hbar : ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (gaussMode hbar θ) * gaussMode' hbar θ
      = ((gaussC hbar ^ 2 * Real.exp (-θ ^ 2) : ℝ) : ℂ) * (-(θ : ℂ) - Complex.I) := by
  have hexp : Real.exp (-θ ^ 2 / 2) ^ 2 = Real.exp (-θ ^ 2) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hwre : (((-θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I).re = -θ ^ 2 / 2 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hns : Complex.normSq (gaussMode hbar θ) = gaussC hbar ^ 2 * Real.exp (-θ ^ 2) := by
    unfold gaussMode
    rw [Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp, hwre, hexp]
    ring
  unfold gaussMode'
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (gaussMode hbar θ)) (gaussMode hbar θ),
    Complex.mul_conj, hns]

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

end QIQTH.WedgeKMSToGR
