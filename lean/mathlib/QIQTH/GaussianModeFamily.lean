/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# GR scaffolding C — the width-parametrized Gaussian localization family

`GaussianMode.lean` exhibits ONE calibrated reference profile `g₀(θ) = C·exp(−θ²/2 − iθ)` discharging the
per-generator `hTkk` (`(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`).  This file shows the localization discharge is NOT
specific to that single Gaussian: a **one-parameter family** `gaussModeA hbar a θ = C(a)·exp(−a θ²/2 − iθ)`
(`a > 0`, unit phase, width `a`) hits the **same** calibration `2π/ℏ` for **every** width `a`, with
`C(a) = (ℏ·√(π/a))^{−1/2}`.  The `a=1` specialization recovers `GaussianMode`.

Only the IMAGINARY part of the boost-charge integral enters, and `Im(∫f) = ∫ Im(f)` discards the real
(total-derivative) part, so the computation needs only the width-`a` Gaussian normalization
`∫e^{−a θ²} = √(π/a)` (`integral_gaussian a`) — no new hard integral relative to the `a=1` case.

Stage C1 (this file): defs + `gaussCA_sq_mul_sqrt` + `gaussModeA_normSq` + `gaussModeA_conj_mul`.
Stages C2 (calibration ∀ a) and C3 (regularity block) follow.  Axiom-free.
-/
import QIQTH.GaussianMode

namespace QIQTH.WedgeKMSToGR

open Complex MeasureTheory Real

/-- Width-`a` normalization constant `C(a) = (ℏ·√(π/a))^{−1/2}`. -/
noncomputable def gaussCA (hbar a : ℝ) : ℝ := (Real.sqrt (hbar * Real.sqrt (Real.pi / a)))⁻¹

/-- The width-`a` Gaussian reference profile `g(θ) = C(a)·exp(−a θ²/2 − iθ)` (unit phase). -/
noncomputable def gaussModeA (hbar a : ℝ) (θ : ℝ) : ℂ :=
  (gaussCA hbar a : ℂ) * Complex.exp (((-a * θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I)

/-- Its derivative profile `g'(θ) = g(θ)·(−a θ − i)`. -/
noncomputable def gaussModeA' (hbar a : ℝ) (θ : ℝ) : ℂ :=
  gaussModeA hbar a θ * (-(a : ℂ) * (θ : ℂ) - Complex.I)

/-- `C(a)²·√(π/a) = 1/ℏ` — the width-`a` calibration arithmetic (so the family always calibrates to `2π/ℏ`). -/
theorem gaussCA_sq_mul_sqrt (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) :
    gaussCA hbar a ^ 2 * Real.sqrt (Real.pi / a) = 1 / hbar := by
  have hsπ : 0 < Real.sqrt (Real.pi / a) := Real.sqrt_pos.mpr (by positivity)
  have hbπ : 0 < hbar * Real.sqrt (Real.pi / a) := mul_pos hb hsπ
  unfold gaussCA
  rw [inv_pow, Real.sq_sqrt hbπ.le]
  field_simp

/-- `normSq(g(θ)) = C(a)²·e^{−a θ²}` — the width-`a` Gaussian envelope. -/
theorem gaussModeA_normSq (hbar a : ℝ) (θ : ℝ) :
    Complex.normSq (gaussModeA hbar a θ) = gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) := by
  have hexp : Real.exp (-a * θ ^ 2 / 2) ^ 2 = Real.exp (-a * θ ^ 2) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hwre : (((-a * θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I).re = -a * θ ^ 2 / 2 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  unfold gaussModeA
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp, hwre, hexp]
  ring

/-- The pointwise boost-charge density: `conj(g θ)·g'(θ) = ↑(C(a)²·e^{−a θ²})·(−a θ − i)`. -/
theorem gaussModeA_conj_mul (hbar a : ℝ) (θ : ℝ) :
    (starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ
      = ((gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) : ℝ) : ℂ) * (-(a : ℂ) * (θ : ℂ) - Complex.I) := by
  unfold gaussModeA'
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (gaussModeA hbar a θ)) (gaussModeA hbar a θ),
    Complex.mul_conj, gaussModeA_normSq]

/-- The width-`a` boost-charge integrand is integrable (Gaussian × polynomial). -/
theorem gaussModeA_integrable (hbar a : ℝ) (ha : 0 < a) :
    Integrable (fun θ => (starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ)
      (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => Real.exp (-a * θ ^ 2)) volume :=
    integrable_exp_neg_mul_sq ha
  have hxg : Integrable (fun θ : ℝ => θ * Real.exp (-a * θ ^ 2)) volume :=
    integrable_mul_exp_neg_mul_sq ha
  have hint : Integrable
      (fun θ => ((gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) : ℝ) : ℂ)
        * (-(a : ℂ) * (θ : ℂ) - Complex.I)) volume := by
    have h1 : Integrable
        (fun θ : ℝ => (((-(gaussCA hbar a ^ 2 * a * (θ * Real.exp (-a * θ ^ 2)))) : ℝ) : ℂ)) volume :=
      Integrable.ofReal ((hxg.const_mul (gaussCA hbar a ^ 2 * a)).neg)
    have h2 : Integrable
        (fun θ : ℝ => (((gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2)) : ℝ) : ℂ) * (-Complex.I)) volume :=
      (Integrable.ofReal (hg.const_mul (gaussCA hbar a ^ 2))).mul_const _
    refine (h1.add h2).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.add_apply, Complex.ofReal_neg, Complex.ofReal_mul]; push_cast; ring
  exact hint.congr (Filter.Eventually.of_forall (fun θ => (gaussModeA_conj_mul hbar a θ).symm))

/-- **★ Stage C2 — the whole width family satisfies the SAME calibration** `(−2π ∫ conj·').im = 2π/ℏ` for
    every width `a > 0`.  Only the imaginary part survives (`Im(∫f)=∫Im(f)`); the width `a` enters the real
    (total-derivative) part only, so the imaginary density is `−C(a)²e^{−a θ²}` and the integral is
    `−C(a)²√(π/a) = −1/ℏ` (`gaussCA_sq_mul_sqrt`).  So the localization discharge of `hTkk` is not specific
    to the single Gaussian — a one-parameter family of modes works. -/
theorem gaussModeA_calibration (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) :
    (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ
        ∂(volume : Measure ℝ))).im = 2 * Real.pi / hbar := by
  have himInt : (∫ θ, (starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ
        ∂(volume : Measure ℝ)).im
      = ∫ θ, ((starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ).im
        ∂(volume : Measure ℝ) :=
    (Complex.imCLM.integral_comp_comm (gaussModeA_integrable hbar a ha)).symm
  have hdens : ∀ θ : ℝ, ((starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ).im
      = -(gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2)) := by
    intro θ
    rw [gaussModeA_conj_mul]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.neg_im, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.I_re]
    ring
  have hgauss : (∫ θ : ℝ, Real.exp (-a * θ ^ 2)) = Real.sqrt (Real.pi / a) := integral_gaussian a
  have hintval : (∫ θ, ((starRingEnd ℂ) (gaussModeA hbar a θ) * gaussModeA' hbar a θ).im
      ∂(volume : Measure ℝ)) = -(gaussCA hbar a ^ 2 * Real.sqrt (Real.pi / a)) := by
    simp only [hdens]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, hgauss]
  have hpiim : ∀ z : ℂ, (-(2 * Real.pi * z)).im = -(2 * Real.pi * z.im) := by
    intro z
    simp only [Complex.neg_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hpiim, himInt, hintval, gaussCA_sq_mul_sqrt hbar a hb ha]
  ring

end QIQTH.WedgeKMSToGR
