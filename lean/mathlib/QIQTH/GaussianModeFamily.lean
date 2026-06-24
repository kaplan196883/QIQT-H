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

/-! ### Stage C3 — regularity of the width-`a` mode (the capstone's `ff`-block requirements). -/

theorem gaussCA_pos (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) : 0 < gaussCA hbar a :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hb (Real.sqrt_pos.mpr (by positivity))))

/-- `‖g(θ)‖ = C(a)·e^{−a θ²/2}` (from `normSq = C(a)²e^{−a θ²}`). -/
theorem gaussModeA_norm (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) (θ : ℝ) :
    ‖gaussModeA hbar a θ‖ = gaussCA hbar a * Real.exp (-a * θ ^ 2 / 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (gaussModeA hbar a θ)), ← Complex.normSq_eq_norm_sq, gaussModeA_normSq,
    show gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2)
        = (gaussCA hbar a * Real.exp (-a * θ ^ 2 / 2)) ^ 2 by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring]
  exact Real.sqrt_sq (mul_nonneg (gaussCA_pos hbar a hb ha).le (Real.exp_pos _).le)

theorem gaussModeA_continuous (hbar a : ℝ) : Continuous (gaussModeA hbar a) := by
  unfold gaussModeA; fun_prop

theorem gaussModeA_hasDerivAt (hbar a : ℝ) (θ : ℝ) :
    HasDerivAt (gaussModeA hbar a) (gaussModeA' hbar a θ) θ := by
  have hpoly : HasDerivAt (fun y : ℝ => -a * y ^ 2 / 2) (-a * θ) θ := by
    have h := (hasDerivAt_pow 2 θ).const_mul (-a / 2 : ℝ)
    convert h using 1
    · funext y; ring
    · push_cast; ring
  have h1 : HasDerivAt (fun y : ℝ => ((-a * y ^ 2 / 2 : ℝ) : ℂ)) ((-a * θ : ℝ) : ℂ) θ :=
    hpoly.ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I θ := by
    have := ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
    simpa using this
  have hu : HasDerivAt (fun y : ℝ => ((-a * y ^ 2 / 2 : ℝ) : ℂ) - (y : ℂ) * Complex.I)
      (-(a : ℂ) * (θ : ℂ) - Complex.I) θ := by
    have hsub := h1.sub h2
    have hcast : (((-a * θ : ℝ) : ℂ)) - Complex.I = -(a : ℂ) * (θ : ℂ) - Complex.I := by
      push_cast; ring
    rwa [hcast] at hsub
  have hcexp := (hu.cexp).const_mul (gaussCA hbar a : ℂ)
  have heq : gaussModeA' hbar a θ
      = (gaussCA hbar a : ℂ) * (Complex.exp (((-a * θ ^ 2 / 2 : ℝ) : ℂ) - (θ : ℂ) * Complex.I)
          * (-(a : ℂ) * (θ : ℂ) - Complex.I)) := by
    unfold gaussModeA' gaussModeA; ring
  rw [heq]; exact hcexp

theorem gaussModeA'_continuous (hbar a : ℝ) : Continuous (gaussModeA' hbar a) := by
  unfold gaussModeA'; exact (gaussModeA_continuous hbar a).mul (by fun_prop)

/-- `‖g'(θ)‖ ≤ C(a)·√(a+1)` — a clean uniform bound for the width-`a` mode, via `u·e^{−u} ≤ 1`
    (`u = a θ²`) so `e^{−a θ²}(a²θ²+1) ≤ a+1`. -/
theorem gaussModeA'_norm_le (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) (θ : ℝ) :
    ‖gaussModeA' hbar a θ‖ ≤ gaussCA hbar a * Real.sqrt (a + 1) := by
  have hns : ‖gaussModeA' hbar a θ‖ ^ 2
      = gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) * (a ^ 2 * θ ^ 2 + 1) := by
    rw [← Complex.normSq_eq_norm_sq]
    unfold gaussModeA'
    rw [Complex.normSq_mul, gaussModeA_normSq]
    congr 1
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hbound : Real.exp (-a * θ ^ 2) * (a ^ 2 * θ ^ 2 + 1) ≤ a + 1 := by
    have hexp_pos : (0 : ℝ) < Real.exp (a * θ ^ 2) := Real.exp_pos _
    have hule : a * θ ^ 2 ≤ Real.exp (a * θ ^ 2) := by linarith [Real.add_one_le_exp (a * θ ^ 2)]
    have huexp : a * θ ^ 2 * Real.exp (-(a * θ ^ 2)) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hexp_pos]; exact hule
    have hexp1 : Real.exp (-(a * θ ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have h4 : a * (a * θ ^ 2 * Real.exp (-(a * θ ^ 2))) ≤ a * 1 :=
      mul_le_mul_of_nonneg_left huexp ha.le
    have hcongr : Real.exp (-a * θ ^ 2) = Real.exp (-(a * θ ^ 2)) := by rw [neg_mul]
    rw [hcongr]; nlinarith [h4, hexp1]
  have hCsq : (0 : ℝ) ≤ gaussCA hbar a ^ 2 := sq_nonneg _
  have hsq : ‖gaussModeA' hbar a θ‖ ^ 2 ≤ (gaussCA hbar a * Real.sqrt (a + 1)) ^ 2 := by
    rw [hns, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ a + 1)]
    calc gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) * (a ^ 2 * θ ^ 2 + 1)
        = gaussCA hbar a ^ 2 * (Real.exp (-a * θ ^ 2) * (a ^ 2 * θ ^ 2 + 1)) := by ring
      _ ≤ gaussCA hbar a ^ 2 * (a + 1) := mul_le_mul_of_nonneg_left hbound hCsq
  have hB0 : (0 : ℝ) ≤ gaussCA hbar a * Real.sqrt (a + 1) :=
    mul_nonneg (gaussCA_pos hbar a hb ha).le (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (norm_nonneg (gaussModeA' hbar a θ))]
  calc Real.sqrt (‖gaussModeA' hbar a θ‖ ^ 2)
      ≤ Real.sqrt ((gaussCA hbar a * Real.sqrt (a + 1)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = gaussCA hbar a * Real.sqrt (a + 1) := Real.sqrt_sq hB0

theorem gaussModeA_sq_integrable (hbar a : ℝ) (ha : 0 < a) :
    Integrable (fun θ => ‖gaussModeA hbar a θ‖ ^ 2) (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2)) volume :=
    (integrable_exp_neg_mul_sq ha).const_mul (gaussCA hbar a ^ 2)
  refine hg.congr (Filter.Eventually.of_forall (fun θ => ?_))
  show gaussCA hbar a ^ 2 * Real.exp (-a * θ ^ 2) = ‖gaussModeA hbar a θ‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, gaussModeA_normSq]

theorem gaussModeA_memLp (hbar a : ℝ) (ha : 0 < a) :
    MemLp (gaussModeA hbar a) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq_norm (gaussModeA_continuous hbar a).aestronglyMeasurable).mpr
    (gaussModeA_sq_integrable hbar a ha)

theorem gaussModeA_integrable_fn (hbar a : ℝ) (hb : 0 < hbar) (ha : 0 < a) :
    Integrable (gaussModeA hbar a) (volume : Measure ℝ) := by
  have hg : Integrable (fun θ : ℝ => gaussCA hbar a * Real.exp (-a * θ ^ 2 / 2)) volume := by
    have h := (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < a / 2)).const_mul (gaussCA hbar a)
    refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
    have hθ : -(a / 2) * θ ^ 2 = -a * θ ^ 2 / 2 := by ring
    simp only [hθ]
  exact Integrable.mono' hg (gaussModeA_continuous hbar a).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ => le_of_eq (gaussModeA_norm hbar a hb ha θ)))

end QIQTH.WedgeKMSToGR
