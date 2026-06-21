import QIQTH.Fock.StressTensor.HorizonFourier
import QIQTH.Fock.SchwartzDecay
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Free-field stress tensor (Route B) — Phase 3b-ii: the Fourier-convention bridge

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 3b-ii.  Phase 3b-i wrote `horizonFieldDeriv` (= `∂_λ φ_H`) as a
"physicists'" Fourier integral `∫ g(x) e^{−iλx} dx`.  To use Mathlib's Fourier API (in particular the weak
sesquilinear Parseval identity) we must identify that with Mathlib's `𝓕` (`Real.fourierIntegral`), whose
convention carries the `2π` in the exponent.  This file proves the purely mechanical bridge

`𝓕 g (λ / 2π) = ∫ x, g x · e^{−iλx}`,

i.e. the physicists' transform at frequency `λ` is Mathlib's `𝓕` at frequency `λ/(2π)`.  No analytic
hypotheses.  Axiom-free.  (The remaining 3b-ii steps — the `ψ_H = 𝓕[B]` partner via IBP, the sesquilinear
pairing, and the change of variables back to `θ` giving `−2π·rapidityMomentum` — follow.)
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory Real
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle
open scoped FourierTransform

/-- **The Fourier-convention bridge.**  The physicists' Fourier integral `∫ g(x) e^{−iλx} dx` is Mathlib's
    `𝓕 g` evaluated at the rescaled frequency `λ / (2π)`.  Purely the `2π`-in-the-exponent convention; no
    integrability or smoothness needed. -/
theorem fourierIntegral_exp_bridge (g : ℝ → ℂ) (lam : ℝ) :
    𝓕 g (lam / (2 * Real.pi)) = ∫ x, g x * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ)) := by
  rw [fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have he : Complex.exp (↑(-2 * Real.pi * x * (lam / (2 * Real.pi))) * Complex.I)
      = Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ)) := by
    congr 1
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [show (-2 * Real.pi * x * (lam / (2 * Real.pi))) = -(x * lam) from by field_simp]
    push_cast; ring
  show Complex.exp (↑(-2 * Real.pi * x * (lam / (2 * Real.pi))) * Complex.I) • g x
      = g x * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ))
  rw [he, smul_eq_mul, mul_comm]

/-- The **horizon amplitude** `A(x) = −i·Krep m f (rapInv m x)` on `(0,∞)`, extended by `0` to all of `ℝ` —
    the `k`-line function whose Mathlib Fourier transform is `χ_H = ∂_λ φ_H`. -/
noncomputable def horizonAmp (m : ℝ) (f : V → ℂ) : ℝ → ℂ :=
  Set.indicator (Set.Ioi 0) (fun x => -Complex.I * Krep m f (rapInv m x))

/-- **The pointwise Cauchy envelope of the horizon amplitude.**  For `f` Schwartz and `m > 0`,
    `‖horizonAmp m f x‖ ≤ 4Cc²·(c²+x²)⁻¹` with `c = m/√2` and `C` the `(cosh)⁻²` decay constant
    (`schwartz_Krep_decay_sq`); on `x > 0` via `cosh(rapInv x) = (c²+x²)/(2cx)` and `x² ≤ c²+x²`, on `x ≤ 0`
    the amplitude vanishes.  The single bound feeding both `L¹` and `L²` integrability of `horizonAmp`. -/
theorem horizonAmp_norm_le {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) (x : ℝ) :
    ‖horizonAmp m (⇑f) x‖
      ≤ 4 * (16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
          + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2))
        * (m / Real.sqrt 2) ^ 2 * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹ := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set C : ℝ := 16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2) with hCdef
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  simp only [horizonAmp, Set.indicator_apply]
  split_ifs with hx
  · rw [Set.mem_Ioi] at hx
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hcosh_eq : Real.cosh (rapInv m x) = (c ^ 2 + x ^ 2) / (2 * c * x) := by
      rw [rapInv, ← hc, ← Real.log_div hcpos.ne' hx.ne', Real.cosh_log (by positivity)]
      field_simp
    have hdecay := schwartz_Krep_decay_sq f hm.ne' (rapInv m x)
    rw [hcosh_eq, ← hCdef] at hdecay
    refine le_trans hdecay ?_
    rw [div_pow, inv_div, ← mul_div_assoc, div_le_iff₀ (by positivity),
      show 4 * C * c ^ 2 * (c ^ 2 + x ^ 2)⁻¹ * (c ^ 2 + x ^ 2) ^ 2
        = 4 * C * c ^ 2 * (c ^ 2 + x ^ 2) by field_simp]
    have hkey : (0 : ℝ) ≤ 4 * C * c ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)
    nlinarith [hkey]
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)) (by positivity)

/-- **★ The horizon amplitude is `L¹`** for a Schwartz test function `f` (`m > 0`).  The `(cosh)⁻²` Schwartz
    decay (`schwartz_Krep_decay_sq`) plus the explicit boundary map `cosh(rapInv x) = (c²+x²)/(2cx)`
    (`c = m/√2`) dominate `‖horizonAmp m f x‖ ≤ 4Cc²·(c²+x²)⁻¹` by the integrable Cauchy kernel
    (`integrable_inv_const_sq_add`).  This is the integrability half of the softer Route-B regularity. -/
theorem horizonAmp_integrable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Integrable (horizonAmp m (⇑f)) := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set C : ℝ := 16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2) with hCdef
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hRHSnn : ∀ x : ℝ, (0 : ℝ) ≤ 4 * C * c ^ 2 * (c ^ 2 + x ^ 2)⁻¹ := fun x =>
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)) (by positivity)
  have hrap_meas : Measurable (rapInv m) := by
    unfold rapInv; exact measurable_const.sub Real.measurable_log
  have hg_meas : Measurable (fun x : ℝ => -Complex.I * Krep m (⇑f) (rapInv m x)) :=
    (((Krep_continuous f.integrable).measurable.comp hrap_meas).const_mul _)
  refine ((integrable_inv_const_sq_add hcpos).const_mul (4 * C * c ^ 2)).mono'
    (hg_meas.aestronglyMeasurable.indicator measurableSet_Ioi) ?_
  filter_upwards with x
  simp only [horizonAmp, Set.indicator_apply]
  split_ifs with hx
  · rw [Set.mem_Ioi] at hx
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hcosh_eq : Real.cosh (rapInv m x) = (c ^ 2 + x ^ 2) / (2 * c * x) := by
      rw [rapInv, ← hc, ← Real.log_div hcpos.ne' hx.ne', Real.cosh_log (by positivity)]
      field_simp
    have hdecay := schwartz_Krep_decay_sq f hm.ne' (rapInv m x)
    rw [hcosh_eq, ← hCdef] at hdecay
    refine le_trans hdecay ?_
    rw [div_pow, inv_div, ← mul_div_assoc, div_le_iff₀ (by positivity),
      show 4 * C * c ^ 2 * (c ^ 2 + x ^ 2)⁻¹ * (c ^ 2 + x ^ 2) ^ 2
        = 4 * C * c ^ 2 * (c ^ 2 + x ^ 2) by field_simp]
    have hkey : (0 : ℝ) ≤ 4 * C * c ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)
    nlinarith [hkey]
  · rw [norm_zero]; exact hRHSnn x

/-- **★ `∂_λ φ_H` IS a Mathlib Fourier transform.**  Consolidating Phase 3b-i (`horizonFieldDeriv_eq_kIntegral`)
    with the convention bridge: `horizonFieldDeriv m f λ = 𝓕 (horizonAmp m f) (λ / 2π)`.  This makes the weak
    sesquilinear Parseval identity directly applicable to `χ_H`. -/
theorem horizonFieldDeriv_eq_fourier (m : ℝ) (hm : 0 < m) (f : V → ℂ) (lam : ℝ) :
    horizonFieldDeriv m f lam = 𝓕 (horizonAmp m f) (lam / (2 * Real.pi)) := by
  rw [fourierIntegral_exp_bridge, horizonFieldDeriv_eq_kIntegral m hm f lam,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show (Set.Ioi (0 : ℝ)).indicator
      (fun x => (-Complex.I * Krep m f (rapInv m x)) * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ))) x
    = horizonAmp m f x * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ))
  unfold horizonAmp
  by_cases hx : x ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- **★ Self-adjointness of `−i∂_θ`: the rapidity-momentum integral is purely imaginary.**
    For a smooth, decaying amplitude `f` (the boundary terms vanish), `∫ conj(f)·f' = i·rapidityMomentum f f'`
    — equivalently `Re ∫ conj(f)·f' = 0`.  This is the Hermiticity of the momentum operator; it is what turns
    the Parseval output (`∫ conj(A)·B = i·∫ conj(K)·K'`) into the real `−2π·rapidityMomentum` at the end of
    Phase 3b-ii.  Proof: `∫ conj(f)f' + conj(∫ conj(f)f') = ∫ d/dθ|f|² = 0` (full-line FTC). -/
theorem inner_deriv_eq_I_mul_rapidityMomentum (f f' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (f' θ) * f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f' θ)) :
    ∫ θ, (starRingEnd ℂ) (f θ) * f' θ = Complex.I * (rapidityMomentum f f' : ℂ) := by
  set I := ∫ θ, (starRingEnd ℂ) (f θ) * f' θ with hI
  have hgderiv : ∀ x, HasDerivAt (fun θ => (starRingEnd ℂ) (f θ) * f θ)
      ((starRingEnd ℂ) (f' x) * f x + (starRingEnd ℂ) (f x) * f' x) x := by
    intro x
    have hc : HasDerivAt (fun θ => (starRingEnd ℂ) (f θ)) ((starRingEnd ℂ) (f' x)) x := by
      simpa only [starRingEnd_apply] using (hderiv x).star
    exact hc.mul (hderiv x)
  have hzero : ∫ θ, ((starRingEnd ℂ) (f' θ) * f θ + (starRingEnd ℂ) (f θ) * f' θ) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hgderiv (h1.add h2) hff
  rw [integral_add h1 h2] at hzero
  have hconj : ∫ θ, (starRingEnd ℂ) (f' θ) * f θ = (starRingEnd ℂ) I := by
    rw [hI, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp [mul_comm]
  rw [hconj, ← hI] at hzero
  have hre : I.re = 0 := by
    have h := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at h
    linarith
  have hII : I = Complex.I * (I.im : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, hre]
    · simp [Complex.mul_im]
  rw [hII]
  have hrm : rapidityMomentum f f' = I.im := by simp only [rapidityMomentum, hI]
  rw [hrm]

/-- **★★ Phase 3b-ii assembly: the horizon flux equals `−2π·rapidityMomentum` (modulo the Parseval step).**
    Given the genuine analytic fact `hFlux` — that the Parseval/Fourier-derivative computation reduces the
    horizon flux to `2π·i·∫ conj(a)·a'` — the self-adjointness `inner_deriv_eq_I_mul_rapidityMomentum`
    (`∫ conj(a)a' = i·rapidityMomentum`) turns the two factors of `i` into the real sign, yielding
    `stressFluxKK m f = −2π · rapidityMomentum a a'`.

    `hFlux` is the *one* remaining piece to formalize: the weak sesquilinear Parseval identity applied to
    `χ_H = 𝓕(horizonAmp)` and `ψ_H = 𝓕(−i·horizonAmp')` (`horizonFieldDeriv_eq_fourier` + the Fourier-derivative
    relation), then the `k ↦ θ` change of variables — all standard, Mathlib-provable analysis (Fourier
    inversion + `integral_sesq_fourierIntegral_eq_neg_flip`), deferred.  It is a genuine theorem, NOT a
    conjecture and NOT vacuous (it is a concrete equation between two integrals of the wedge mode). -/
theorem stressFluxKK_eq_of_flux (m : ℝ) (f : V → ℂ) (a a' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt a (a' x) x)
    (hff : Integrable (fun θ => (starRingEnd ℂ) (a θ) * a θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (a' θ) * a θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (a θ) * a' θ))
    (hFlux : ((stressFluxKK m f : ℝ) : ℂ)
        = 2 * Real.pi * Complex.I * ∫ θ, (starRingEnd ℂ) (a θ) * a' θ) :
    stressFluxKK m f = -(2 * Real.pi) * rapidityMomentum a a' := by
  rw [inner_deriv_eq_I_mul_rapidityMomentum a a' hderiv hff h1 h2] at hFlux
  have key : ((stressFluxKK m f : ℝ) : ℂ)
      = ((-(2 * Real.pi) * rapidityMomentum a a' : ℝ) : ℂ) := by
    rw [hFlux]
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (Complex.I * (rapidityMomentum a a' : ℂ))
          = (2 * (Real.pi : ℂ) * (rapidityMomentum a a' : ℂ)) * (Complex.I * Complex.I) from by ring,
      Complex.I_mul_I]
    push_cast; ring
  exact_mod_cast key

/-- **★ Multiplication formula for the real Fourier transform** (self-adjointness of `𝓕`):
    `∫ w, 𝓕 A w · g w = ∫ x, A x · 𝓕 g x`.  Since the real inner product is symmetric, `L.flip = L`, so this
    follows from Mathlib's `integral_fourierIntegral_smul_eq_flip` with NO Fourier inversion.  This is the
    engine of the Parseval pairing `∫ conj(𝓕A)·𝓕B = ∫ conj(A)·B` needed to discharge `hFlux`. -/
theorem real_fourier_mul_formula (A g : ℝ → ℂ)
    (hA : Integrable A) (hg : Integrable g) :
    ∫ w, 𝓕 A w * g w = ∫ x, A x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ) (f := A) (g := g)
    continuous_fourierChar continuous_inner hA hg
  rw [flip_innerₗ] at h
  simpa only [smul_eq_mul] using h

/-- **★★ Parseval pairing for the real Fourier transform** (the conjugate / sesquilinear form):
    `∫ w, conj(𝓕 A w)·𝓕 B w = ∫ x, conj(A x)·B x`.  This is Plancherel in the form Phase 3b-ii needs: it pairs
    `χ_H = 𝓕(horizonAmp)` with `ψ_H = 𝓕(horizonAmp')` to land `∫ conj(A)·B`.  From Mathlib's sesquilinear
    Fourier identity (`integral_sesq_fourierIntegral_eq_neg_flip` with `M = innerSL ℂ`) + Fourier inversion
    `𝓕⁻(𝓕 B) = B`. -/
theorem fourier_conj_parseval (A B : ℝ → ℂ)
    (hA : Integrable A) (hBc : Continuous B) (hB : Integrable B) (hFB : Integrable (𝓕 B)) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 B w = ∫ x, (starRingEnd ℂ) (A x) * B x := by
  have hinv : 𝓕⁻ (𝓕 B) = B := Continuous.fourierInv_fourier_eq hBc hB hFB
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := A) (g := 𝓕 B) continuous_fourierChar continuous_inner hA hFB
  rw [flip_innerₗ] at h
  rw [show (VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ) (-innerₗ ℝ) (𝓕 B)) = B from hinv] at h
  simpa only [coe_innerSL_apply, RCLike.inner_apply'] using h

/-- **★★ Parseval ∘ self-adjointness:** `∫ w, conj(𝓕 A w)·𝓕 (deriv A) w = i·rapidityMomentum A (deriv A)`.
    Chains the Parseval pairing (`fourier_conj_parseval` with `B = deriv A`) with the Hermiticity of `−i∂`
    (`inner_deriv_eq_I_mul_rapidityMomentum`).  This is the spectral side of the horizon flux: once the
    Fourier-derivative relation `w·𝓕A = (2πi)⁻¹·𝓕(deriv A)` puts the affine weight into `𝓕(deriv A)`, this
    lemma evaluates the resulting pairing to the rapidity momentum. -/
theorem fourier_parseval_deriv (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A)
    (hdAc : Continuous (deriv A)) (hdA : Integrable (deriv A)) (hFdA : Integrable (𝓕 (deriv A)))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 (deriv A) w
      = Complex.I * (rapidityMomentum A (deriv A) : ℂ) := by
  rw [fourier_conj_parseval A (deriv A) hA hdAc hdA hFdA]
  exact inner_deriv_eq_I_mul_rapidityMomentum A (deriv A) (fun x => (hAd x).hasDerivAt) hff h1 h2

/-- **★★ The affine-weighted spectral pairing** `∫ w, conj(𝓕A w)·(w·𝓕A w) = (2π)⁻¹·rapidityMomentum A (deriv A)`.
    Mathlib's `fourier_deriv` (`𝓕(deriv A) w = 2πi·w·𝓕A w`) moves the weight `w` onto `𝓕(deriv A)`, and
    `fourier_parseval_deriv` evaluates the result; the `2πi` and the `i` from self-adjointness combine to the
    real factor `(2π)⁻¹`.  This is the `w`-weighted norm of `χ_H = 𝓕A` — exactly the shape of `stressFluxKK`
    after the `λ = 2π w` rescale. -/
theorem fourier_weighted_pairing (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A)
    (hdAc : Continuous (deriv A)) (hdA : Integrable (deriv A)) (hFdA : Integrable (𝓕 (deriv A)))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w)
      = (1 / (2 * Real.pi) : ℂ) * (rapidityMomentum A (deriv A) : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hpd := fourier_parseval_deriv A hA hAd hdAc hdA hFdA hff h1 h2
  have hstep : (∫ w, (starRingEnd ℂ) (𝓕 A w) * 𝓕 (deriv A) w)
      = (2 * (Real.pi : ℂ) * Complex.I)
          * ∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    rw [fourier_deriv hA hAd hdA]
    simp only [smul_eq_mul]
    ring
  rw [hstep] at hpd
  refine mul_left_cancel₀ h2pi ?_
  rw [hpd]
  field_simp

/-- **★★ The real `w`-weighted Fourier norm** `∫ w, w·‖𝓕A w‖² = (2π)⁻¹·rapidityMomentum A (deriv A)`.
    The real form of `fourier_weighted_pairing`, using `conj(z)·z = ‖z‖²`. -/
theorem weighted_pairing_real (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A)
    (hdAc : Continuous (deriv A)) (hdA : Integrable (deriv A)) (hFdA : Integrable (𝓕 (deriv A)))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ w, w * ‖𝓕 A w‖ ^ 2 = (1 / (2 * Real.pi)) * rapidityMomentum A (deriv A) := by
  have hnorm : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hwp := fourier_weighted_pairing A hA hAd hdAc hdA hFdA hff h1 h2
  have ha : (∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w))
      = ((∫ w, w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ) := by
    have hc : (∫ w, (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w))
        = ∫ w, ((w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      show (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w) = ((w * ‖𝓕 A w‖ ^ 2 : ℝ) : ℂ)
      rw [show (starRingEnd ℂ) (𝓕 A w) * ((w : ℂ) * 𝓕 A w)
            = (w : ℂ) * ((starRingEnd ℂ) (𝓕 A w) * 𝓕 A w) from by ring, hnorm (𝓕 A w)]
      push_cast; ring
    rw [hc]; exact integral_ofReal
  rw [ha] at hwp
  exact_mod_cast hwp

/-- **★★ The flux integral in `λ` equals `2π·rapidityMomentum`.**  After the `λ = 2π w` rescale (the `χ_H`
    arguments carry `λ/2π`), the `(2π)²` Jacobian-and-weight factor times `weighted_pairing_real`'s `(2π)⁻¹`
    gives `∫ λ, λ·‖𝓕A(λ/2π)‖² = 2π·rapidityMomentum A (deriv A)`.  This is exactly `stressFluxKK` once
    `A = horizonAmp` (via `horizonFieldDeriv_eq_fourier`). -/
theorem flux_integral_eq (A : ℝ → ℂ)
    (hA : Integrable A) (hAd : Differentiable ℝ A)
    (hdAc : Continuous (deriv A)) (hdA : Integrable (deriv A)) (hFdA : Integrable (𝓕 (deriv A)))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (A θ) * A θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv A θ) * A θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (A θ) * deriv A θ)) :
    ∫ lam, lam * ‖𝓕 A (lam / (2 * Real.pi))‖ ^ 2 = 2 * Real.pi * rapidityMomentum A (deriv A) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi) ≠ 0 := hpos.ne'
  set φ : ℝ → ℝ := fun lam => lam * ‖𝓕 A (lam / (2 * Real.pi))‖ ^ 2 with hφ
  have hphi : ∀ x, φ (2 * Real.pi * x) = 2 * Real.pi * (x * ‖𝓕 A x‖ ^ 2) := by
    intro x
    simp only [hφ]
    rw [show (2 * Real.pi * x) / (2 * Real.pi) = x from by
      rw [mul_comm, mul_div_assoc, div_self hne, mul_one]]
    ring
  have hlem := Measure.integral_comp_mul_left φ (2 * Real.pi)
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), smul_eq_mul] at hlem
  simp only [hphi] at hlem
  rw [integral_const_mul] at hlem
  have hwpr := weighted_pairing_real A hA hAd hdAc hdA hFdA hff h1 h2
  rw [show (∫ lam, φ lam) = 2 * Real.pi * (2 * Real.pi * ∫ x, x * ‖𝓕 A x‖ ^ 2) from by
    rw [hlem, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
  rw [hwpr]; field_simp

/-- **★★★ The horizon stress flux as a rapidity momentum.**  Instantiating `flux_integral_eq` at the wedge
    mode's horizon amplitude `A = horizonAmp m f` (via `horizonFieldDeriv_eq_fourier`, so `χ_H = 𝓕 A`):
    `stressFluxKK m f = 2π · rapidityMomentum (horizonAmp m f) (deriv (horizonAmp m f))`.
    The hypotheses are the genuine on-shell regularity of the horizon amplitude (its differentiability,
    integrability, and that of its derivative and Fourier transform) — true for nicely-decaying test functions.
    The `k ↦ θ` change of variables (next) relates `rapidityMomentum(horizonAmp)` to the wedge wavefunction's
    `∫ conj(Krep)·Krep'`, producing the `hFlux` shape with the geometric sign. -/
theorem stressFluxKK_eq_rapMom (m : ℝ) (hm : 0 < m) (f : V → ℂ)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdAc : Continuous (deriv (horizonAmp m f))) (hdA : Integrable (deriv (horizonAmp m f)))
    (hFdA : Integrable (𝓕 (deriv (horizonAmp m f))))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    stressFluxKK m f
      = 2 * Real.pi * rapidityMomentum (horizonAmp m f) (deriv (horizonAmp m f)) := by
  have hint : (∫ lam, lam * Tkk m f lam)
      = ∫ lam, lam * ‖𝓕 (horizonAmp m f) (lam / (2 * Real.pi))‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun lam => ?_))
    show lam * ‖horizonFieldDeriv m f lam‖ ^ 2
      = lam * ‖𝓕 (horizonAmp m f) (lam / (2 * Real.pi))‖ ^ 2
    rw [horizonFieldDeriv_eq_fourier m hm f lam]
  rw [show stressFluxKK m f = ∫ lam, lam * Tkk m f lam from rfl, hint]
  exact flux_integral_eq (horizonAmp m f) hA hAd hdAc hdA hFdA hff h1 h2

/-- **★ The horizon amplitude's derivative** (chain rule for `−i·Krep∘rapInv` on `(0,∞)`):
    given the wedge mode's rapidity derivative `kd` (`HasDerivAt Krep kd`), for `x > 0`
    `HasDerivAt (horizonAmp m f) ((i/x)·kd(rapInv m x)) x`.  (`Ioi 0` is open so the indicator is locally the
    smooth amplitude; `rapInv' = −1/x`.)  This is the `B = −iA'` partner's explicit form, the input to the
    `k ↦ θ` change of variables relating `rapidityMomentum(horizonAmp)` to the wedge `∫conj(Krep)·Krep'`. -/
theorem horizonAmp_hasDerivAt (m : ℝ) (hm : 0 < m) (f : V → ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (horizonAmp m f) ((Complex.I / (x : ℂ)) * kd (rapInv m x)) x := by
  have hrapInv : HasDerivAt (rapInv m) (-x⁻¹) x := by
    simpa [rapInv] using (Real.hasDerivAt_log hx.ne').const_sub (Real.log (m / Real.sqrt 2))
  have hcomp : HasDerivAt (fun y => Krep m f (rapInv m y)) ((-x⁻¹ : ℝ) • kd (rapInv m x)) x :=
    (hkd (rapInv m x)).scomp x hrapInv
  have hg : HasDerivAt (fun y => -Complex.I * Krep m f (rapInv m y))
      (-Complex.I * ((-x⁻¹ : ℝ) • kd (rapInv m x))) x := hcomp.const_mul (-Complex.I)
  have hval : -Complex.I * ((-x⁻¹ : ℝ) • kd (rapInv m x))
      = (Complex.I / (x : ℂ)) * kd (rapInv m x) := by
    rw [Complex.real_smul]; push_cast; ring
  rw [hval] at hg
  have heq : horizonAmp m f =ᶠ[nhds x] (fun y => -Complex.I * Krep m f (rapInv m y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy _
  exact hg.congr_of_eventuallyEq heq

/-- **★★ The `k ↦ θ` change of variables for the horizon momentum.**
    `∫ x, conj(horizonAmp m f x)·(deriv horizonAmp) x = − ∫ θ, conj(Krep m f θ)·kd θ`, where `kd` is the wedge
    mode's rapidity derivative.  The integrand vanishes for `x ≤ 0` (the indicator), and for `x > 0` the
    explicit derivative (`horizonAmp_hasDerivAt`) + `conj(−i·z)=i·conj z` give `(−1/x)·conj(Krep)·kd`; the
    Jacobian `|nullMom'|=nullMom` of `θ ↦ k = nullMom θ` cancels the `1/x`, and the orientation flip
    (`k=e^{−θ}` decreasing) produces the minus sign. -/
theorem horizonAmp_inner_deriv (m : ℝ) (hm : 0 < m) (f : V → ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ) :
    (∫ x, (starRingEnd ℂ) (horizonAmp m f x) * deriv (horizonAmp m f) x)
      = - ∫ θ, (starRingEnd ℂ) (Krep m f θ) * kd θ := by
  set h : ℝ → ℂ :=
    fun x => (-(x : ℂ)⁻¹) * ((starRingEnd ℂ) (Krep m f (rapInv m x)) * kd (rapInv m x)) with hh
  have hg : ∀ x, (starRingEnd ℂ) (horizonAmp m f x) * deriv (horizonAmp m f) x
      = Set.indicator (Set.Ioi 0) h x := by
    intro x
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
      have hxpos : 0 < x := hx
      have hd : deriv (horizonAmp m f) x = (Complex.I / (x : ℂ)) * kd (rapInv m x) :=
        (horizonAmp_hasDerivAt m hm f kd hkd hxpos).deriv
      have ha : horizonAmp m f x = -Complex.I * Krep m f (rapInv m x) := by
        simp only [horizonAmp, Set.indicator_of_mem hx]
      have hconj : (starRingEnd ℂ) (horizonAmp m f x)
          = Complex.I * (starRingEnd ℂ) (Krep m f (rapInv m x)) := by
        rw [ha, map_mul, map_neg, Complex.conj_I]; ring
      rw [hd, hconj, hh, div_eq_mul_inv,
        show Complex.I * (starRingEnd ℂ) (Krep m f (rapInv m x))
              * (Complex.I * (x : ℂ)⁻¹ * kd (rapInv m x))
            = (Complex.I * Complex.I)
              * ((x : ℂ)⁻¹ * ((starRingEnd ℂ) (Krep m f (rapInv m x)) * kd (rapInv m x))) from by ring,
        Complex.I_mul_I]
      ring
    · rw [Set.indicator_of_notMem hx]
      have ha : horizonAmp m f x = 0 := by simp only [horizonAmp, Set.indicator_of_notMem hx]
      rw [ha, map_zero, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hg), integral_indicator measurableSet_Ioi]
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := nullMom m)
    (f' := fun θ => -(nullMom m θ)) (s := Set.univ) MeasurableSet.univ
    (fun θ _ => (nullMom_hasDerivAt m θ).hasDerivWithinAt) ((nullMom_injective m hm).injOn) h
  rw [nullMom_image_univ m hm] at hcov
  rw [hcov, setIntegral_univ, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  have hnz : ((nullMom m θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nullMom_pos m hm θ).ne'
  simp only [hh, rapInv_nullMom m hm θ, abs_neg, abs_of_pos (nullMom_pos m hm θ), Complex.real_smul]
  field_simp

/-- **★★★★ Route B target: the free-field horizon stress flux equals `−2π·rapidityMomentum` of the wedge mode.**
    `stressFluxKK m f = −2π · rapidityMomentum (Krep m f) Krep'` — the *defined* null stress flux
    `∫_H λ T_kk dλ` equals (up to the fixed `−2π`) the rapidity-momentum boost charge of the one-particle
    wedge mode, exactly the scalar `hTkk` asserted.  Combines `stressFluxKK_eq_rapMom`
    (`= 2π·rapidityMomentum(horizonAmp)`) with the `k↦θ` change of variables `horizonAmp_inner_deriv`
    (`rapidityMomentum(horizonAmp) = −rapidityMomentum(Krep)`).

    The hypotheses are the genuine on-shell regularity of the wedge mode (`kd = Krep'` its rapidity derivative,
    and the integrability/differentiability of the horizon amplitude) — true for nicely-decaying test functions.
    This discharges the scalar stress-flux identification `hTkk` of the QIQT→GR boost-charge=stress-flux input. -/
theorem stressFluxKK_eq_neg_rapMom (m : ℝ) (hm : 0 < m) (f : V → ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdAc : Continuous (deriv (horizonAmp m f))) (hdA : Integrable (deriv (horizonAmp m f)))
    (hFdA : Integrable (𝓕 (deriv (horizonAmp m f))))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    stressFluxKK m f = -(2 * Real.pi) * rapidityMomentum (fun θ => Krep m f θ) kd := by
  have hrel : rapidityMomentum (horizonAmp m f) (deriv (horizonAmp m f))
      = - rapidityMomentum (fun θ => Krep m f θ) kd := by
    simp only [rapidityMomentum]
    rw [horizonAmp_inner_deriv m hm f kd hkd, Complex.neg_im]
  rw [stressFluxKK_eq_rapMom m hm f hA hAd hdAc hdA hFdA hff h1 h2, hrel]
  ring

/-- **★★★ Bridge to the GR chain's `hTkk`.**  The boost energy of the wedge mode in the exact form the
    `wedge_hBoostCharge_of_smooth` input uses — `(2π·∫ conj(Krep)·Krep').im` — equals `−stressFluxKK`.
    Hence defining the chain's stress scalar by `T_kk := −(ℏ/2π)·stressFluxKK` makes the labelled `hTkk`
    (`(2π/ℏ)·T_kk = (2π·∫conj(f)·f').im`) hold by `stressFluxKK_eq_neg_rapMom`: the bundled scalar `T_kk` is
    now the DEFINED, proven free-field horizon stress flux, not a free parameter.  Same on-shell regularity
    hypotheses. -/
theorem boostEnergy_eq_neg_stressFlux (m : ℝ) (hm : 0 < m) (f : V → ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdAc : Continuous (deriv (horizonAmp m f))) (hdA : Integrable (deriv (horizonAmp m f)))
    (hFdA : Integrable (𝓕 (deriv (horizonAmp m f))))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    (2 * Real.pi * ∫ θ, (starRingEnd ℂ) (Krep m f θ) * kd θ).im = - stressFluxKK m f := by
  rw [stressFluxKK_eq_neg_rapMom m hm f kd hkd hA hAd hdAc hdA hFdA hff h1 h2]
  simp only [rapidityMomentum, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **★★★★ Route B, hkd discharged: for a compactly-supported test function the wedge mode is differentiable
    and the horizon stress flux equals `−2π·rapidityMomentum(Krep)(Krep')`.**  Instantiates
    `stressFluxKK_eq_neg_rapMom` with the rapidity derivative `Krep' = kd` produced by `Krep_hasDerivAt`,
    removing the differentiability hypothesis `hkd` (the hardest on-shell regularity gate) from the labelled
    inputs.  Only the softer horizon-amplitude regularity (`Differentiable ℝ horizonAmp` and integrability)
    remains as labelled hypotheses; both follow from `Krep` being Schwartz-on-rapidity. -/
theorem stressFluxKK_eq_neg_rapMom_cptSupp (m : ℝ) (hm : 0 < m) (f : V → ℂ)
    (hf : Continuous f) (hf_supp : HasCompactSupport f)
    (hA : Integrable (horizonAmp m f)) (hAd : Differentiable ℝ (horizonAmp m f))
    (hdAc : Continuous (deriv (horizonAmp m f))) (hdA : Integrable (deriv (horizonAmp m f)))
    (hFdA : Integrable (𝓕 (deriv (horizonAmp m f))))
    (hff : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * horizonAmp m f θ))
    (h1 : Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m f) θ) * horizonAmp m f θ))
    (h2 : Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m f θ) * deriv (horizonAmp m f) θ)) :
    ∃ kd, (∀ θ, HasDerivAt (fun θ => Krep m f θ) (kd θ) θ) ∧
      stressFluxKK m f = -(2 * Real.pi) * rapidityMomentum (fun θ => Krep m f θ) kd := by
  refine ⟨_, fun θ => Krep_hasDerivAt m hm.le f hf hf_supp θ,
    stressFluxKK_eq_neg_rapMom m hm f _ (fun θ => Krep_hasDerivAt m hm.le f hf hf_supp θ)
      hA hAd hdAc hdA hFdA hff h1 h2⟩

/-- **★★★ The horizon amplitude has derivative `0` at the bifurcation surface `x = 0`** (`f` Schwartz,
    `m > 0`).  The `(cosh)⁻²` Schwartz decay forces the quadratic envelope `‖horizonAmp t‖ ≤ K·t²`
    (via `cosh(rapInv t) = (c²+t²)/(2ct)`), so the slope `→ 0` (`squeeze_zero_norm`) and the derivative is `0`.
    The boundary input to both `horizonAmp_differentiable` (`hAd`) and `horizonAmp_deriv_continuous` (`hdAc`). -/
theorem horizonAmp_hasDerivAt_zero {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    HasDerivAt (horizonAmp m (⇑f)) 0 0 := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set C : ℝ := 16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2) with hCdef
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  set K : ℝ := 4 * C / c ^ 2 with hKdef
  have hKnn : (0 : ℝ) ≤ K := by rw [hKdef]; exact div_nonneg (by positivity) (by positivity)
  have hbound : ∀ t : ℝ, ‖horizonAmp m (⇑f) t‖ ≤ K * t ^ 2 := by
    intro t
    simp only [horizonAmp, Set.indicator_apply]
    split_ifs with ht
    · rw [Set.mem_Ioi] at ht
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      have hcosh_eq : Real.cosh (rapInv m t) = (c ^ 2 + t ^ 2) / (2 * c * t) := by
        rw [rapInv, ← hc, ← Real.log_div hcpos.ne' ht.ne', Real.cosh_log (by positivity)]
        field_simp
      have hdecay := schwartz_Krep_decay_sq f hm.ne' (rapInv m t)
      rw [hcosh_eq, ← hCdef] at hdecay
      refine le_trans hdecay ?_
      rw [div_pow, inv_div, ← mul_div_assoc, div_le_iff₀ (by positivity), hKdef,
        show 4 * C / c ^ 2 * t ^ 2 * (c ^ 2 + t ^ 2) ^ 2
          = 4 * C * t ^ 2 * (c ^ 2 + t ^ 2) ^ 2 / c ^ 2 by ring, le_div_iff₀ (by positivity)]
      have hh : (0 : ℝ) ≤ 4 * C * (t ^ 4 * (2 * c ^ 2 + t ^ 2)) :=
        mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)
      nlinarith [hh]
    · rw [norm_zero]; exact mul_nonneg hKnn (sq_nonneg t)
  rw [hasDerivAt_iff_tendsto_slope]
  have h0val : horizonAmp m (⇑f) 0 = 0 := by
    simp only [horizonAmp]; rw [Set.indicator_of_notMem (by simp : (0 : ℝ) ∉ Set.Ioi 0)]
  have hsl : ∀ t : ℝ, ‖slope (horizonAmp m (⇑f)) 0 t‖ ≤ K * |t| := by
    intro t
    rw [slope_def_module, h0val, sub_zero, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · refine (mul_le_mul_of_nonneg_left (hbound t) (by positivity)).trans (le_of_eq ?_)
      rw [← sq_abs]; field_simp
  have htend : Filter.Tendsto (fun t : ℝ => K * |t|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h := (tendsto_const_nhds (x := K)).mul (continuous_abs.tendsto (0 : ℝ))
    simp only [abs_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm hsl htend

/-- **★★★ The horizon amplitude is differentiable** for a Schwartz test function `f` (`m > 0`), given the
    wedge mode's rapidity derivative `kd` (`HasDerivAt Krep kd`).  Three regions: `x < 0` locally `0`;
    `x > 0` via `horizonAmp_hasDerivAt`; `x = 0` via `horizonAmp_hasDerivAt_zero`.  Discharges `hAd`. -/
theorem horizonAmp_differentiable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) (kd : ℝ → ℂ)
    (hkd : ∀ θ, HasDerivAt (fun θ => Krep m (⇑f) θ) (kd θ) θ) :
    Differentiable ℝ (horizonAmp m (⇑f)) := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · refine ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hx)] with y hy
    have hynot : y ∉ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi, not_lt]; exact (Set.mem_Iio.mp hy).le
    simp only [horizonAmp, Set.indicator_of_notMem hynot]
  · subst hx; exact (horizonAmp_hasDerivAt_zero hm f).differentiableAt
  · exact (horizonAmp_hasDerivAt m hm (⇑f) kd hkd hx).differentiableAt

/-- **★★ The self-adjoint integrability `∫ conj(A)·A`** (`hff`) for the horizon amplitude `A = horizonAmp m f`
    (`f` Schwartz, `m > 0`).  Since `‖conj(A x)·A x‖ = ‖A x‖²`, the Cauchy envelope
    `‖A x‖ ≤ 4Cc²(c²+x²)⁻¹` (`horizonAmp_norm_le`) gives the squared dominator `(4Cc²)²·((c²+x²)⁻¹)²`
    (`integrable_inv_const_sq_add_sq`).  Discharges the `hff` regularity hypothesis. -/
theorem horizonAmp_sq_integrable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m (⇑f) θ) * horizonAmp m (⇑f) θ) := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set B : ℝ := 4 * (16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2)) * (m / Real.sqrt 2) ^ 2 with hBdef
  have hrap_meas : Measurable (rapInv m) := by
    unfold rapInv; exact measurable_const.sub Real.measurable_log
  have hg_meas : Measurable (fun x : ℝ => -Complex.I * Krep m (⇑f) (rapInv m x)) :=
    ((Krep_continuous f.integrable).measurable.comp hrap_meas).const_mul _
  have hA_aes : AEStronglyMeasurable (horizonAmp m (⇑f)) volume :=
    hg_meas.aestronglyMeasurable.indicator measurableSet_Ioi
  refine ((integrable_inv_const_sq_add_sq hcpos).const_mul (B ^ 2)).mono'
    ((Complex.continuous_conj.comp_aestronglyMeasurable hA_aes).mul hA_aes) ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_conj]
  have hb : ‖horizonAmp m (⇑f) x‖ ≤ B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹ := by
    rw [hBdef]; exact horizonAmp_norm_le hm f x
  have hBcInv : B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹ = B * (c ^ 2 + x ^ 2)⁻¹ := by rw [hc]
  rw [hBcInv] at hb
  calc ‖horizonAmp m (⇑f) x‖ * ‖horizonAmp m (⇑f) x‖
      ≤ (B * (c ^ 2 + x ^ 2)⁻¹) * (B * (c ^ 2 + x ^ 2)⁻¹) :=
        mul_le_mul hb hb (norm_nonneg _) (le_trans (norm_nonneg _) hb)
    _ = B ^ 2 * ((c ^ 2 + x ^ 2)⁻¹) ^ 2 := by ring

/-- **★★ The `(cosh)⁻¹` decay of the actual derivative `deriv (Krep m f)`** (`f` Schwartz, `m > 0`).  Packages
    `kd_norm_le` against the genuine `deriv` via `schwartz_Krep_hasDerivAt.deriv` — so `kd := deriv (Krep m f)`
    is both bounded (`≤ C·(cosh θ)⁻¹`) and, being a `deriv`, automatically measurable (`measurable_deriv`).
    This is the bound every remaining horizon-amplitude derivative gate (`hdA`/`hdAc`/`hFdA`/`h1`/`h2`) consumes. -/
theorem Krep_deriv_norm_le {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, ‖deriv (fun θ => Krep m (⇑f) θ) θ‖ ≤ C * (Real.cosh θ)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := kd_norm_le m hm f
  refine ⟨C, hC, fun θ => ?_⟩
  rw [(schwartz_Krep_hasDerivAt m hm.le f θ).deriv]
  exact hb θ

/-- **`(cosh)⁻²` (super-exponential) decay of `deriv (Krep m f)`** — packages `kd_norm_le_sq` against the
    genuine `deriv` (`schwartz_Krep_hasDerivAt.deriv`).  The bound the `hdAc` boundary squeeze consumes. -/
theorem Krep_deriv_norm_le_sq {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, ‖deriv (fun θ => Krep m (⇑f) θ) θ‖ ≤ C * ((Real.cosh θ) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := kd_norm_le_sq m hm f
  refine ⟨C, hC, fun θ => ?_⟩
  rw [(schwartz_Krep_hasDerivAt m hm.le f θ).deriv]
  exact hb θ

/-- **The Cauchy bound + measurability of `deriv (horizonAmp)`** — the shared analytic core of the
    derivative gates (`hdA`/`h1`/`h2`).  Off the null set `{0}`, `deriv (horizonAmp m f) = (i/x)·Krep'(rapInv x)`
    on `x > 0` and `0` on `x < 0`; with `cosh(rapInv x) = (c²+x²)/(2cx)` and `‖Krep'(θ)‖ ≤ C·(cosh θ)⁻¹`
    (`Krep_deriv_norm_le`) the `1/x` cancels, leaving `‖deriv(horizonAmp) x‖ ≤ 2Cc·(c²+x²)⁻¹` a.e.  `deriv` is
    measurable (`measurable_deriv`); `{0}` is null (`compl_mem_ae_iff`). -/
theorem horizonAmp_deriv_le {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    AEStronglyMeasurable (deriv (horizonAmp m (⇑f))) volume ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ x ∂volume,
        ‖deriv (horizonAmp m (⇑f)) x‖ ≤ D * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹ := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨C, hC, hCb⟩ := Krep_deriv_norm_le hm f
  set kd : ℝ → ℂ := deriv (fun θ => Krep m (⇑f) θ) with hkddef
  have hkd : ∀ θ, HasDerivAt (fun θ => Krep m (⇑f) θ) (kd θ) θ := fun θ =>
    (schwartz_Krep_hasDerivAt m hm.le f θ).differentiableAt.hasDerivAt
  set derivH : ℝ → ℂ :=
    fun x => (Set.Ioi 0).indicator (fun x : ℝ => (Complex.I / (x : ℂ)) * kd (rapInv m x)) x with hdHdef
  have hrap_meas : Measurable (rapInv m) := by
    unfold rapInv; exact measurable_const.sub Real.measurable_log
  have hae : deriv (horizonAmp m (⇑f)) =ᵐ[volume] derivH := by
    have hnull : volume ({(0 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
    refine Filter.eventuallyEq_of_mem (s := {(0 : ℝ)}ᶜ) (compl_mem_ae_iff.mpr hnull) (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hd0 : derivH x = 0 := by
        simp only [hdHdef]
        exact Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hlt.le) _
      rw [hd0]
      refine ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_).deriv
      filter_upwards [isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt)] with y hy
      exact Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact (Set.mem_Iio.mp hy).le) _
    · have hdx : derivH x = (Complex.I / (x : ℂ)) * kd (rapInv m x) := by
        simp only [hdHdef]
        exact Set.indicator_of_mem (Set.mem_Ioi.mpr hgt) _
      rw [hdx]
      exact (horizonAmp_hasDerivAt m hm (⇑f) kd hkd hgt).deriv
  have hderivH_meas : Measurable derivH := by
    rw [hdHdef]
    exact (((measurable_const.div Complex.continuous_ofReal.measurable).mul
      ((measurable_deriv (fun θ => Krep m (⇑f) θ)).comp hrap_meas)).indicator measurableSet_Ioi)
  have hbound : ∀ x : ℝ, ‖derivH x‖ ≤ 2 * C * c * (c ^ 2 + x ^ 2)⁻¹ := by
    intro x
    simp only [hdHdef, Set.indicator_apply]
    split_ifs with hx
    · rw [Set.mem_Ioi] at hx
      rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, one_div]
      have hcosh_eq : Real.cosh (rapInv m x) = (c ^ 2 + x ^ 2) / (2 * c * x) := by
        rw [rapInv, ← hc, ← Real.log_div hcpos.ne' hx.ne', Real.cosh_log (by positivity)]; field_simp
      have hkb := hCb (rapInv m x)
      rw [hcosh_eq] at hkb
      calc x⁻¹ * ‖kd (rapInv m x)‖
          ≤ x⁻¹ * (C * ((c ^ 2 + x ^ 2) / (2 * c * x))⁻¹) :=
            mul_le_mul_of_nonneg_left hkb (by positivity)
        _ = 2 * C * c * (c ^ 2 + x ^ 2)⁻¹ := by rw [inv_div]; field_simp
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity)) (by positivity)
  refine ⟨hderivH_meas.aestronglyMeasurable.congr hae.symm,
    2 * C * c, mul_nonneg (mul_nonneg (by norm_num) hC) hcpos.le, ?_⟩
  filter_upwards [hae] with x hx
  rw [hx]; exact hbound x

/-- **★★★ `deriv (horizonAmp)` is `L¹`** (`hdA`) for a Schwartz test function (`m > 0`). -/
theorem horizonAmp_deriv_integrable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Integrable (deriv (horizonAmp m (⇑f))) := by
  obtain ⟨hmeas, D, _, hb⟩ := horizonAmp_deriv_le hm f
  exact ((integrable_inv_const_sq_add (show (0 : ℝ) < m / Real.sqrt 2 by positivity)).const_mul D).mono'
    hmeas hb

/-- The horizon-amplitude Cauchy envelope in existential form (for use with the `deriv` envelope). -/
theorem horizonAmp_norm_le' {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖horizonAmp m (⇑f) x‖ ≤ B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹ :=
  ⟨4 * (16 * π ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2)) * (m / Real.sqrt 2) ^ 2,
    by positivity, fun x => horizonAmp_norm_le hm f x⟩

/-- **★★ The cross self-pairing `∫ conj(A')·A`** (`h1`) for `A = horizonAmp m f` (`f` Schwartz, `m > 0`).
    `‖conj(A' x)·A x‖ = ‖A' x‖·‖A x‖ ≤ (2Cc·(c²+x²)⁻¹)·(B·(c²+x²)⁻¹)` (`horizonAmp_deriv_le` ×
    `horizonAmp_norm_le'`), dominated by the squared Cauchy kernel (`integrable_inv_const_sq_add_sq`). -/
theorem horizonAmp_deriv_mul_integrable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Integrable (fun θ => (starRingEnd ℂ) (deriv (horizonAmp m (⇑f)) θ) * horizonAmp m (⇑f) θ) := by
  obtain ⟨hAd_meas, D, _, hAd_b⟩ := horizonAmp_deriv_le hm f
  obtain ⟨B, _, hA_b⟩ := horizonAmp_norm_le' hm f
  have hA_aes : AEStronglyMeasurable (horizonAmp m (⇑f)) volume :=
    (horizonAmp_integrable hm f).aestronglyMeasurable
  refine ((integrable_inv_const_sq_add_sq (show (0 : ℝ) < m / Real.sqrt 2 by positivity)).const_mul
    (D * B)).mono' ((Complex.continuous_conj.comp_aestronglyMeasurable hAd_meas).mul hA_aes) ?_
  filter_upwards [hAd_b] with x hx
  rw [norm_mul, Complex.norm_conj]
  calc ‖deriv (horizonAmp m (⇑f)) x‖ * ‖horizonAmp m (⇑f) x‖
      ≤ (D * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) * (B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) :=
        mul_le_mul hx (hA_b x) (norm_nonneg _) (le_trans (norm_nonneg _) hx)
    _ = D * B * (((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := by ring

/-- **★★ The cross self-pairing `∫ conj(A)·A'`** (`h2`) for `A = horizonAmp m f` (`f` Schwartz, `m > 0`). -/
theorem horizonAmp_mul_deriv_integrable {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Integrable (fun θ => (starRingEnd ℂ) (horizonAmp m (⇑f) θ) * deriv (horizonAmp m (⇑f)) θ) := by
  obtain ⟨hAd_meas, D, _, hAd_b⟩ := horizonAmp_deriv_le hm f
  obtain ⟨B, _, hA_b⟩ := horizonAmp_norm_le' hm f
  have hA_aes : AEStronglyMeasurable (horizonAmp m (⇑f)) volume :=
    (horizonAmp_integrable hm f).aestronglyMeasurable
  refine ((integrable_inv_const_sq_add_sq (show (0 : ℝ) < m / Real.sqrt 2 by positivity)).const_mul
    (B * D)).mono' ((Complex.continuous_conj.comp_aestronglyMeasurable hA_aes).mul hAd_meas) ?_
  filter_upwards [hAd_b] with x hx
  rw [norm_mul, Complex.norm_conj]
  calc ‖horizonAmp m (⇑f) x‖ * ‖deriv (horizonAmp m (⇑f)) x‖
      ≤ (B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) * (D * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) :=
        mul_le_mul (hA_b x) hx (norm_nonneg _) (le_trans (norm_nonneg _) (hA_b x))
    _ = B * D * (((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := by ring

/-- **★★★ `deriv (horizonAmp)` is continuous** (`hdAc`) for a Schwartz test function (`m > 0`).  Globally
    `deriv (horizonAmp m f) = derivH` where `derivH x = (i/x)·Krep'(rapInv x)` on `x > 0` and `0` on `x ≤ 0`
    (`horizonAmp_hasDerivAt` / `horizonAmp_hasDerivAt_zero`).  `derivH` is continuous: off `x = 0` via `Krep' ∈ C⁰`
    (`schwartz_Krep_deriv_continuous`), and AT the bifurcation surface `x = 0` the SUPER-exponential `(cosh)⁻²`
    decay (`Krep_deriv_norm_le_sq`) + `cosh(rapInv t) = (c²+t²)/(2ct)` give `‖derivH t‖ ≤ 4Cc²|t|/(c²+t²)² → 0`,
    so `derivH` is continuous at `0` by squeeze.  Discharges `hdAc`. -/
theorem horizonAmp_deriv_continuous {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    Continuous (deriv (horizonAmp m (⇑f))) := by
  set c : ℝ := m / Real.sqrt 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨C, hC, hCb⟩ := Krep_deriv_norm_le_sq hm f
  set kd : ℝ → ℂ := deriv (fun θ => Krep m (⇑f) θ) with hkddef
  have hkd : ∀ θ, HasDerivAt (fun θ => Krep m (⇑f) θ) (kd θ) θ := fun θ =>
    (schwartz_Krep_hasDerivAt m hm.le f θ).differentiableAt.hasDerivAt
  have hkd_cont : Continuous kd := schwartz_Krep_deriv_continuous hm.le f
  set derivH : ℝ → ℂ :=
    fun x => (Set.Ioi 0).indicator (fun x : ℝ => (Complex.I / (x : ℂ)) * kd (rapInv m x)) x with hdHdef
  have hderiv_eq : deriv (horizonAmp m (⇑f)) = derivH := by
    funext x
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hd0 : derivH x = 0 := by
        simp only [hdHdef]
        exact Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hlt.le) _
      rw [hd0]
      refine ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_).deriv
      filter_upwards [isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt)] with y hy
      exact Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact (Set.mem_Iio.mp hy).le) _
    · have hd0 : derivH 0 = 0 := by
        simp only [hdHdef]; exact Set.indicator_of_notMem (by simp) _
      rw [hd0, (horizonAmp_hasDerivAt_zero hm f).deriv]
    · have hdx : derivH x = (Complex.I / (x : ℂ)) * kd (rapInv m x) := by
        simp only [hdHdef]; exact Set.indicator_of_mem (Set.mem_Ioi.mpr hgt) _
      rw [hdx]; exact (horizonAmp_hasDerivAt m hm (⇑f) kd hkd hgt).deriv
  rw [hderiv_eq, continuous_iff_continuousAt]
  intro x₀
  rcases lt_trichotomy x₀ 0 with hlt | rfl | hgt
  · have h0 : ContinuousAt (fun _ : ℝ => (0 : ℂ)) x₀ := continuousAt_const
    refine h0.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt)] with y hy
    show (0 : ℂ) = derivH y
    simp only [hdHdef]
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact (Set.mem_Iio.mp hy).le)]
  · have hd0 : derivH 0 = 0 := by
      simp only [hdHdef]; exact Set.indicator_of_notMem (by simp) _
    have hbd : ∀ t : ℝ, ‖derivH t‖ ≤ 4 * C * c ^ 2 * |t| / (c ^ 2 + t ^ 2) ^ 2 := by
      intro t
      simp only [hdHdef, Set.indicator_apply]
      split_ifs with ht
      · rw [Set.mem_Ioi] at ht
        rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
          one_div]
        have hcosh_eq : Real.cosh (rapInv m t) = (c ^ 2 + t ^ 2) / (2 * c * t) := by
          rw [rapInv, ← hc, ← Real.log_div hcpos.ne' ht.ne', Real.cosh_log (by positivity)]; field_simp
        have hkb := hCb (rapInv m t)
        rw [hcosh_eq] at hkb
        refine (mul_le_mul_of_nonneg_left hkb (by positivity)).trans (le_of_eq ?_)
        rw [div_pow, inv_div]; field_simp; ring
      · rw [norm_zero]; positivity
    have hg_cont : Continuous (fun t : ℝ => 4 * C * c ^ 2 * |t| / (c ^ 2 + t ^ 2) ^ 2) :=
      Continuous.div (continuous_const.mul continuous_abs)
        ((continuous_const.add (continuous_pow 2)).pow 2) (fun t => by positivity)
    have htend : Filter.Tendsto (fun t : ℝ => 4 * C * c ^ 2 * |t| / (c ^ 2 + t ^ 2) ^ 2)
        (nhds 0) (nhds 0) := by simpa using hg_cont.tendsto 0
    show Filter.Tendsto derivH (nhds 0) (nhds (derivH 0))
    rw [hd0]
    exact squeeze_zero_norm hbd htend
  · have hrap : ContinuousAt (rapInv m) x₀ := by
      unfold rapInv; exact continuousAt_const.sub (Real.continuousAt_log hgt.ne')
    have hgfunc : ContinuousAt (fun x : ℝ => (Complex.I / (x : ℂ)) * kd (rapInv m x)) x₀ :=
      (continuousAt_const.div Complex.continuous_ofReal.continuousAt
        (Complex.ofReal_ne_zero.mpr hgt.ne')).mul (hkd_cont.continuousAt.comp hrap)
    refine hgfunc.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hgt)] with y hy
    simp only [hdHdef]
    rw [Set.indicator_of_mem hy]

/-- **★★ The horizon amplitude is `L²`** (`f` Schwartz, `m > 0`) — the wedge mode is normalizable.
    `‖horizonAmp x‖² ≤ B²·((c²+x²)⁻¹)²` (`horizonAmp_norm_le'`), dominated by the squared Cauchy kernel.
    Foundation for the `L²`-Plancherel route to `hFdA`. -/
theorem horizonAmp_memLp_two {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    MemLp (horizonAmp m (⇑f)) 2 volume := by
  have hmeas : AEStronglyMeasurable (horizonAmp m (⇑f)) volume :=
    (horizonAmp_integrable hm f).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  obtain ⟨B, hB, hAb⟩ := horizonAmp_norm_le' hm f
  refine ((integrable_inv_const_sq_add_sq (show (0 : ℝ) < m / Real.sqrt 2 by positivity)).const_mul
    (B ^ 2)).mono' ((continuous_pow 2).comp_aestronglyMeasurable hmeas.norm) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖horizonAmp m (⇑f) x‖ ^ 2
      ≤ (B * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hAb x) 2
    _ = B ^ 2 * (((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := by rw [mul_pow]

/-- **★★ `deriv (horizonAmp)` is `L²`** (`f` Schwartz, `m > 0`).  `‖deriv(horizonAmp) x‖² ≤ D²·((c²+x²)⁻¹)²`
    (`horizonAmp_deriv_le`).  Together with `horizonAmp_memLp_two` this gives `A, A' ∈ L²` — the input the
    Plancherel isometry (`MeasureTheory.Lp.inner_fourier_eq`) needs to discharge `hFdA` without inversion. -/
theorem horizonAmp_deriv_memLp_two {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ) :
    MemLp (deriv (horizonAmp m (⇑f))) 2 volume := by
  obtain ⟨hmeas, D, hD, hAd_b⟩ := horizonAmp_deriv_le hm f
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ((integrable_inv_const_sq_add_sq (show (0 : ℝ) < m / Real.sqrt 2 by positivity)).const_mul
    (D ^ 2)).mono' ((continuous_pow 2).comp_aestronglyMeasurable hmeas.norm) ?_
  filter_upwards [hAd_b] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖deriv (horizonAmp m (⇑f)) x‖ ^ 2
      ≤ (D * ((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    _ = D ^ 2 * (((m / Real.sqrt 2) ^ 2 + x ^ 2)⁻¹) ^ 2 := by rw [mul_pow]

/-- **★★★★ Route B for the SCHWARTZ class — 8 of 9 regularity gates discharged.**  For any Schwartz test
    function `f` (`m > 0`), the horizon stress flux equals the boost momentum
    `stressFluxKK m f = −2π·rapidityMomentum(Krep)(Krep')` — assembling the eight axiom-free regularity
    discharges (`hkd` `hA` `hAd` `hff` `hdA` `h1` `h2` `hdAc`) into `stressFluxKK_eq_neg_rapMom`.  The ONLY
    remaining hypothesis is `hFdA : Integrable (𝓕 (deriv (horizonAmp m f)))` — the integrability of the Fourier
    transform of the derivative (genuinely true for Schwartz `f` since `horizonAmp ∈ C^∞`, but its proof needs
    the third-derivative `C³` layer, or an `L²`-Plancherel refactor of `fourier_conj_parseval` avoiding Fourier
    inversion).  This isolates the single open technical gate of Route B. -/
theorem stressFluxKK_eq_neg_rapMom_schwartz {m : ℝ} (hm : 0 < m) (f : SchwartzMap V ℂ)
    (hFdA : Integrable (𝓕 (deriv (horizonAmp m (⇑f))))) :
    stressFluxKK m (⇑f) = -(2 * Real.pi) *
      rapidityMomentum (fun θ => Krep m (⇑f) θ) (deriv (fun θ => Krep m (⇑f) θ)) := by
  have hkd : ∀ θ, HasDerivAt (fun θ => Krep m (⇑f) θ) (deriv (fun θ => Krep m (⇑f) θ) θ) θ := fun θ =>
    (schwartz_Krep_hasDerivAt m hm.le f θ).differentiableAt.hasDerivAt
  exact stressFluxKK_eq_neg_rapMom m hm (⇑f) (deriv (fun θ => Krep m (⇑f) θ)) hkd
    (horizonAmp_integrable hm f) (horizonAmp_differentiable hm f _ hkd)
    (horizonAmp_deriv_continuous hm f) (horizonAmp_deriv_integrable hm f) hFdA
    (horizonAmp_sq_integrable hm f) (horizonAmp_deriv_mul_integrable hm f)
    (horizonAmp_mul_deriv_integrable hm f)

end QIQTH.Fock.StressTensor
