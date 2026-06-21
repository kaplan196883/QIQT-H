import QIQTH.Fock.StressTensor.HorizonFourier
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

end QIQTH.Fock.StressTensor
