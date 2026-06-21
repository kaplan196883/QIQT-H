import QIQTH.Fock.StressTensor.HorizonFourier
import Mathlib.Analysis.Fourier.FourierTransform

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

end QIQTH.Fock.StressTensor
