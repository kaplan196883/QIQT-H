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

end QIQTH.Fock.StressTensor
