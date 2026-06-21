import QIQTH.Fock.StressTensor.NullStressFlux
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Free-field stress tensor (Route B) — Phase 3b-i: the horizon field as a Fourier integral on the k-line

`STRESS_TENSOR_FORMALIZATION_PLAN.md`, Phase 3b-i.  Toward `stressFluxKK = −2π·rapidityMomentum`, the first step
is to recognise `horizonFieldDeriv` (= `∂_λ φ_H`) as a genuine **Fourier transform on the null-momentum line**
`k ∈ (0,∞)`, so that Mathlib's sesquilinear Fourier (Parseval) identity applies.

The change of variables is `θ ↦ k = nullMom m θ = (m/√2)e^{−θ}`, a decreasing diffeomorphism `ℝ → (0,∞)` with
inverse `rapInv m x = log(m/√2) − log x` and `|d k/dθ| = k`.  Crucially the Jacobian `k` exactly cancels the
explicit `nullMom` factor in `horizonFieldDeriv`, giving
`horizonFieldDeriv m f λ = ∫_{x>0} (−i·Krep m f (rapInv m x))·e^{−iλx} dx`,
which is (a `2π`-rescaling of) `Real.fourierIntegral` of `A(x) := −i·Krep m f (rapInv m x)·1_{x>0}`.

This file proves the inverse-map infrastructure and that change-of-variables identity.  Axiom-free.  Phase
3b-ii then pairs `χ_H = 𝓕[A]` with `ψ_H = 𝓕[B]` (`B = K'/k`) via the sesquilinear identity.
-/

namespace QIQTH.Fock.StressTensor

open MeasureTheory
open QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- The inverse of the null-momentum map `θ ↦ nullMom m θ = (m/√2)e^{−θ}` on `(0,∞)`:
    `rapInv m x = log(m/√2) − log x`. -/
noncomputable def rapInv (m x : ℝ) : ℝ := Real.log (m / Real.sqrt 2) - Real.log x

theorem nullMom_pos (m : ℝ) (hm : 0 < m) (θ : ℝ) : 0 < nullMom m θ :=
  mul_pos (div_pos hm (Real.sqrt_pos.mpr two_pos)) (Real.exp_pos _)

/-- `rapInv` is a left inverse of `nullMom`: `rapInv m (nullMom m θ) = θ`. -/
theorem rapInv_nullMom (m : ℝ) (hm : 0 < m) (θ : ℝ) : rapInv m (nullMom m θ) = θ := by
  have hc : 0 < m / Real.sqrt 2 := div_pos hm (Real.sqrt_pos.mpr two_pos)
  simp only [rapInv, nullMom]
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `rapInv` is a right inverse of `nullMom` on `(0,∞)`: `nullMom m (rapInv m x) = x` for `x > 0`. -/
theorem nullMom_rapInv (m : ℝ) (hm : 0 < m) {x : ℝ} (hx : 0 < x) : nullMom m (rapInv m x) = x := by
  have hc : 0 < m / Real.sqrt 2 := div_pos hm (Real.sqrt_pos.mpr two_pos)
  simp only [nullMom, rapInv, neg_sub, Real.exp_sub, Real.exp_log hx, Real.exp_log hc]
  field_simp

theorem nullMom_injective (m : ℝ) (hm : 0 < m) : Function.Injective (nullMom m) :=
  Function.LeftInverse.injective (rapInv_nullMom m hm)

/-- `nullMom m` has derivative `−(nullMom m θ)` (since `d/dθ (c e^{−θ}) = −c e^{−θ}`). -/
theorem nullMom_hasDerivAt (m θ : ℝ) : HasDerivAt (nullMom m) (-(nullMom m θ)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-θ)) θ := by
    simpa using (Real.hasDerivAt_exp (-θ)).comp θ ((hasDerivAt_id θ).neg)
  have h2 := h1.const_mul (m / Real.sqrt 2)
  have hfun : (fun t : ℝ => m / Real.sqrt 2 * Real.exp (-t)) = nullMom m := rfl
  rw [hfun] at h2
  convert h2 using 1
  simp only [nullMom]; ring

/-- The image of the null-momentum map is exactly the open half-line `(0,∞)`. -/
theorem nullMom_image_univ (m : ℝ) (hm : 0 < m) : nullMom m '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_univ]
  ext y
  simp only [Set.mem_range, Set.mem_Ioi]
  constructor
  · rintro ⟨θ, rfl⟩; exact nullMom_pos m hm θ
  · intro hy; exact ⟨rapInv m y, nullMom_rapInv m hm hy⟩

/-- **★ Phase 3b-i: the horizon-field derivative is a Fourier integral on the k-line.**
    `horizonFieldDeriv m f λ = ∫_{x>0} (−i·Krep m f (rapInv m x)) · e^{−iλx} dx`.
    The change of variables `θ ↦ k = nullMom m θ` turns the (non-Fourier) `θ`-integral into a genuine Fourier
    transform in the null-momentum variable `x = k`; the Jacobian `|dk/dθ| = k` exactly cancels the explicit
    `nullMom` factor in `horizonFieldDeriv`.  This is the entry point to the sesquilinear-Fourier evaluation. -/
theorem horizonFieldDeriv_eq_kIntegral (m : ℝ) (hm : 0 < m) (f : V → ℂ) (lam : ℝ) :
    horizonFieldDeriv m f lam
      = ∫ x in Set.Ioi (0 : ℝ),
          (-Complex.I * Krep m f (rapInv m x)) * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ)) := by
  set g : ℝ → ℂ := fun x =>
    (-Complex.I * Krep m f (rapInv m x)) * Complex.exp (-Complex.I * (lam : ℂ) * (x : ℂ)) with hg
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := nullMom m)
    (f' := fun θ => -(nullMom m θ)) (s := Set.univ) MeasurableSet.univ
    (fun θ _ => (nullMom_hasDerivAt m θ).hasDerivWithinAt) ((nullMom_injective m hm).injOn) g
  rw [nullMom_image_univ m hm] at hcov
  have hpt : ∀ θ, |-(nullMom m θ)| • g (nullMom m θ)
      = Krep m f θ * (-Complex.I * (nullMom m θ : ℂ))
          * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)) := by
    intro θ
    simp only [hg, rapInv_nullMom m hm θ, abs_neg, abs_of_pos (nullMom_pos m hm θ),
      Complex.real_smul]
    push_cast; ring
  calc horizonFieldDeriv m f lam
      = ∫ θ, Krep m f θ * (-Complex.I * (nullMom m θ : ℂ))
          * Complex.exp (-Complex.I * (lam : ℂ) * (nullMom m θ : ℂ)) := rfl
    _ = ∫ θ, |-(nullMom m θ)| • g (nullMom m θ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => (hpt θ).symm))
    _ = ∫ θ in Set.univ, |-(nullMom m θ)| • g (nullMom m θ) := setIntegral_univ.symm
    _ = ∫ x in Set.Ioi (0 : ℝ), g x := hcov.symm

end QIQTH.Fock.StressTensor
