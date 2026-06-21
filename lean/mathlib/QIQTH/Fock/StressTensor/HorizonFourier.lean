import QIQTH.Fock.StressTensor.NullStressFlux
import QIQTH.Fock.PauliJordan
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

/-- **The θ-derivative of the `Krep` integrand** (the `h_diff` ingredient of the differentiation-under-the-
    integral for `Krep`).  For each fixed `x`, `θ ↦ e^{−i η(p_m(θ),x)}·f(x)` is differentiable with derivative
    `e^{−i η(p_m(θ),x)}·(−i·m(x₀ sinh θ − x₁ cosh θ))·f(x)`, since `∂_θ η(p_m(θ),x) = m(x₀ sinh θ − x₁ cosh θ)`
    (from `minkowskiDot_massShell` and `cosh' = sinh`, `sinh' = cosh`).  This is the pointwise core of
    `Krep`'s rapidity differentiability `kd = Krep'`; the full statement adds the dominated-convergence
    domination (a `(|x₀|+|x₁|)·‖f x‖` bound, integrable for compactly-supported `f`). -/
theorem Krep_integrand_hasDerivAt (m : ℝ) (f : V → ℂ) (x : V) (θ : ℝ) :
    HasDerivAt
      (fun θ => Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * f x)
      ((Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * f x) θ := by
  have hg : HasDerivAt (fun θ => (minkowskiDot (massShell m θ) x : ℝ))
      (m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ)) θ := by
    have h1 : HasDerivAt (fun θ => x 0 * Real.cosh θ) (x 0 * Real.sinh θ) θ :=
      (Real.hasDerivAt_cosh θ).const_mul (x 0)
    have h2 : HasDerivAt (fun θ => x 1 * Real.sinh θ) (x 1 * Real.cosh θ) θ :=
      (Real.hasDerivAt_sinh θ).const_mul (x 1)
    have h0 := (h1.sub h2).const_mul m
    have heq : (fun θ => (minkowskiDot (massShell m θ) x : ℝ))
        = fun θ => m * (x 0 * Real.cosh θ - x 1 * Real.sinh θ) := by
      funext θ; exact minkowskiDot_massShell m θ x
    rw [heq]; exact h0
  exact (((hg.ofReal_comp).const_mul (-Complex.I)).cexp).mul_const (f x)

/-- **The domination bound for `Krep`'s θ-derivative** (the `h_bound`/`bound_integrable` ingredient).
    For `|θ| ≤ R`, the derivative integrand is bounded by `m·cosh R·(|x₀|+|x₁|)·‖f x‖`, since `‖e^{iφ}‖ = 1`
    and `|sinh θ|, |cosh θ| ≤ cosh R`.  The bound is a continuous, compactly-supported (for such `f`)
    function of `x`, hence integrable — the domination the differentiation-under-the-integral needs. -/
theorem Krep_deriv_norm_bound (m : ℝ) (hm : 0 ≤ m) (f : V → ℂ) (x : V) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : |θ| ≤ R) :
    ‖(Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * f x‖
      ≤ m * Real.cosh R * (|x 0| + |x 1|) * ‖f x‖ := by
  have hexp1 : ‖Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hsinh : |Real.sinh θ| ≤ Real.cosh R := by
    rw [Real.abs_sinh]
    have h1 : Real.sinh |θ| ≤ Real.cosh |θ| := by
      have := Real.exp_pos (-|θ|); rw [Real.cosh_eq, Real.sinh_eq]; linarith
    have h2 : Real.cosh |θ| ≤ Real.cosh R := by
      rw [Real.cosh_abs]; exact Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hR])
    linarith
  have hcosh : |Real.cosh θ| ≤ Real.cosh R := by
    rw [abs_of_nonneg (Real.cosh_pos θ).le]
    exact Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hR])
  have hnorm : ‖(Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * f x‖
      = |m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ)| * ‖f x‖ := by
    rw [norm_mul, norm_mul, hexp1, one_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [abs_mul, abs_of_nonneg hm]
  have hg : |x 0 * Real.sinh θ - x 1 * Real.cosh θ| ≤ Real.cosh R * (|x 0| + |x 1|) := by
    calc |x 0 * Real.sinh θ - x 1 * Real.cosh θ|
        ≤ |x 0 * Real.sinh θ| + |x 1 * Real.cosh θ| := abs_sub _ _
      _ = |x 0| * |Real.sinh θ| + |x 1| * |Real.cosh θ| := by rw [abs_mul, abs_mul]
      _ ≤ |x 0| * Real.cosh R + |x 1| * Real.cosh R := by
          gcongr
      _ = Real.cosh R * (|x 0| + |x 1|) := by ring
  calc m * |x 0 * Real.sinh θ - x 1 * Real.cosh θ|
      ≤ m * (Real.cosh R * (|x 0| + |x 1|)) := mul_le_mul_of_nonneg_left hg hm
    _ = m * Real.cosh R * (|x 0| + |x 1|) := by ring

end QIQTH.Fock.StressTensor
