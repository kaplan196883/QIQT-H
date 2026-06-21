import QIQTH.Fock.StressTensor.NullStressFlux
import QIQTH.Fock.PauliJordan
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

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

/-- **Integrability of the domination bound** (`bound_integrable`).  For a continuous, compactly-supported
    test function `f`, the bound `m·cosh R·(|x₀|+|x₁|)·‖f x‖` is continuous and compactly-supported (it
    vanishes wherever `f` does), hence integrable. -/
theorem Krep_bound_integrable (m : ℝ) (f : V → ℂ) (hf : Continuous f)
    (hf_supp : HasCompactSupport f) (R : ℝ) :
    Integrable (fun x => m * Real.cosh R * (|x 0| + |x 1|) * ‖f x‖) := by
  have c1 : Continuous (fun x : V => |x 0| + |x 1|) :=
    (continuous_abs.comp (continuous_apply 0)).add (continuous_abs.comp (continuous_apply 1))
  have cont : Continuous (fun x : V => m * Real.cosh R * (|x 0| + |x 1|) * ‖f x‖) :=
    (continuous_const.mul c1).mul hf.norm
  exact cont.integrable_of_hasCompactSupport (hf_supp.norm.mul_left)

/-- **Integrability of the Cauchy-type dominator** `(c² + x²)⁻¹` (for `c > 0`), the function that bounds the
    horizon amplitude `‖horizonAmp m f x‖` (via `cosh(rapInv x) = (c²+x²)/(2cx)` and the `(cosh)⁻²` Schwartz
    decay).  Reduces to Mathlib's `integrable_inv_one_add_sq` by the domination
    `(c²+x²)⁻¹ ≤ (min(c²,1))⁻¹·(1+x²)⁻¹`. -/
theorem integrable_inv_const_sq_add {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) := by
  have hmin : (0 : ℝ) < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  refine (integrable_inv_one_add_sq.const_mul (min (c ^ 2) 1)⁻¹).mono'
    ((continuous_const.add (continuous_pow 2)).inv₀
      (fun x => (show (0 : ℝ) < c ^ 2 + x ^ 2 by positivity).ne')).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_inv]
  gcongr
  nlinarith [min_le_left (c ^ 2) 1, min_le_right (c ^ 2) 1, sq_nonneg x, hmin]

/-- **Integrability of the squared Cauchy dominator** `((c²+x²)⁻¹)²` (for `c > 0`), bounding `‖horizonAmp‖²`
    (hence the self-adjoint `∫ conj A · A`).  Reduces to `integrable_inv_const_sq_add` by
    `((c²+x²)⁻¹)² ≤ (c²)⁻¹·(c²+x²)⁻¹`. -/
theorem integrable_inv_const_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => ((c ^ 2 + x ^ 2)⁻¹) ^ 2) := by
  refine ((integrable_inv_const_sq_add hc).const_mul (c ^ 2)⁻¹).mono'
    (((continuous_const.add (continuous_pow 2)).inv₀
      (fun x => (show (0 : ℝ) < c ^ 2 + x ^ 2 by positivity).ne')).pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  have h1 : (c ^ 2 + x ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
    gcongr
    nlinarith [sq_nonneg x]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **★★★ `Krep` is rapidity-differentiable** (the last regularity gate of the Route B target).  For a
    continuous, compactly-supported test function `f`, `θ ↦ Krep m f θ` is differentiable, with
    `kd θ₀ = (1/√2)·∫ e^{−i η(p_m(θ₀),x)}·(−i·m(x₀ sinh θ₀ − x₁ cosh θ₀))·f(x) dx` — i.e. `kd = Krep'`.
    Differentiation under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the pointwise
    derivative `Krep_integrand_hasDerivAt`, the domination `Krep_deriv_norm_bound`, and the integrability
    `Krep_bound_integrable`.  This discharges the `hkd` hypothesis of `stressFluxKK_eq_neg_rapMom`. -/
theorem Krep_hasDerivAt (m : ℝ) (hm : 0 ≤ m) (f : V → ℂ) (hf : Continuous f)
    (hf_supp : HasCompactSupport f) (θ₀ : ℝ) :
    HasDerivAt (fun θ => Krep m f θ)
      ((1 / Real.sqrt 2 : ℂ) * ∫ x, (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ₀) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ₀ - x 1 * Real.cosh θ₀) : ℝ) : ℂ))) * f x) θ₀ := by
  set F : ℝ → V → ℂ := fun θ x =>
    Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * f x with hF
  set F' : ℝ → V → ℂ := fun θ x =>
    (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
      * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * f x with hF'
  have hmD : ∀ θ, Continuous (fun x : V => (minkowskiDot (massShell m θ) x : ℝ)) := by
    intro θ
    simp only [minkowskiDot]
    exact (continuous_const.mul (continuous_apply 0)).sub (continuous_const.mul (continuous_apply 1))
  have hexpc : ∀ θ, Continuous (fun x : V =>
      Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))) := fun θ =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hmD θ)))
  have hFcont : ∀ θ, Continuous (F θ) := fun θ => (hexpc θ).mul hf
  have hF'cont : ∀ θ, Continuous (F' θ) := by
    intro θ
    refine ((hexpc θ).mul ?_).mul hf
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul
      (((continuous_apply 0).mul continuous_const).sub ((continuous_apply 1).mul continuous_const))))
  have hbnd : ∀ᵐ x ∂(volume : Measure V), ∀ θ ∈ Metric.ball θ₀ 1,
      ‖F' θ x‖ ≤ m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖f x‖ := by
    refine Filter.Eventually.of_forall (fun x θ hθ => ?_)
    have hθR : |θ| ≤ |θ₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      calc |θ| = |θ₀ + (θ - θ₀)| := by ring_nf
        _ ≤ |θ₀| + |θ - θ₀| := abs_add_le _ _
        _ ≤ |θ₀| + 1 := by linarith
    exact Krep_deriv_norm_bound m hm f x (by positivity) hθR
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := θ₀)
    (F := F) (F' := F') (bound := fun x => m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖f x‖)
    (Metric.ball_mem_nhds θ₀ one_pos)
    (Filter.Eventually.of_forall (fun θ => (hFcont θ).aestronglyMeasurable))
    ((hFcont θ₀).integrable_of_hasCompactSupport (hf_supp.mul_left))
    ((hF'cont θ₀).aestronglyMeasurable) hbnd
    (Krep_bound_integrable m f hf hf_supp (|θ₀| + 1))
    (Filter.Eventually.of_forall (fun x θ _ => Krep_integrand_hasDerivAt m f x θ))
  have hKrep : (fun θ => Krep m f θ) = fun θ => (1 / Real.sqrt 2 : ℂ) * ∫ x, F θ x := by
    funext θ; simp only [hF, Krep, minkowskiFourier]
  rw [hKrep]
  exact key.2.const_mul (1 / Real.sqrt 2 : ℂ)

/-- **★★★ `Krep` is rapidity-differentiable for a SCHWARTZ test function** — the class-unifying companion of
    `Krep_hasDerivAt`.  Same proof (differentiation under the integral, same explicit `kd = Krep'`), but the two
    integrabilities use the Schwartz tail instead of compact support: `F θ₀ = e^{iη}·f` is `L¹` because
    `‖e^{iη}‖ = 1` and `f` is integrable, and the dominating bound `m·cosh R·(|x₀|+|x₁|)·‖f x‖` is `L¹` because
    `(|x₀|+|x₁|)‖f x‖ ≤ 2‖x‖‖f x‖` (`integrable_pow_mul`).  Lets `hkd` be discharged on the SAME Schwartz class
    as `hA`/`hAd`/`hff`. -/
theorem schwartz_Krep_hasDerivAt (m : ℝ) (hm : 0 ≤ m) (f : SchwartzMap V ℂ) (θ₀ : ℝ) :
    HasDerivAt (fun θ => Krep m (⇑f) θ)
      ((1 / Real.sqrt 2 : ℂ) * ∫ x, (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ₀) x : ℝ) : ℂ))
        * (-Complex.I * ((m * (x 0 * Real.sinh θ₀ - x 1 * Real.cosh θ₀) : ℝ) : ℂ))) * (⇑f) x) θ₀ := by
  set F : ℝ → V → ℂ := fun θ x =>
    Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ)) * (⇑f) x with hF
  set F' : ℝ → V → ℂ := fun θ x =>
    (Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
      * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ))) * (⇑f) x with hF'
  have hfc : Continuous (⇑f) := f.continuous
  have hnorm1 : ∀ t : ℝ, ‖Complex.exp (-Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hmD : ∀ θ, Continuous (fun x : V => (minkowskiDot (massShell m θ) x : ℝ)) := by
    intro θ; simp only [minkowskiDot]
    exact (continuous_const.mul (continuous_apply 0)).sub (continuous_const.mul (continuous_apply 1))
  have hexpc : ∀ θ, Continuous (fun x : V =>
      Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))) := fun θ =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hmD θ)))
  have hFcont : ∀ θ, Continuous (F θ) := fun θ => (hexpc θ).mul hfc
  have hF'cont : ∀ θ, Continuous (F' θ) := by
    intro θ
    refine ((hexpc θ).mul ?_).mul hfc
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul
      (((continuous_apply 0).mul continuous_const).sub ((continuous_apply 1).mul continuous_const))))
  have hbnd : ∀ᵐ x ∂(volume : Measure V), ∀ θ ∈ Metric.ball θ₀ 1,
      ‖F' θ x‖ ≤ m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖ := by
    refine Filter.Eventually.of_forall (fun x θ hθ => ?_)
    have hθR : |θ| ≤ |θ₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      calc |θ| = |θ₀ + (θ - θ₀)| := by ring_nf
        _ ≤ |θ₀| + |θ - θ₀| := abs_add_le _ _
        _ ≤ |θ₀| + 1 := by linarith
    exact Krep_deriv_norm_bound m hm (⇑f) x (by positivity) hθR
  have hFint : Integrable (F θ₀) := by
    refine (f.integrable).norm.mono' (hFcont θ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => le_of_eq ?_))
    simp only [hF, norm_mul, hnorm1, one_mul]
  have hbound_int : Integrable
      (fun x : V => m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖) := by
    refine ((f.integrable_pow_mul volume 1).const_mul
      (2 * m * Real.cosh (|θ₀| + 1))).mono'
      (((continuous_const.mul ((continuous_abs.comp (continuous_apply 0)).add
        (continuous_abs.comp (continuous_apply 1)))).mul hfc.norm).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hx2 : |x 0| + |x 1| ≤ 2 * ‖x‖ := by
      have h0 := norm_le_pi_norm x 0
      have h1 := norm_le_pi_norm x 1
      rw [Real.norm_eq_abs] at h0 h1
      linarith
    calc m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖
        ≤ m * Real.cosh (|θ₀| + 1) * (2 * ‖x‖) * ‖(⇑f) x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 (by positivity)) (norm_nonneg _)
      _ = 2 * m * Real.cosh (|θ₀| + 1) * (‖x‖ ^ 1 * ‖(⇑f) x‖) := by rw [pow_one]; ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := θ₀)
    (F := F) (F' := F') (bound := fun x => m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖)
    (Metric.ball_mem_nhds θ₀ one_pos)
    (Filter.Eventually.of_forall (fun θ => (hFcont θ).aestronglyMeasurable))
    hFint ((hF'cont θ₀).aestronglyMeasurable) hbnd hbound_int
    (Filter.Eventually.of_forall (fun x θ _ => Krep_integrand_hasDerivAt m (⇑f) x θ))
  have hKrep : (fun θ => Krep m (⇑f) θ) = fun θ => (1 / Real.sqrt 2 : ℂ) * ∫ x, F θ x := by
    funext θ; simp only [hF, Krep, minkowskiFourier]
  rw [hKrep]
  exact key.2.const_mul (1 / Real.sqrt 2 : ℂ)

/-- **★★ `Krep ∈ C¹`: the rapidity derivative `kd = Krep'` is continuous** (`f` Schwartz, `m ≥ 0`).  Since
    `deriv (Krep m f) θ = (1/√2)·∫ F θ x` (the `schwartz_Krep_hasDerivAt` value), continuity follows from
    `continuousAt_of_dominated`: the integrand `F` is continuous in `θ` (a.e. `x`), and on each ball
    `|θ − θ₀| < 1` it is dominated by the integrable Schwartz bound `m·cosh(|θ₀|+1)·(|x₀|+|x₁|)·‖f x‖`
    (`Krep_deriv_norm_bound` + `integrable_pow_mul`).  Needed for the continuity of `deriv (horizonAmp)`
    (the `hdAc` gate). -/
theorem schwartz_Krep_deriv_continuous {m : ℝ} (hm : 0 ≤ m) (f : SchwartzMap V ℂ) :
    Continuous (deriv (fun θ => Krep m (⇑f) θ)) := by
  set F : ℝ → V → ℂ := fun θ x =>
    Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) x : ℝ) : ℂ))
      * (-Complex.I * ((m * (x 0 * Real.sinh θ - x 1 * Real.cosh θ) : ℝ) : ℂ)) * (⇑f) x with hF
  have hderiv_eq : deriv (fun θ => Krep m (⇑f) θ)
      = fun θ => (1 / Real.sqrt 2 : ℂ) * ∫ x, F θ x := by
    funext θ; rw [hF]; exact (schwartz_Krep_hasDerivAt m hm f θ).deriv
  rw [hderiv_eq]
  refine Continuous.const_mul ?_ _
  rw [continuous_iff_continuousAt]
  intro θ₀
  have hFcont_x : ∀ θ, Continuous (F θ) := by
    intro θ; simp only [hF, minkowskiDot, massShell_zero, massShell_one]; fun_prop
  have hFcont_θ : ∀ x, Continuous (fun θ => F θ x) := by
    intro x; simp only [hF, minkowskiDot, massShell_zero, massShell_one]; fun_prop
  have hbound_int : Integrable
      (fun x : V => m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖) := by
    refine ((f.integrable_pow_mul volume 1).const_mul (2 * m * Real.cosh (|θ₀| + 1))).mono'
      (((continuous_const.mul ((continuous_abs.comp (continuous_apply 0)).add
        (continuous_abs.comp (continuous_apply 1)))).mul f.continuous.norm).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hx2 : |x 0| + |x 1| ≤ 2 * ‖x‖ := by
      have h0 := norm_le_pi_norm x 0
      have h1 := norm_le_pi_norm x 1
      rw [Real.norm_eq_abs] at h0 h1
      linarith
    calc m * Real.cosh (|θ₀| + 1) * (|x 0| + |x 1|) * ‖(⇑f) x‖
        ≤ m * Real.cosh (|θ₀| + 1) * (2 * ‖x‖) * ‖(⇑f) x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 (by positivity)) (norm_nonneg _)
      _ = 2 * m * Real.cosh (|θ₀| + 1) * (‖x‖ ^ 1 * ‖(⇑f) x‖) := by rw [pow_one]; ring
  refine continuousAt_of_dominated
    (Filter.Eventually.of_forall (fun θ => (hFcont_x θ).aestronglyMeasurable))
    ?_ hbound_int (Filter.Eventually.of_forall (fun x => (hFcont_θ x).continuousAt))
  filter_upwards [Metric.ball_mem_nhds θ₀ one_pos] with θ hθ
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hθR : |θ| ≤ |θ₀| + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hθ
    calc |θ| = |θ₀ + (θ - θ₀)| := by ring_nf
      _ ≤ |θ₀| + |θ - θ₀| := abs_add_le _ _
      _ ≤ |θ₀| + 1 := by linarith
  rw [hF]
  exact Krep_deriv_norm_bound m hm (⇑f) x (by positivity) hθR

end QIQTH.Fock.StressTensor
