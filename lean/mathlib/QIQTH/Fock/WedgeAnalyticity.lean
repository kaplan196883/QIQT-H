/-
  Wedge-mode analyticity (Item A, Phase A1 of QIQT_GR_DISCHARGE_PLAN.md).

  The analytic continuation of the localized rapidity amplitude `Krep m f θ` to complex rapidity
  `ζ = θ + iλ`, toward the free-field Hardy-space proof of `StripKMSrvd(boostUnitary, 𝒦_W)` (the
  Bisognano–Wichmann KMS property). The engine is the complexified mass shell `p_m(ζ) = (m cosh ζ, m sinh ζ)`
  with the identity `p_m(θ+iπ) = −p_m(θ)`, and the wedge-damping bound `Re(−i·p_m(θ+iλ)·x) < 0` for
  `x ∈ rightWedge`, `0 < λ < π`.

  A1a (this file, first increment): the complexified objects (`minkowskiDotℂ`, `massShellℂ`, `KrepCont`) and
  their agreement with the real-rapidity `Krep` on the real axis.
-/
import QIQTH.Fock.Localization
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open MeasureTheory Complex

namespace QIQTH.Fock.WedgeAnalyticity

open QIQTH.Fock.Localization

/-- **Complex Minkowski pairing** `p · x = p₀x₀ − p₁x₁` for a complex momentum `p` and a real point `x`. -/
def minkowskiDotℂ (p : Fin 2 → ℂ) (x : V) : ℂ := p 0 * (x 0 : ℂ) - p 1 * (x 1 : ℂ)

/-- **The complexified mass shell** `p_m(ζ) = (m cosh ζ, m sinh ζ)` (`ℂ`-valued momentum at complex
    rapidity `ζ`). On the real axis it is `massShell m θ`; it satisfies `p_m(ζ+iπ) = −p_m(ζ)`. -/
def massShellℂ (m : ℝ) (ζ : ℂ) : Fin 2 → ℂ := ![(m : ℂ) * Complex.cosh ζ, (m : ℂ) * Complex.sinh ζ]

/-- **The analytically continued localized amplitude** `(K_ℂ f)(ζ) = 2^{-1/2}·∫ e^{−i·p_m(ζ)·x} f(x) dx`. -/
def KrepCont (m : ℝ) (f : V → ℂ) (ζ : ℂ) : ℂ :=
  (1 / Real.sqrt 2 : ℂ) * ∫ x, Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * f x

@[simp] theorem massShellℂ_zero (m : ℝ) (ζ : ℂ) : massShellℂ m ζ 0 = (m : ℂ) * Complex.cosh ζ := rfl

@[simp] theorem massShellℂ_one (m : ℝ) (ζ : ℂ) : massShellℂ m ζ 1 = (m : ℂ) * Complex.sinh ζ := rfl

/-- On the real axis the complexified mass shell is the real one: `p_m(θ) = massShell m θ` (cast to `ℂ`). -/
theorem massShellℂ_ofReal (m θ : ℝ) (i : Fin 2) :
    massShellℂ m (θ : ℂ) i = ((massShell m θ i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [massShellℂ, massShell, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.ofReal_mul]

/-- **The `iπ`-shift identity `p_m(ζ + iπ) = −p_m(ζ)`** — the analytic engine of the boundary conjugation
    `ψ_f(θ+iπ) = conj(ψ_f(θ))`. Immediate from `cosh(ζ+iπ)=−cosh ζ`, `sinh(ζ+iπ)=−sinh ζ`. -/
theorem massShellℂ_add_pi_I (m : ℝ) (ζ : ℂ) :
    massShellℂ m (ζ + (Real.pi : ℂ) * Complex.I) = -massShellℂ m ζ := by
  funext i
  fin_cases i <;>
    simp [massShellℂ, Complex.cosh_add_pi_mul_I, Complex.sinh_add_pi_mul_I, mul_neg]

/-- The complex pairing on the real-axis mass shell is the real pairing (cast to `ℂ`). -/
theorem minkowskiDotℂ_massShellℂ_ofReal (m θ : ℝ) (x : V) :
    minkowskiDotℂ (massShellℂ m (θ : ℂ)) x = ((minkowskiDot (massShell m θ) x : ℝ) : ℂ) := by
  simp only [minkowskiDotℂ, minkowskiDot, massShellℂ_ofReal, Complex.ofReal_sub, Complex.ofReal_mul]

/-- **A1a — real-axis agreement.** The continued amplitude restricted to the real rapidity axis is the
    original localized amplitude: `(K_ℂ f)(θ) = (K f)(θ)`. -/
theorem KrepCont_ofReal (m : ℝ) (f : V → ℂ) (θ : ℝ) :
    KrepCont m f (θ : ℂ) = Krep m f θ := by
  rw [KrepCont, Krep, minkowskiFourier]
  refine congrArg (fun z => (1 / Real.sqrt 2 : ℂ) * z)
    (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [minkowskiDotℂ_massShellℂ_ofReal]

/-! ### A1c — the wedge-damping bound -/

/-- `cosh(θ + iλ) = cosh θ cos λ + i sinh θ sin λ` (real/imaginary split at a complex rapidity). -/
theorem cosh_ofReal_add_ofReal_mul_I (θ lam : ℝ) :
    Complex.cosh ((θ : ℂ) + (lam : ℂ) * Complex.I)
      = ((Real.cosh θ * Real.cos lam : ℝ) : ℂ) + ((Real.sinh θ * Real.sin lam : ℝ) : ℂ) * Complex.I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

/-- `sinh(θ + iλ) = sinh θ cos λ + i cosh θ sin λ`. -/
theorem sinh_ofReal_add_ofReal_mul_I (θ lam : ℝ) :
    Complex.sinh ((θ : ℂ) + (lam : ℂ) * Complex.I)
      = ((Real.sinh θ * Real.cos lam : ℝ) : ℂ) + ((Real.cosh θ * Real.sin lam : ℝ) : ℂ) * Complex.I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

/-- **A1c — the wedge-damping bound.** For `m ≥ 0`, `x` in the right wedge, and `0 ≤ λ ≤ π`, the
    analytic-continuation kernel has norm `≤ 1`:
    `‖exp(−i·p_m(θ+iλ)·x)‖ = exp(m sinλ·(sinhθ·x₀ − coshθ·x₁)) ≤ 1`,
    because `coshθ·x₁ − sinhθ·x₀ = ½e^θ(x₁−x₀)+½e^{−θ}(x₁+x₀) > 0` on `rightWedge` and `sinλ ≥ 0`. -/
theorem norm_kernel_le_one {m : ℝ} (hm : 0 ≤ m) {x : V} (hx1 : 0 < x 1 - x 0) (hx2 : 0 < x 1 + x 0)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamπ : lam ≤ Real.pi) (θ : ℝ) :
    ‖Complex.exp (-Complex.I *
      minkowskiDotℂ (massShellℂ m ((θ : ℂ) + (lam : ℂ) * Complex.I)) x)‖ ≤ 1 := by
  rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_le_exp]
  have hre : (-Complex.I *
      minkowskiDotℂ (massShellℂ m ((θ : ℂ) + (lam : ℂ) * Complex.I)) x).re
      = m * Real.sin lam * (Real.sinh θ * x 0 - Real.cosh θ * x 1) := by
    simp only [minkowskiDotℂ, massShellℂ_zero, massShellℂ_one, cosh_ofReal_add_ofReal_mul_I,
      sinh_ofReal_add_ofReal_mul_I, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  have hsin : 0 ≤ Real.sin lam := Real.sin_nonneg_of_nonneg_of_le_pi hlam0 hlamπ
  have hwedge : 0 < Real.cosh θ * x 1 - Real.sinh θ * x 0 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    nlinarith [mul_pos (Real.exp_pos θ) hx1, mul_pos (Real.exp_pos (-θ)) hx2]
  nlinarith [mul_nonneg (mul_nonneg hm hsin) (le_of_lt hwedge)]

/-! ### A1b — holomorphy of the continued amplitude (pointwise ζ-derivative of the kernel) -/

/-- The analytic-continuation **kernel** `K(ζ, x) = exp(−i·p_m(ζ)·x)`. -/
def kernel (m : ℝ) (x : V) (ζ : ℂ) : ℂ :=
  Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x)

/-- The `ζ`-derivative of the complex pairing `p_m(ζ)·x = m coshζ·x₀ − m sinhζ·x₁` is
    `m sinhζ·x₀ − m coshζ·x₁`. -/
theorem hasDerivAt_minkowskiDotℂ_massShellℂ (m : ℝ) (x : V) (ζ : ℂ) :
    HasDerivAt (fun ζ => minkowskiDotℂ (massShellℂ m ζ) x)
      ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ) - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)) ζ := by
  have h0 : HasDerivAt (fun ζ => (m : ℂ) * Complex.cosh ζ * (x 0 : ℂ))
      ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)) ζ :=
    ((Complex.hasDerivAt_cosh ζ).const_mul (m : ℂ)).mul_const (x 0 : ℂ)
  have h1 : HasDerivAt (fun ζ => (m : ℂ) * Complex.sinh ζ * (x 1 : ℂ))
      ((m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)) ζ :=
    ((Complex.hasDerivAt_sinh ζ).const_mul (m : ℂ)).mul_const (x 1 : ℂ)
  exact h0.sub h1

/-- **A1b (pointwise).** For each `x`, the kernel `ζ ↦ K(ζ,x)` is complex-differentiable everywhere, with
    `dK/dζ = K(ζ,x)·(−i·(m sinhζ·x₀ − m coshζ·x₁))` — the chain rule through `exp`. So for each fixed `x`
    the integrand is entire in the rapidity parameter (the per-`x` half of the dominated-convergence
    holomorphy argument). -/
theorem hasDerivAt_kernel (m : ℝ) (x : V) (ζ : ℂ) :
    HasDerivAt (kernel m x)
      (kernel m x ζ * (-Complex.I * ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)
        - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)))) ζ := by
  have hin : HasDerivAt (fun ζ => -Complex.I * minkowskiDotℂ (massShellℂ m ζ) x)
      (-Complex.I * ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)
        - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ))) ζ :=
    (hasDerivAt_minkowskiDotℂ_massShellℂ m x ζ).const_mul (-Complex.I)
  exact (Complex.hasDerivAt_exp _).comp ζ hin

/-- The integrand-derivative value `K'(ζ,x) = K(ζ,x)·(−i·(m sinhζ·x₀ − m coshζ·x₁))`. -/
def kernelDeriv (m : ℝ) (x : V) (ζ : ℂ) : ℂ :=
  kernel m x ζ * (-Complex.I * ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)
    - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)))

/-- The full integrand `ζ ↦ K(ζ,x)·f(x)` is complex-differentiable, derivative `K'(ζ,x)·f(x)`
    (the `h_diff` ingredient for the dominated parametric-derivative assembly). -/
theorem hasDerivAt_kernel_mul (m : ℝ) (f : V → ℂ) (x : V) (ζ : ℂ) :
    HasDerivAt (fun ζ => kernel m x ζ * f x) (kernelDeriv m x ζ * f x) ζ :=
  (hasDerivAt_kernel m x ζ).mul_const (f x)

/-- The kernel is continuous in `x` (for fixed `ζ`) — gives `ae`-strong-measurability of the integrand. -/
theorem continuous_kernel_in_x (m : ℝ) (ζ : ℂ) : Continuous (fun x : V => kernel m x ζ) := by
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1)))

/-- `‖exp z‖ ≤ e^{‖z‖}` and `‖exp(−z)‖ ≤ e^{‖z‖}` (from `‖exp z‖ = e^{Re z}` and `±Re z ≤ ‖z‖`). -/
theorem norm_exp_le_exp_norm (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (RCLike.re_le_norm z)

theorem norm_exp_neg_le_exp_norm (z : ℂ) : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
  have h := norm_exp_le_exp_norm (-z)
  rwa [norm_neg] at h

/-- `‖cosh ζ‖ ≤ e^{‖ζ‖}` (crude growth bound from `cosh ζ = (e^ζ + e^{−ζ})/2`). -/
theorem norm_cosh_le (ζ : ℂ) : ‖Complex.cosh ζ‖ ≤ Real.exp ‖ζ‖ := by
  have key : ‖Complex.cosh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := by
    simp only [Complex.cosh, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]; gcongr; exact norm_add_le _ _
  calc ‖Complex.cosh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := key
    _ ≤ (Real.exp ‖ζ‖ + Real.exp ‖ζ‖) / 2 := by
        gcongr; exacts [norm_exp_le_exp_norm ζ, norm_exp_neg_le_exp_norm ζ]
    _ = Real.exp ‖ζ‖ := by ring

/-- `‖sinh ζ‖ ≤ e^{‖ζ‖}` (crude growth bound from `sinh ζ = (e^ζ − e^{−ζ})/2`). -/
theorem norm_sinh_le (ζ : ℂ) : ‖Complex.sinh ζ‖ ≤ Real.exp ‖ζ‖ := by
  have key : ‖Complex.sinh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := by
    simp only [Complex.sinh, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]; gcongr; exact norm_sub_le _ _
  calc ‖Complex.sinh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := key
    _ ≤ (Real.exp ‖ζ‖ + Real.exp ‖ζ‖) / 2 := by
        gcongr; exacts [norm_exp_le_exp_norm ζ, norm_exp_neg_le_exp_norm ζ]
    _ = Real.exp ‖ζ‖ := by ring

/-- A bound for a term `(m·c)·a − (m·s)·b` with `‖c‖,‖s‖ ≤ e^r`: `≤ |m|·e^r·(|a|+|b|)`. Used for both the
    pairing `p_m(ζ)·x` (`c,s = cosh,sinh`) and its `ζ`-derivative (`c,s = sinh,cosh`). -/
theorem norm_term_le {r : ℝ} (m : ℝ) {c s : ℂ} (hc : ‖c‖ ≤ Real.exp r) (hs : ‖s‖ ≤ Real.exp r)
    (a b : ℝ) :
    ‖(m : ℂ) * c * (a : ℂ) - (m : ℂ) * s * (b : ℂ)‖ ≤ |m| * Real.exp r * (|a| + |b|) := by
  calc ‖(m : ℂ) * c * (a : ℂ) - (m : ℂ) * s * (b : ℂ)‖
      ≤ ‖(m : ℂ) * c * (a : ℂ)‖ + ‖(m : ℂ) * s * (b : ℂ)‖ := norm_sub_le _ _
    _ = |m| * ‖c‖ * |a| + |m| * ‖s‖ * |b| := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |m| * Real.exp r * (|a| + |b|) := by
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg m) (abs_nonneg a)) (sub_nonneg.mpr hc),
          mul_nonneg (mul_nonneg (abs_nonneg m) (abs_nonneg b)) (sub_nonneg.mpr hs)]

/-- `‖K(ζ,x)‖ ≤ exp(|m|·e^{‖ζ‖}·(|x₀|+|x₁|))` (kernel growth bound; `‖exp(−i·D)‖ ≤ exp‖D‖`, `‖D‖` bound). -/
theorem norm_kernel_le (m : ℝ) (x : V) (ζ : ℂ) :
    ‖kernel m x ζ‖ ≤ Real.exp (|m| * Real.exp ‖ζ‖ * (|x 0| + |x 1|)) := by
  refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  simp only [minkowskiDotℂ, massShellℂ_zero, massShellℂ_one]
  exact norm_term_le m (norm_cosh_le ζ) (norm_sinh_le ζ) (x 0) (x 1)

/-- `‖K'(ζ,x)‖ ≤ exp(B)·B` with `B = |m|·e^{‖ζ‖}·(|x₀|+|x₁|)` (the integrand-derivative growth bound). -/
theorem norm_kernelDeriv_le (m : ℝ) (x : V) (ζ : ℂ) :
    ‖kernelDeriv m x ζ‖ ≤ Real.exp (|m| * Real.exp ‖ζ‖ * (|x 0| + |x 1|))
      * (|m| * Real.exp ‖ζ‖ * (|x 0| + |x 1|)) := by
  rw [kernelDeriv, norm_mul]
  have hpoly : ‖-Complex.I * ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)
      - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ))‖ ≤ |m| * Real.exp ‖ζ‖ * (|x 0| + |x 1|) := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_term_le m (norm_sinh_le ζ) (norm_cosh_le ζ) (x 0) (x 1)
  exact mul_le_mul (norm_kernel_le m x ζ) hpoly (norm_nonneg _) (Real.exp_pos _).le

/-- The integrand-derivative is continuous in `x` (for fixed `ζ`) — gives measurability. -/
theorem continuous_kernelDeriv_in_x (m : ℝ) (ζ : ℂ) :
    Continuous (fun x : V => kernelDeriv m x ζ) := by
  refine (continuous_kernel_in_x m ζ).mul (continuous_const.mul ?_)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1)))

/-- **A1b-ii-β — holomorphy of `KrepCont`.** For `f` continuous with compact support, `ζ ↦ KrepCont m f ζ`
    is complex-differentiable at every `ζ₀`, with derivative `(1/√2)·∫ K'(ζ₀,x)·f(x)`. Proven by the
    dominated parametric-derivative theorem (𝕜 = ℂ): the per-`x` derivative is `hasDerivAt_kernel_mul`, and
    the ball-domination uses `norm_kernelDeriv_le` + the compact bound `‖x‖ ≤ M` on `tsupport f`. -/
theorem hasDerivAt_KrepCont (m : ℝ) {f : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (ζ₀ : ℂ) :
    HasDerivAt (KrepCont m f) ((1 / Real.sqrt 2 : ℂ) * ∫ x, kernelDeriv m x ζ₀ * f x) ζ₀ := by
  obtain ⟨M, hM⟩ := hfc.isBounded.exists_norm_le
  set C : ℝ := Real.exp (|m| * Real.exp (‖ζ₀‖ + 1) * (M + M))
    * (|m| * Real.exp (‖ζ₀‖ + 1) * (M + M)) with hCdef
  have hbound : ∀ᵐ x ∂(volume : Measure V), ∀ ζ ∈ Metric.ball ζ₀ 1,
      ‖kernelDeriv m x ζ * f x‖ ≤ C * ‖f x‖ := by
    refine Filter.Eventually.of_forall fun x ζ hζ => ?_
    rw [norm_mul]
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hxsupp : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hfx)
      have hxM : ‖x‖ ≤ M := hM x hxsupp
      have hx0 : |x 0| ≤ M := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x 0).trans hxM
      have hx1 : |x 1| ≤ M := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x 1).trans hxM
      have hζR : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
        have hd : ‖ζ - ζ₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hζ
        have ht : ‖ζ‖ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := by
          calc ‖ζ‖ = ‖ζ₀ + (ζ - ζ₀)‖ := by congr 1; ring
            _ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
        linarith
      refine mul_le_mul_of_nonneg_right ((norm_kernelDeriv_le m x ζ).trans ?_) (norm_nonneg _)
      have hB : |m| * Real.exp ‖ζ‖ * (|x 0| + |x 1|) ≤ |m| * Real.exp (‖ζ₀‖ + 1) * (M + M) := by
        gcongr
      exact mul_le_mul (Real.exp_le_exp.mpr hB) hB (by positivity) (Real.exp_pos _).le
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure V))
    (F := fun ζ x => kernel m x ζ * f x) (F' := fun ζ x => kernelDeriv m x ζ * f x)
    (bound := fun x => C * ‖f x‖) (s := Metric.ball ζ₀ 1) (x₀ := ζ₀)
    (Metric.ball_mem_nhds ζ₀ one_pos)
    (Filter.Eventually.of_forall fun ζ =>
      ((continuous_kernel_in_x m ζ).mul hf).aestronglyMeasurable)
    (((continuous_kernel_in_x m ζ₀).mul hf).integrable_of_hasCompactSupport (hfc.mul_left))
    ((continuous_kernelDeriv_in_x m ζ₀).mul hf).aestronglyMeasurable
    hbound
    ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul C)
    (Filter.Eventually.of_forall fun x ζ _ => hasDerivAt_kernel_mul m f x ζ)
  exact key.2.const_mul (1 / Real.sqrt 2 : ℂ)

/-- **A1b — `KrepCont m f` is entire** for `f` continuous with compact support. -/
theorem differentiable_KrepCont (m : ℝ) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : Differentiable ℂ (KrepCont m f) :=
  fun ζ₀ => (hasDerivAt_KrepCont m hf hfc ζ₀).differentiableAt

/-! ### A3 — the `iπ` boundary conjugation (the KMS bottom edge) -/

/-- The kernel's `iπ`-boundary conjugation: `K(θ+iπ, x) = conj(K(θ, x))`. Engine: `p_m(θ+iπ) = −p_m(θ)`
    and `p_m(θ)·x` real, so `exp(−i·(−p_m(θ)·x)) = conj(exp(−i·p_m(θ)·x))`. -/
theorem kernel_add_pi_I (m : ℝ) (x : V) (θ : ℝ) :
    kernel m x ((θ : ℂ) + (Real.pi : ℂ) * Complex.I) = (starRingEnd ℂ) (kernel m x (θ : ℂ)) := by
  rw [kernel, kernel, ← Complex.exp_conj]
  congr 1
  have hneg : minkowskiDotℂ (massShellℂ m ((θ : ℂ) + (Real.pi : ℂ) * Complex.I)) x
      = -minkowskiDotℂ (massShellℂ m (θ : ℂ)) x := by
    rw [massShellℂ_add_pi_I]; simp only [minkowskiDotℂ, Pi.neg_apply]; ring
  rw [hneg, minkowskiDotℂ_massShellℂ_ofReal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **A3 — boundary conjugation of the continued amplitude.** For *real* `f`,
    `ψ_f(θ+iπ) = conj(ψ_f(θ))` (`= conj(Krep m f θ)`). This is the relation that turns the top edge
    `⟪η, V_t ξ⟫` into the KMS bottom edge `⟪V_t ξ, η⟫`. -/
theorem KrepCont_add_pi_I (m : ℝ) {f : V → ℂ} (hf : ∀ x, (starRingEnd ℂ) (f x) = f x) (θ : ℝ) :
    KrepCont m f ((θ : ℂ) + (Real.pi : ℂ) * Complex.I) = (starRingEnd ℂ) (Krep m f θ) := by
  rw [← KrepCont_ofReal m f θ, KrepCont, KrepCont, map_mul]
  congr 1
  · simp
  · rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, hf]
    congr 1
    exact kernel_add_pi_I m x θ

/-! ### A2 (partial) — the uniform sup-bound on the strip -/

/-- **A2 (sup-bound).** On the strip `0 ≤ λ ≤ π`, for `f` (continuous, compact support) supported in the right
    wedge, the analytic continuation is bounded by the `L¹` norm of `f`:
    `‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)·∫‖f‖`. Immediate from the wedge-damping bound `‖K(ζ,x)‖ ≤ 1`
    (`norm_kernel_le_one`) pushed through the integral. (This is the `L^∞`-on-strip half of the `H²(S_π)`
    bound; the `L²`-in-`θ` decay — extending the real-axis `cosh⁻²` estimates to the strip — remains.) -/
theorem norm_KrepCont_le {m : ℝ} (hm : 0 ≤ m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ x, f x ≠ 0 → 0 < x 1 - x 0 ∧ 0 < x 1 + x 0)
    {θ lam : ℝ} (hlam0 : 0 ≤ lam) (hlamπ : lam ≤ Real.pi) :
    ‖KrepCont m f ((θ : ℂ) + (lam : ℂ) * Complex.I)‖ ≤ (1 / Real.sqrt 2) * ∫ x, ‖f x‖ := by
  have hsqrt : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [KrepCont, norm_mul, hsqrt]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ x, kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I) * f x‖
      ≤ ∫ x, ‖kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I) * f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (hf.norm.integrable_of_hasCompactSupport hfc.norm) (Filter.Eventually.of_forall fun x => ?_)
        simp only [norm_mul]
        by_cases hfx : f x = 0
        · simp [hfx]
        · obtain ⟨hx1, hx2⟩ := hsupp x hfx
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_kernel_le_one hm hx1 hx2 hlam0 hlamπ θ)

/-- `θ²/8 ≤ cosh θ` — a crude quadratic lower bound (`cosh θ ≥ e^{|θ|}/2 ≥ (1+|θ|/2)²/2 ≥ θ²/8`),
    the comparison feeding the Gaussian domination of the wedge-mode strip decay. -/
theorem sq_div_eight_le_cosh (θ : ℝ) : θ ^ 2 / 8 ≤ Real.cosh θ := by
  have he : Real.exp |θ| ≤ 2 * Real.cosh θ := by
    rw [Real.cosh_eq]
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [Real.exp_pos θ, Real.exp_pos (-θ)]
  have h3 : 1 + |θ| / 2 ≤ Real.exp (|θ| / 2) := by
    have := Real.add_one_le_exp (|θ| / 2); linarith
  have hsqexp : Real.exp (|θ| / 2) ^ 2 = Real.exp |θ| := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : (1 + |θ| / 2) ^ 2 ≤ Real.exp |θ| := by
    rw [← hsqexp]; nlinarith [h3, abs_nonneg θ]
  nlinarith [he, h2, sq_abs θ, abs_nonneg θ]

/-- **A2 (decay building block).** `θ ↦ exp(−c·cosh θ)` is integrable over `ℝ` for `c > 0` — by Gaussian
    domination `exp(−c cosh θ) ≤ exp(−(c/8)·θ²)` (`sq_div_eight_le_cosh`). The `θ`-integrability that the
    interior-`λ` strip decay of the wedge mode reduces to (the damping exponent is `∝ −cosh θ`). -/
theorem integrable_exp_neg_const_mul_cosh {c : ℝ} (hc : 0 < c) :
    Integrable (fun θ : ℝ => Real.exp (-(c * Real.cosh θ))) := by
  refine (integrable_exp_neg_mul_sq (show (0 : ℝ) < c / 8 by positivity)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_div_eight_le_cosh θ, hc.le]

/-- **A2 — uniform wedge margin.** If `f` has compact support contained strictly in the (open) right wedge
    (`tsupport f ⊆ {x₁ > |x₀|}`), there is a uniform margin `δ > 0` with `δ ≤ x₁−x₀` and `δ ≤ x₁+x₀` on
    `tsupport f`. (Continuous positive function on a compact set attains a positive minimum.) This gives the
    uniform damping rate `coshθ·x₁ − sinhθ·x₀ ≥ δ·coshθ` powering the interior-`λ` `L²` decay. -/
theorem exists_wedge_margin {f : V → ℂ} (hfc : HasCompactSupport f)
    (hsupp : ∀ x ∈ tsupport f, 0 < x 1 - x 0 ∧ 0 < x 1 + x 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport f, δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0 := by
  rcases Set.eq_empty_or_nonempty (tsupport f) with he | hne
  · exact ⟨1, one_pos, fun x hx => by simp only [he, Set.mem_empty_iff_false] at hx⟩
  · have hg : ContinuousOn (fun x : V => min (x 1 - x 0) (x 1 + x 0)) (tsupport f) :=
      (Continuous.min (by fun_prop) (by fun_prop)).continuousOn
    obtain ⟨x₁, hx₁mem, hx₁min⟩ := IsCompact.exists_isMinOn hfc hne hg
    rw [isMinOn_iff] at hx₁min
    refine ⟨min (x₁ 1 - x₁ 0) (x₁ 1 + x₁ 0), ?_, fun y hy => ?_⟩
    · obtain ⟨ha, hb⟩ := hsupp x₁ hx₁mem; exact lt_min ha hb
    · exact ⟨(hx₁min y hy).trans (min_le_left _ _), (hx₁min y hy).trans (min_le_right _ _)⟩

/-- The exact kernel modulus on the strip: `‖K(θ+iλ,x)‖ = exp(m sinλ·(sinhθ·x₀ − coshθ·x₁))`. -/
theorem norm_kernel_eq (m : ℝ) (x : V) (θ lam : ℝ) :
    ‖kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I)‖
      = Real.exp (m * Real.sin lam * (Real.sinh θ * x 0 - Real.cosh θ * x 1)) := by
  rw [kernel, Complex.norm_exp]
  congr 1
  simp only [minkowskiDotℂ, massShellℂ_zero, massShellℂ_one, cosh_ofReal_add_ofReal_mul_I,
    sinh_ofReal_add_ofReal_mul_I, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Pointwise strip-decay of the kernel.** For `x` with wedge margin `δ` (`δ ≤ x₁∓x₀`) and `0≤λ≤π`,
    `‖K(θ+iλ,x)‖ ≤ exp(−(m sinλ δ)·coshθ)` — double-exponential decay in `θ` for interior `λ`. -/
theorem norm_kernel_le_exp_decay {m : ℝ} (hm : 0 ≤ m) {x : V} {δ : ℝ}
    (hx1 : δ ≤ x 1 - x 0) (hx2 : δ ≤ x 1 + x 0) {θ lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamπ : lam ≤ Real.pi) :
    ‖kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I)‖
      ≤ Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ) := by
  rw [norm_kernel_eq]
  refine Real.exp_le_exp.mpr ?_
  have hsin : 0 ≤ Real.sin lam := Real.sin_nonneg_of_nonneg_of_le_pi hlam0 hlamπ
  have hwedge : δ * Real.cosh θ ≤ Real.cosh θ * x 1 - Real.sinh θ * x 0 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    nlinarith [mul_nonneg (Real.exp_pos θ).le (by linarith : (0 : ℝ) ≤ x 1 - x 0 - δ),
      mul_nonneg (Real.exp_pos (-θ)).le (by linarith : (0 : ℝ) ≤ x 1 + x 0 - δ)]
  nlinarith [mul_nonneg (mul_nonneg hm hsin) (by linarith : (0 : ℝ) ≤
    (Real.cosh θ * x 1 - Real.sinh θ * x 0) - δ * Real.cosh θ)]

/-- **A2 (step 1) — pointwise strip-decay of the continued amplitude.** For wedge-supported `f` (uniform
    margin `δ` via `exists_wedge_margin`) and `0≤λ≤π`,
    `‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)·(∫‖f‖)·exp(−(m sinλ δ)·coshθ)`. The decay factor (double-exponential in
    `θ` for interior `λ`) is what makes `KrepCont m f (·+iλ) ∈ L²`. -/
theorem norm_KrepCont_le_exp_decay {m : ℝ} (hm : 0 ≤ m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ}
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {θ lam : ℝ} (hlam0 : 0 ≤ lam) (hlamπ : lam ≤ Real.pi) :
    ‖KrepCont m f ((θ : ℂ) + (lam : ℂ) * Complex.I)‖
      ≤ 1 / Real.sqrt 2 * (∫ x, ‖f x‖) * Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ) := by
  have hsqrt : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [KrepCont, norm_mul, hsqrt, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ x, kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I) * f x‖
      ≤ ∫ x, ‖kernel m x ((θ : ℂ) + (lam : ℂ) * Complex.I) * f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ) * ‖f x‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul _)
          (Filter.Eventually.of_forall fun x => ?_)
        simp only [norm_mul]
        by_cases hfx : f x = 0
        · simp [hfx]
        · obtain ⟨hx1, hx2⟩ := hmargin x hfx
          exact mul_le_mul_of_nonneg_right
            (norm_kernel_le_exp_decay hm hx1 hx2 hlam0 hlamπ) (norm_nonneg _)
    _ = (∫ x, ‖f x‖) * Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ) := by
        rw [integral_const_mul]; ring

end QIQTH.Fock.WedgeAnalyticity
