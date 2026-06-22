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

/-- `‖cosh ζ‖ ≤ cosh(Re ζ)` (sharp real-part bound, `‖e^{±ζ}‖ = e^{±Re ζ}`). -/
theorem norm_cosh_le_cosh_re (ζ : ℂ) : ‖Complex.cosh ζ‖ ≤ Real.cosh ζ.re := by
  rw [Real.cosh_eq]
  calc ‖Complex.cosh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := by
        simp only [Complex.cosh, norm_div]
        rw [show ‖(2 : ℂ)‖ = 2 by simp]; gcongr; exact norm_add_le _ _
    _ = (Real.exp ζ.re + Real.exp (-ζ.re)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

/-- `‖sinh ζ‖ ≤ cosh(Re ζ)` (sharp real-part bound). -/
theorem norm_sinh_le_cosh_re (ζ : ℂ) : ‖Complex.sinh ζ‖ ≤ Real.cosh ζ.re := by
  rw [Real.cosh_eq]
  calc ‖Complex.sinh ζ‖ ≤ (‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖) / 2 := by
        simp only [Complex.sinh, norm_div]
        rw [show ‖(2 : ℂ)‖ = 2 by simp]; gcongr; exact norm_sub_le _ _
    _ = (Real.exp ζ.re + Real.exp (-ζ.re)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

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

/-- **`deriv (KrepCont m f)` is continuous** (entire ⟹ analytic ⟹ deriv analytic ⟹ continuous,
    `AnalyticAt.deriv`). The measurability ingredient (`hF'_meas`) for the dominated-derivative theorem. -/
theorem continuous_deriv_KrepCont (m : ℝ) {f : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (deriv (KrepCont m f)) :=
  Differentiable.continuous fun z => ((differentiable_KrepCont m hf hfc).analyticAt z).deriv.differentiableAt

/-- The rapidity-derivative of `KrepCont m f` as an integral: `(K_ℂ f)'(ζ) = 2^{-1/2}·∫ K'(ζ,x)·f(x) dx`. -/
theorem deriv_KrepCont_eq (m : ℝ) {f : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (ζ : ℂ) :
    deriv (KrepCont m f) ζ = (1 / Real.sqrt 2 : ℂ) * ∫ x, kernelDeriv m x ζ * f x :=
  (hasDerivAt_KrepCont m hf hfc ζ).deriv

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

/-- `|sinh θ| ≤ cosh θ` (`cosh±sinh = e^{±θ} ≥ 0`). -/
theorem abs_sinh_le_cosh (θ : ℝ) : |Real.sinh θ| ≤ Real.cosh θ := by
  rw [abs_le]
  exact ⟨by nlinarith [Real.cosh_eq θ, Real.sinh_eq θ, Real.exp_pos θ],
    by nlinarith [Real.cosh_eq θ, Real.sinh_eq θ, Real.exp_pos (-θ)]⟩

/-- `cosh s + |sinh s| = e^{|s|}` and `cosh s − |sinh s| = e^{−|s|}`. -/
theorem cosh_add_abs_sinh (s : ℝ) : Real.cosh s + |Real.sinh s| = Real.exp |s| := by
  rcases abs_cases s with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hmono : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    have hsnn : (0 : ℝ) ≤ Real.sinh s := by nlinarith [Real.sinh_eq s]
    rw [h1, abs_of_nonneg hsnn]; nlinarith [Real.cosh_eq s, Real.sinh_eq s]
  · have hmono : Real.exp s ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
    have hsnp : Real.sinh s ≤ 0 := by nlinarith [Real.sinh_eq s]
    rw [h1, abs_of_nonpos hsnp]; nlinarith [Real.cosh_eq s, Real.sinh_eq s]

theorem cosh_sub_abs_sinh (s : ℝ) : Real.cosh s - |Real.sinh s| = Real.exp (-|s|) := by
  rcases abs_cases s with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hmono : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    have hsnn : (0 : ℝ) ≤ Real.sinh s := by nlinarith [Real.sinh_eq s]
    rw [h1, abs_of_nonneg hsnn]; nlinarith [Real.cosh_eq s, Real.sinh_eq s]
  · have hmono : Real.exp s ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
    have hsnp : Real.sinh s ≤ 0 := by nlinarith [Real.sinh_eq s]
    rw [h1, abs_of_nonpos hsnp, neg_neg, sub_neg_eq_add]
    nlinarith [Real.cosh_eq s, Real.sinh_eq s]

/-- **`cosh(θ+s) ≤ e^{|s|}·cosh θ`** (shift upper bound — makes the shifting-peak strip decay uniform). -/
theorem cosh_add_le_exp_abs_mul (θ s : ℝ) : Real.cosh (θ + s) ≤ Real.exp |s| * Real.cosh θ := by
  rw [Real.cosh_add, ← cosh_add_abs_sinh s]
  have hkey : Real.sinh θ * Real.sinh s ≤ Real.cosh θ * |Real.sinh s| :=
    calc Real.sinh θ * Real.sinh s ≤ |Real.sinh θ * Real.sinh s| := le_abs_self _
      _ = |Real.sinh θ| * |Real.sinh s| := abs_mul _ _
      _ ≤ Real.cosh θ * |Real.sinh s| := by gcongr; exact abs_sinh_le_cosh θ
  nlinarith [hkey]

/-- **`e^{−|s|}·cosh θ ≤ cosh(θ+s)`** (shift lower bound). -/
theorem exp_neg_abs_mul_le_cosh_add (θ s : ℝ) : Real.exp (-|s|) * Real.cosh θ ≤ Real.cosh (θ + s) := by
  rw [Real.cosh_add, ← cosh_sub_abs_sinh s]
  have hkey : -(Real.cosh θ * |Real.sinh s|) ≤ Real.sinh θ * Real.sinh s :=
    calc -(Real.cosh θ * |Real.sinh s|) ≤ -(|Real.sinh θ| * |Real.sinh s|) := by
          gcongr; exact abs_sinh_le_cosh θ
      _ = -|Real.sinh θ * Real.sinh s| := by rw [abs_mul]
      _ ≤ Real.sinh θ * Real.sinh s := neg_abs_le _
  nlinarith [hkey]

/-- `|θ| ≤ cosh θ` (from `cosh θ ≥ e^{|θ|}/2` and `e^{|θ|} ≥ 2|θ|`, `Real.two_mul_le_exp`). -/
theorem abs_le_cosh (θ : ℝ) : |θ| ≤ Real.cosh θ := by
  have he : Real.exp |θ| ≤ 2 * Real.cosh θ := by
    rw [Real.cosh_eq]
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [Real.exp_pos θ, Real.exp_pos (-θ)]
  have h2 : 2 * |θ| ≤ Real.exp |θ| := Real.two_mul_le_exp
  linarith

/-- `0 < sin(−π·w)` for `−1 < w < 0` (the decay rate `σ = sin(−π·Im z)` is positive on the open strip). -/
theorem sin_neg_pi_mul_pos {w : ℝ} (h0 : -1 < w) (h1 : w < 0) : 0 < Real.sin (-(Real.pi * w)) :=
  Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- **The shifted `cosh·exp` made uniform.** For `|s| ≤ S`, `0 < c₀ ≤ c`:
    `cosh(θ+s)·exp(−c·cosh(θ+s)) ≤ e^S·cosh θ·exp(−c₀·e^{−S}·cosh θ)`. The core estimate that turns the
    shifting-peak strip decay (`s = πRe z` over a `z`-ball) into a `z`-uniform integrable-in-`θ` bound. -/
theorem cosh_shift_exp_le {θ s c c₀ S : ℝ} (hS : |s| ≤ S) (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    Real.cosh (θ + s) * Real.exp (-(c * Real.cosh (θ + s)))
      ≤ Real.exp S * Real.cosh θ * Real.exp (-(c₀ * Real.exp (-S) * Real.cosh θ)) := by
  have hupper : Real.cosh (θ + s) ≤ Real.exp S * Real.cosh θ :=
    (cosh_add_le_exp_abs_mul θ s).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hS) (Real.cosh_pos θ).le)
  have he' : Real.exp (-S) * Real.cosh θ ≤ Real.cosh (θ + s) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith : (-S : ℝ) ≤ -|s|))
      (Real.cosh_pos θ).le).trans (exp_neg_abs_mul_le_cosh_add θ s)
  have h1 : c₀ * Real.exp (-S) * Real.cosh θ ≤ c * Real.cosh (θ + s) :=
    calc c₀ * Real.exp (-S) * Real.cosh θ = c₀ * (Real.exp (-S) * Real.cosh θ) := by ring
      _ ≤ c₀ * Real.cosh (θ + s) := mul_le_mul_of_nonneg_left he' hc₀.le
      _ ≤ c * Real.cosh (θ + s) := mul_le_mul_of_nonneg_right hcc (Real.cosh_pos _).le
  have hexp : Real.exp (-(c * Real.cosh (θ + s)))
      ≤ Real.exp (-(c₀ * Real.exp (-S) * Real.cosh θ)) := Real.exp_le_exp.mpr (by linarith)
  calc Real.cosh (θ + s) * Real.exp (-(c * Real.cosh (θ + s)))
      ≤ Real.exp S * Real.cosh θ * Real.exp (-(c₀ * Real.exp (-S) * Real.cosh θ)) :=
        mul_le_mul hupper hexp (Real.exp_pos _).le (by positivity)

/-- **The `h_bound` core estimate.** A `cosh(θ+s)·exp(−c·cosh(θ+s))`-decaying factor (`na`) times a bounded
    factor (`nb ≤ Cb`), made `z`-uniform: `na·nb ≤ Cd·Cb·(e^S·cosh θ·exp(−c₀·e^{−S}·cosh θ))`. Both terms of
    the `kmsFun` integrand `z`-derivative reduce to this (via the four factor bounds + `cosh_shift_exp_le`). -/
theorem prod_norm_bound_cosh_shift {na nb Cd Cb c c₀ S s θ : ℝ}
    (hna : na ≤ Cd * (Real.cosh (θ + s) * Real.exp (-(c * Real.cosh (θ + s)))))
    (hnb : nb ≤ Cb) (hnb0 : 0 ≤ nb) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hS : |s| ≤ S) (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    na * nb ≤ Cd * Cb * (Real.exp S * Real.cosh θ * Real.exp (-(c₀ * Real.exp (-S) * Real.cosh θ))) :=
  calc na * nb ≤ Cd * (Real.cosh (θ + s) * Real.exp (-(c * Real.cosh (θ + s)))) * Cb :=
        mul_le_mul hna hnb hnb0 (mul_nonneg hCd (by positivity))
    _ = Cd * Cb * (Real.cosh (θ + s) * Real.exp (-(c * Real.cosh (θ + s)))) := by ring
    _ ≤ Cd * Cb * (Real.exp S * Real.cosh θ * Real.exp (-(c₀ * Real.exp (-S) * Real.cosh θ))) :=
        mul_le_mul_of_nonneg_left (cosh_shift_exp_le hS hc₀ hcc) (mul_nonneg hCd hCb)

/-- **A2 (derivative-decay building block).** `s ↦ cosh s·exp(−c·cosh s)` is integrable over `ℝ` for `c > 0`.
    The integrand-derivative bound (`‖kernelDeriv‖ ≲ cosh(s)·exp(−c·cosh s)`, the `cosh` polynomial factor
    against the double-exponential damping) reduces to this. Via `cosh s ≤ (1/c)·exp((c/2)cosh s)`
    (`Real.two_mul_le_exp`) ⟹ `cosh s·exp(−c cosh s) ≤ (1/c)·exp(−(c/2)cosh s)`. -/
theorem integrable_cosh_mul_exp_neg_const_mul_cosh {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.cosh s * Real.exp (-(c * Real.cosh s))) := by
  refine ((integrable_exp_neg_const_mul_cosh (show (0 : ℝ) < c / 2 by positivity)).const_mul
    (1 / c)).mono' (by fun_prop) (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hc' : c * Real.cosh s ≤ Real.exp ((c / 2) * Real.cosh s) := by
    nlinarith [Real.two_mul_le_exp (x := (c / 2) * Real.cosh s)]
  have hcosh_le : Real.cosh s ≤ (1 / c) * Real.exp ((c / 2) * Real.cosh s) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]; linarith [hc']
  calc Real.cosh s * Real.exp (-(c * Real.cosh s))
      ≤ (1 / c) * Real.exp ((c / 2) * Real.cosh s) * Real.exp (-(c * Real.cosh s)) :=
        mul_le_mul_of_nonneg_right hcosh_le (Real.exp_pos _).le
    _ = (1 / c) * Real.exp (-(c / 2 * Real.cosh s)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

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

/-- The exact kernel modulus at a **general** complex `ζ`: `‖K(ζ,x)‖ = exp(m sin(Im ζ)·(sinh(Re ζ)·x₀ −
    cosh(Re ζ)·x₁))` (rewrite `ζ = Re ζ + i·Im ζ`, then `norm_kernel_eq`). -/
theorem norm_kernel_eq' (m : ℝ) (x : V) (ζ : ℂ) :
    ‖kernel m x ζ‖
      = Real.exp (m * Real.sin ζ.im * (Real.sinh ζ.re * x 0 - Real.cosh ζ.re * x 1)) := by
  conv_lhs => rw [← Complex.re_add_im ζ]
  exact norm_kernel_eq m x ζ.re ζ.im

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

/-- **Pointwise strip-decay of the kernel at a general `ζ`** (`0 ≤ Im ζ ≤ π`, `x` with wedge margin `δ`):
    `‖K(ζ,x)‖ ≤ exp(−(m sin(Im ζ) δ)·cosh(Re ζ))`. The general-`ζ` form powering the `z`-derivative decay. -/
theorem norm_kernel_le_exp_decay' {m : ℝ} (hm : 0 ≤ m) {x : V} {δ : ℝ}
    (hx1 : δ ≤ x 1 - x 0) (hx2 : δ ≤ x 1 + x 0) {ζ : ℂ} (him0 : 0 ≤ ζ.im) (himπ : ζ.im ≤ Real.pi) :
    ‖kernel m x ζ‖ ≤ Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re) := by
  rw [norm_kernel_eq']
  refine Real.exp_le_exp.mpr ?_
  have hsin : 0 ≤ Real.sin ζ.im := Real.sin_nonneg_of_nonneg_of_le_pi him0 himπ
  have hwedge : δ * Real.cosh ζ.re ≤ Real.cosh ζ.re * x 1 - Real.sinh ζ.re * x 0 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    nlinarith [mul_nonneg (Real.exp_pos ζ.re).le (by linarith : (0 : ℝ) ≤ x 1 - x 0 - δ),
      mul_nonneg (Real.exp_pos (-ζ.re)).le (by linarith : (0 : ℝ) ≤ x 1 + x 0 - δ)]
  nlinarith [mul_nonneg (mul_nonneg hm hsin) (by linarith : (0 : ℝ) ≤
    (Real.cosh ζ.re * x 1 - Real.sinh ζ.re * x 0) - δ * Real.cosh ζ.re)]

/-- **Pointwise strip-decay of `kernelDeriv` at a general `ζ`**: `‖K'(ζ,x)‖ ≤ exp(−c·cosh(Re ζ))·|m|·
    cosh(Re ζ)·(|x₀|+|x₁|)` (`c = m sin(Im ζ) δ`). Kernel decay (`norm_kernel_le_exp_decay'`) × `poly` bound
    (`‖poly‖ ≤ |m|·cosh(Re ζ)·(|x₀|+|x₁|)` via `norm_sinh/cosh_le_cosh_re`). The `cosh(Re ζ)` polynomial factor
    against the double-exponential damping — the integrand of the `z`-derivative domination. -/
theorem norm_kernelDeriv_le_exp_decay {m : ℝ} (hm : 0 ≤ m) {x : V} {δ : ℝ}
    (hx1 : δ ≤ x 1 - x 0) (hx2 : δ ≤ x 1 + x 0) {ζ : ℂ} (him0 : 0 ≤ ζ.im) (himπ : ζ.im ≤ Real.pi) :
    ‖kernelDeriv m x ζ‖ ≤ Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re)
      * (|m| * Real.cosh ζ.re * (|x 0| + |x 1|)) := by
  rw [kernelDeriv, norm_mul]
  have hpoly : ‖-Complex.I * ((m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)
      - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ))‖ ≤ |m| * Real.cosh ζ.re * (|x 0| + |x 1|) := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    calc ‖(m : ℂ) * Complex.sinh ζ * (x 0 : ℂ) - (m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)‖
        ≤ ‖(m : ℂ) * Complex.sinh ζ * (x 0 : ℂ)‖ + ‖(m : ℂ) * Complex.cosh ζ * (x 1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = |m| * ‖Complex.sinh ζ‖ * |x 0| + |m| * ‖Complex.cosh ζ‖ * |x 1| := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |m| * Real.cosh ζ.re * |x 0| + |m| * Real.cosh ζ.re * |x 1| := by
          gcongr
          exacts [norm_sinh_le_cosh_re ζ, norm_cosh_le_cosh_re ζ]
      _ = |m| * Real.cosh ζ.re * (|x 0| + |x 1|) := by ring
  exact mul_le_mul (norm_kernel_le_exp_decay' hm hx1 hx2 him0 himπ) hpoly (norm_nonneg _)
    (Real.exp_pos _).le

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

/-- **Pointwise strip-decay of `deriv KrepCont`.** For wedge-supported `f` (margin `δ`) and `0≤Im ζ≤π`,
    `‖deriv(KrepCont m f) ζ‖ ≤ (1/√2)·|m|·cosh(Re ζ)·exp(−c·cosh(Re ζ))·∫(|x₀|+|x₁|)‖f‖` (`c=m sin(Im ζ)δ`).
    The `z`-derivative norm bound: `cosh(Re ζ)·exp(−c·cosh(Re ζ))` decay (× a finite constant). -/
theorem norm_deriv_KrepCont_le_exp_decay {m : ℝ} (hm : 0 ≤ m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ}
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {ζ : ℂ} (him0 : 0 ≤ ζ.im) (himπ : ζ.im ≤ Real.pi) :
    ‖deriv (KrepCont m f) ζ‖ ≤ 1 / Real.sqrt 2 * (|m| * Real.cosh ζ.re
      * Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re) * ∫ x, (|x 0| + |x 1|) * ‖f x‖) := by
  have hsqrt : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [deriv_KrepCont_eq m hf hfc, norm_mul, hsqrt]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ x, kernelDeriv m x ζ * f x‖
      ≤ ∫ x, ‖kernelDeriv m x ζ * f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|m| * Real.cosh ζ.re * Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re))
          * ((|x 0| + |x 1|) * ‖f x‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (((((by fun_prop : Continuous fun x : V => |x 0| + |x 1|).mul hf.norm)).integrable_of_hasCompactSupport
            (hfc.norm.mul_left)).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
        simp only [norm_mul]
        by_cases hfx : f x = 0
        · simp [hfx]
        · obtain ⟨hx1, hx2⟩ := hmargin x hfx
          calc ‖kernelDeriv m x ζ‖ * ‖f x‖
              ≤ (Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re)
                  * (|m| * Real.cosh ζ.re * (|x 0| + |x 1|))) * ‖f x‖ :=
                mul_le_mul_of_nonneg_right (norm_kernelDeriv_le_exp_decay hm hx1 hx2 him0 himπ)
                  (norm_nonneg _)
            _ = (|m| * Real.cosh ζ.re * Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re))
                  * ((|x 0| + |x 1|) * ‖f x‖) := by ring
    _ = |m| * Real.cosh ζ.re * Real.exp (-(m * Real.sin ζ.im * δ) * Real.cosh ζ.re)
          * ∫ x, (|x 0| + |x 1|) * ‖f x‖ := by rw [integral_const_mul]

/-- **Pointwise strip-decay of `KrepCont` at a general complex argument `w`** (`0≤Im w≤π`, `f` wedge-supported):
    `‖KrepCont m f w‖ ≤ (1/√2)·(∫‖f‖)·exp(−(m sin(Im w)δ)·cosh(Re w))` (rewrite `w = Re w + i·Im w`). -/
theorem norm_KrepCont_le_exp_decay_gen {m : ℝ} (hm : 0 ≤ m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ}
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {w : ℂ} (him0 : 0 ≤ w.im) (himπ : w.im ≤ Real.pi) :
    ‖KrepCont m f w‖
      ≤ 1 / Real.sqrt 2 * (∫ x, ‖f x‖) * Real.exp (-(m * Real.sin w.im * δ) * Real.cosh w.re) := by
  conv_lhs => rw [← Complex.re_add_im w]
  exact norm_KrepCont_le_exp_decay hm hf hfc hmargin him0 himπ

/-- **Plain `KrepCont` bound on the closed strip** (`0≤Im w≤π`, `f` wedge-supported with `δ≥0`):
    `‖KrepCont m f w‖ ≤ (1/√2)·∫‖f‖` — the strip-damping factor `exp(−(m sin(Im w)δ)·cosh(Re w)) ≤ 1` since its
    exponent is `≤ 0` (`sin(Im w)≥0` on `[0,π]`, `m,δ,cosh ≥ 0`). This `Re`-uniform constant bound is what makes
    the truncated KMS integral trivially bounded on the closed strip (no log-blowup). -/
theorem norm_KrepCont_le_const {m : ℝ} (hm : 0 ≤ m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {w : ℂ} (him0 : 0 ≤ w.im) (himπ : w.im ≤ Real.pi) :
    ‖KrepCont m f w‖ ≤ 1 / Real.sqrt 2 * (∫ x, ‖f x‖) := by
  refine (norm_KrepCont_le_exp_decay_gen hm hf hfc hmargin him0 himπ).trans ?_
  have hsin : 0 ≤ Real.sin w.im := Real.sin_nonneg_of_nonneg_of_le_pi him0 himπ
  have hexp : Real.exp (-(m * Real.sin w.im * δ) * Real.cosh w.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnn : 0 ≤ m * Real.sin w.im * δ * Real.cosh w.re := by positivity
    nlinarith [hnn]
  have hC : 0 ≤ 1 / Real.sqrt 2 * ∫ x, ‖f x‖ := by
    have : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg (fun x => norm_nonneg _)
    positivity
  calc 1 / Real.sqrt 2 * (∫ x, ‖f x‖) * Real.exp (-(m * Real.sin w.im * δ) * Real.cosh w.re)
      ≤ 1 / Real.sqrt 2 * (∫ x, ‖f x‖) * 1 := by
        exact mul_le_mul_of_nonneg_left hexp hC
    _ = 1 / Real.sqrt 2 * (∫ x, ‖f x‖) := mul_one _

/-- **A2 (step 2) — interior-`λ` `L²` membership.** For `m > 0`, wedge-supported `f` (continuous, compact
    support, `tsupport f ⊆` open wedge), and `λ ∈ (0,π)`, the strip slice `θ ↦ KrepCont m f (θ+iλ)` is in
    `L²(dθ)`. Proven by **pointwise domination** `‖KrepCont(θ+iλ)‖ ≤ C·exp(−c·coshθ)`
    (`norm_KrepCont_le_exp_decay`, `c = m sinλ δ > 0`) against the `L²` function `C·exp(−c·cosh)` (whose square
    `C²·exp(−2c·cosh)` is integrable, `integrable_exp_neg_const_mul_cosh`). **No Minkowski integral inequality.** -/
theorem memLp_KrepCont_strip {m : ℝ} (hm : 0 < m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ x ∈ tsupport f, 0 < x 1 - x 0 ∧ 0 < x 1 + x 0)
    {lam : ℝ} (hlam : 0 < lam) (hlamπ : lam < Real.pi) :
    MemLp (fun θ : ℝ => KrepCont m f ((θ : ℂ) + (lam : ℂ) * Complex.I)) 2 volume := by
  obtain ⟨δ, hδ, hmargin⟩ := exists_wedge_margin hfc hsupp
  have hsinpos : 0 < Real.sin lam := Real.sin_pos_of_pos_of_lt_pi hlam hlamπ
  have hcpos : 0 < m * Real.sin lam * δ := mul_pos (mul_pos hm hsinpos) hδ
  set C : ℝ := 1 / Real.sqrt 2 * ∫ x, ‖f x‖ with hCdef
  have hint : Integrable
      (fun θ : ℝ => C ^ 2 * Real.exp (-(2 * (m * Real.sin lam * δ)) * Real.cosh θ)) := by
    have heq : (fun θ : ℝ => C ^ 2 * Real.exp (-(2 * (m * Real.sin lam * δ)) * Real.cosh θ))
        = (fun θ : ℝ => C ^ 2 * Real.exp (-(2 * (m * Real.sin lam * δ) * Real.cosh θ))) := by
      funext θ; rw [neg_mul]
    rw [heq]
    exact (integrable_exp_neg_const_mul_cosh
      (by positivity : (0 : ℝ) < 2 * (m * Real.sin lam * δ))).const_mul _
  have hgmemLp : MemLp
      (fun θ : ℝ => C * Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ)) 2 volume := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have hsqeq : (fun θ : ℝ => (C * Real.exp (-(m * Real.sin lam * δ) * Real.cosh θ)) ^ 2)
        = (fun θ : ℝ => C ^ 2 * Real.exp (-(2 * (m * Real.sin lam * δ)) * Real.cosh θ)) := by
      funext θ; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [hsqeq]; exact hint
  refine hgmemLp.mono'
    (((differentiable_KrepCont m hf hfc).continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ => ?_)
  have hb := norm_KrepCont_le_exp_decay (θ := θ) hm.le hf hfc
    (fun x hx => hmargin x (subset_tsupport f (Function.mem_support.mpr hx))) hlam.le hlamπ.le
  rwa [← hCdef] at hb

/-- **A2 (step 2′) — affine-argument `L²` membership.** For `m > 0`, wedge-supported `f`, and a complex
    offset `c₀` with `Im c₀ ∈ (0,π)`, the slice `θ ↦ KrepCont m f (θ + c₀)` is in `L²(dθ)`. The argument's
    imaginary part is the constant `Im c₀` (strip-interior ⟹ `sin > 0`), and the real part is `θ + Re c₀`;
    pointwise domination by `C·exp(−c·cosh(θ+Re c₀))` (`norm_KrepCont_le_exp_decay_gen`) against the `L²`
    translate of `C·exp(−c·cosh)` (`measurePreserving_add_right`). Generalizes `memLp_KrepCont_strip` to a
    real shift of the strip slice — the form the two boost-KMS slices take. -/
theorem memLp_KrepCont_affine {m : ℝ} (hm : 0 < m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {c₀ : ℂ} (hc0 : 0 < c₀.im) (hc0π : c₀.im < Real.pi) :
    MemLp (fun θ : ℝ => KrepCont m f ((θ : ℂ) + c₀)) 2 volume := by
  have hsinpos : 0 < Real.sin c₀.im := Real.sin_pos_of_pos_of_lt_pi hc0 hc0π
  set C : ℝ := 1 / Real.sqrt 2 * ∫ x, ‖f x‖ with hCdef
  have hbound0 : MemLp (fun s : ℝ => C * Real.exp (-(m * Real.sin c₀.im * δ) * Real.cosh s)) 2 volume := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have hsqeq : (fun s : ℝ => (C * Real.exp (-(m * Real.sin c₀.im * δ) * Real.cosh s)) ^ 2)
        = (fun s : ℝ => C ^ 2 * Real.exp (-(2 * (m * Real.sin c₀.im * δ) * Real.cosh s))) := by
      funext s; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [hsqeq]
    exact (integrable_exp_neg_const_mul_cosh
      (by positivity : (0 : ℝ) < 2 * (m * Real.sin c₀.im * δ))).const_mul _
  have hbound : MemLp
      (fun θ : ℝ => C * Real.exp (-(m * Real.sin c₀.im * δ) * Real.cosh (θ + c₀.re))) 2 volume := by
    have h := hbound0.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) c₀.re)
    simpa [Function.comp_def] using h
  refine hbound.mono'
    (((differentiable_KrepCont m hf hfc).continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ => ?_)
  have hb := norm_KrepCont_le_exp_decay_gen hm.le hf hfc hmargin (w := (θ : ℂ) + c₀)
    (by simpa using hc0.le) (by simpa using hc0π.le)
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re, zero_add] at hb
  rwa [← hCdef] at hb

/-- **`KrepCont` is additive in the test function** (for continuous compact-support `f₁,f₂`): the defining
    integral `∫ kernel·f` is linear in `f`, with each `kernel·fᵢ` integrable (continuous, compact support). The
    sesquilinearity foundation for threading `stripKMSrvd_pair` over the wedge span. -/
theorem KrepCont_add (m : ℝ) {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) (ζ : ℂ) :
    KrepCont m (f₁ + f₂) ζ = KrepCont m f₁ ζ + KrepCont m f₂ ζ := by
  have hint : ∀ {h : V → ℂ}, Continuous h → HasCompactSupport h →
      Integrable (fun x => Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * h x) := by
    intro h hc hcs
    exact ((continuous_kernel_in_x m ζ).mul hc).integrable_of_hasCompactSupport hcs.mul_left
  rw [KrepCont, KrepCont, KrepCont, ← mul_add, ← integral_add (hint hf₁ hf₁c) (hint hf₂ hf₂c)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * (f₁ + f₂) x
    = Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * f₁ x
      + Complex.exp (-Complex.I * minkowskiDotℂ (massShellℂ m ζ) x) * f₂ x
  rw [Pi.add_apply]; ring

/-- **`Krep` (real axis) is additive in the test function** — `KrepCont_add` at real argument (`KrepCont_ofReal`).
    Used for the `MemLp` closure of the wedge-test class under `+`/`−` in the span-closure threading. -/
theorem Krep_add (m : ℝ) {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) (θ : ℝ) :
    Krep m (f₁ + f₂) θ = Krep m f₁ θ + Krep m f₂ θ := by
  rw [← KrepCont_ofReal, ← KrepCont_ofReal, ← KrepCont_ofReal,
    KrepCont_add m hf₁ hf₁c hf₂ hf₂c (θ : ℂ)]

/-- **`Krep` (real axis) respects subtraction** — `Krep m (f₁−f₂) = Krep m f₁ − Krep m f₂` (from `Krep_add`). -/
theorem Krep_sub (m : ℝ) {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) (θ : ℝ) :
    Krep m (f₁ - f₂) θ = Krep m f₁ θ - Krep m f₂ θ := by
  have h : Krep m (f₁ - f₂ + f₂) θ = Krep m (f₁ - f₂) θ + Krep m f₂ θ :=
    Krep_add m (hf₁.sub hf₂) (hf₁c.sub hf₂c) hf₂ hf₂c θ
  have he : f₁ - f₂ + f₂ = f₁ := by ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [he] at h
  rw [h]; ring

/-- **`MemLp` closure under addition**: `MemLp (Krep m (f₁+f₂)) 2` from `MemLp (Krep m fᵢ) 2`, via
    `Krep_add` (`Krep(f₁+f₂)=Krep f₁+Krep f₂`) + `MemLp.add`. The additive companion of `memLp_Krep_sub`;
    together they make the nice one-particle vectors `{KrepL2 f}` closed under `±`, i.e. an ℝ-subspace. -/
theorem memLp_Krep_add {m : ℝ} {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume) :
    MemLp (Krep m (f₁ + f₂)) 2 volume := by
  have heq : Krep m (f₁ + f₂) = Krep m f₁ + Krep m f₂ := by
    funext θ; exact Krep_add m hf₁ hf₁c hf₂ hf₂c θ
  rw [heq]; exact hf₁L.add hf₂L

/-- **`MemLp` closure under subtraction**: `MemLp (Krep m (f₁−f₂)) 2` from `MemLp (Krep m fᵢ) 2`, via
    `Krep_sub` (`Krep(f₁−f₂)=Krep f₁−Krep f₂`) + `MemLp.sub`. -/
theorem memLp_Krep_sub {m : ℝ} {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume) :
    MemLp (Krep m (f₁ - f₂)) 2 volume := by
  have heq : Krep m (f₁ - f₂) = Krep m f₁ - Krep m f₂ := by
    funext θ; exact Krep_sub m hf₁ hf₁c hf₂ hf₂c θ
  rw [heq]; exact hf₁L.sub hf₂L

/-- **Affine-argument `L²` membership on the CLOSED strip** `Im c₀ ∈ [0,π]`. Extends `memLp_KrepCont_affine`
    to the two boundary heights: at `Im c₀ = 0` the slice is a real-axis translate `Krep m f(·+Re c₀)`
    (`KrepCont_ofReal`), at `Im c₀ = π` it is the conjugate `conj(Krep m f(·+Re c₀))` (`KrepCont_add_pi_I`,
    `MemLp.star`) — both in `L²` via the `MemLp (Krep m f) 2` hypothesis; the interior is `memLp_KrepCont_affine`.
    This supplies the edge `L²` slices needed to integrate the `kmsFun` integrand up to the boundary. -/
theorem memLp_KrepCont_affine_closed {m : ℝ} (hm : 0 < m) {f : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hfL : MemLp (Krep m f) 2 volume)
    {c₀ : ℂ} (hc0 : 0 ≤ c₀.im) (hc0π : c₀.im ≤ Real.pi) :
    MemLp (fun θ : ℝ => KrepCont m f ((θ : ℂ) + c₀)) 2 volume := by
  rcases eq_or_lt_of_le hc0 with heq0 | hlt0
  · have hfun : (fun θ : ℝ => KrepCont m f ((θ : ℂ) + c₀)) = fun θ : ℝ => Krep m f (θ + c₀.re) := by
      funext θ
      have harg : (θ : ℂ) + c₀ = ((θ + c₀.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [← heq0]
      rw [harg, KrepCont_ofReal]
    rw [hfun]
    simpa [Function.comp_def] using
      hfL.comp_measurePreserving (measurePreserving_add_right volume c₀.re)
  · rcases eq_or_lt_of_le hc0π with heqπ | hltπ
    · have hfun : (fun θ : ℝ => KrepCont m f ((θ : ℂ) + c₀))
          = fun θ : ℝ => (starRingEnd ℂ) (Krep m f (θ + c₀.re)) := by
        funext θ
        have harg : (θ : ℂ) + c₀ = ((θ + c₀.re : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp [heqπ, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
              Complex.ofReal_im, Complex.ofReal_re]
        rw [harg, KrepCont_add_pi_I m hfr]
      rw [hfun]
      have hT : MemLp (fun θ : ℝ => Krep m f (θ + c₀.re)) 2 volume := by
        simpa [Function.comp_def] using
          hfL.comp_measurePreserving (measurePreserving_add_right volume c₀.re)
      exact hT.star
    · exact memLp_KrepCont_affine hm hf hfc hδ hmargin hlt0 hltπ

end QIQTH.Fock.WedgeAnalyticity
