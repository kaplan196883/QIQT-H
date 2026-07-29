/-
  AnnulusGaussianBound — the SECOND brick of the C4c cutoff-parametrix far-field construction
  (docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md, the a₁ = R/6 endgame).

  THE ANNULUS EXPONENTIAL-SMALLNESS BOUND (the honest boundary — read it).
  Off the near ball (`rncRadialSq v ≥ a²`, an ANNULUS bounded away from the diagonal), the Gaussian
  decay `exp(−r²/(8t))` beats ANY inverse-time power `(1/t)^k`, UNIFORMLY in `t > 0`.  This is the
  analytic fact that controls the cutoff-DERIVATIVE terms of the C4c cutoff-parametrix residual:
  the cutoff `χ` is constant near the diagonal, so `∇χ`, `Δχ` are supported on the annulus where the
  base Gaussian is already exponentially small — small enough to swallow the residual's `1/t` factors.

  THE CRUX (elementary).  Write `x := rncRadialSq v / (8t) ≥ 0`.  On the annulus `rncRadialSq v ≥ a²`,
      `1/t = (rncRadialSq v)/(a² t) · (a²/rncRadialSq v) ≤ (8/a²)·x`,
  so `(1/t)^k ≤ (8/a²)^k · x^k`, and the single-term exp-series bound `x^k·e^{−x} ≤ k!` (C4a,
  `GaussianPolyBound.pow_mul_exp_neg_le_factorial`) gives
      `(1/t)^k · exp(−rncRadialSq v/(8t)) ≤ (8/a²)^k · k!`   — a CONSTANT, uniform in `t`.

  THE GAUSSIAN DEFINITIONS (exact, from `FlatHeatEquation` / `ResidueBound`).
    • `gaussDdim t v      = (√(4πt))⁻ⁿ · exp(−rncRadialSq v/(4t))`   (`gaussDdim_eq_exp`);
    • `gaussDdimWide t v  = (√(4πt))⁻ⁿ · exp(−rncRadialSq v/(8t))`   (SAME prefactor, WIDER exponent).
  Hence the ratio is EXACTLY `gaussDdim t v = exp(−rncRadialSq v/(8t)) · gaussDdimWide t v` — the
  shared prefactor `(√(4πt))⁻ⁿ` cancels, so NO `(√2)ⁿ` factor appears (contrast the width identity
  `gaussDdimWide_eq_scaled_gaussDdim`, which compares DIFFERENT times).

  Deliverables:
    • `invT_pow_exp_le` — the CORE elementary bound (F3/F2 crux):
        `(1/t)^k · exp(−r²/(8t)) ≤ (8/a²)^k · k!`  on the annulus `a² ≤ r²`, uniform in `t > 0`;
    • `gaussDdim_eq_wide_mul` — the ratio identity `gaussDdim t v = exp(−r²/(8t)) · gaussDdimWide t v`;
    • `invTpow_gaussDdim_le_gaussDdimWide` — ★ THE ANNULUS BRICK (F1):
        `(1/t)^k · gaussDdim t v ≤ ((8/a²)^k · k!) · gaussDdimWide t v`  on the annulus, uniform in `t`.

  ⚠ HONEST FLOOR = F1 (both `invT_pow_exp_le` AND `invTpow_gaussDdim_le_gaussDdimWide`, plus the ratio
  identity).  All hypotheses are genuine and load-bearing: `0 < a`, `0 < t`, and the ANNULUS
  hypothesis `a² ≤ rncRadialSq v` (WITHOUT which the bound FAILS — near the diagonal `r → 0` the
  Gaussian is `≈ 1` and cannot beat `(1/t)^k → ∞`).  This is the annulus (cutoff-derivative) input to
  the C4c far-field residual bound `residual_global_baseKernelW_of_gaussianCofactor` toward
  unconditional `a₁ = R/6`.  It is NOT the full C4c residual, NOT the Leibniz split, NOT `a₁ = R/6`.
  No axioms, no `sorry`, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.GaussianPolyBound
import QIQTH.ResidueBound
import QIQTH.ParametrixResidualBaseKernel

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.GaussianPolyBound QIQTH.ResidueBound
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-! ### The core elementary annulus bound — Gaussian beats any inverse-time power. -/

/-- **THE CORE ANNULUS BOUND (exp beats poly).**  On the annulus `a² ≤ rncRadialSq v` (bounded away
    from the diagonal), for any inverse-time power `k` and any `t > 0`,
        `(1/t)^k · exp(−rncRadialSq v/(8t)) ≤ (8/a²)^k · k!`,
    a CONSTANT uniform in `t`.  Route: with `x := rncRadialSq v/(8t) ≥ 0`, the annulus hypothesis
    gives `1/t ≤ (8/a²)·x` (since `rncRadialSq v ≥ a²`), hence `(1/t)^k ≤ (8/a²)^k·x^k`, and the
    single-term exp-series bound `x^k·e^{−x} ≤ k!` (`pow_mul_exp_neg_le_factorial`, C4a) absorbs the
    Gaussian.  The `a² ≤ rncRadialSq v` hypothesis is load-bearing: near the diagonal the bound is
    false. -/
theorem invT_pow_exp_le (k : ℕ) (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : 0 < t)
    {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / t) ^ k * Real.exp (-(rncRadialSq v) / (8 * t)) ≤ (8 / a ^ 2) ^ k * (k.factorial : ℝ) := by
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hr : 0 ≤ rncRadialSq v := rncRadialSq_nonneg v
  have h8t : (0 : ℝ) < 8 * t := by positivity
  have hx : (0 : ℝ) ≤ rncRadialSq v / (8 * t) := div_nonneg hr h8t.le
  -- normalize the exponent `-(r²)/(8t)` to `-(r²/(8t))` to match `pow_mul_exp_neg_le_factorial`
  rw [neg_div]
  -- the annulus key: `1/t ≤ (8/a²)·x`
  have h1t : 1 / t ≤ (8 / a ^ 2) * (rncRadialSq v / (8 * t)) := by
    have heq : (8 / a ^ 2) * (rncRadialSq v / (8 * t)) = rncRadialSq v / (a ^ 2 * t) := by
      field_simp
    rw [heq, div_le_div_iff₀ ht (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hv ht.le]
  -- raise to the `k`-th power
  have hpow : (1 / t) ^ k ≤ ((8 / a ^ 2) * (rncRadialSq v / (8 * t))) ^ k :=
    pow_le_pow_left₀ (by positivity) h1t k
  calc (1 / t) ^ k * Real.exp (-(rncRadialSq v / (8 * t)))
      ≤ ((8 / a ^ 2) * (rncRadialSq v / (8 * t))) ^ k * Real.exp (-(rncRadialSq v / (8 * t))) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (8 / a ^ 2) ^ k
          * ((rncRadialSq v / (8 * t)) ^ k * Real.exp (-(rncRadialSq v / (8 * t)))) := by
        rw [mul_pow]; ring
    _ ≤ (8 / a ^ 2) ^ k * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial hx k) (by positivity)

/-! ### The Gaussian ratio identity (shared prefactor cancels — no `(√2)ⁿ`). -/

/-- **The ratio identity** `gaussDdim t v = exp(−rncRadialSq v/(8t)) · gaussDdimWide t v` (`0 < t`).
    Both Gaussians carry the SAME prefactor `(√(4πt))⁻ⁿ`, so it cancels in the ratio and the extra
    factor is exactly the wide-exponent Gaussian `exp(−r²/(8t))` (from `−r²/(4t) = −r²/(8t) −
    r²/(8t)`).  No `(√2)ⁿ` appears (unlike `gaussDdimWide_eq_scaled_gaussDdim`, which compares
    different TIMES). -/
theorem gaussDdim_eq_wide_mul {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdim t v = Real.exp (-(rncRadialSq v) / (8 * t)) * gaussDdimWide t v := by
  have htne : t ≠ 0 := ht.ne'
  rw [gaussDdim_eq_exp, gaussDdimWide]
  have hsplit : Real.exp (-(rncRadialSq v) / (8 * t)) * Real.exp (-(rncRadialSq v) / (8 * t))
      = Real.exp (-(rncRadialSq v) / (4 * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n * Real.exp (-(rncRadialSq v) / (4 * t))
      = ((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n
          * (Real.exp (-(rncRadialSq v) / (8 * t)) * Real.exp (-(rncRadialSq v) / (8 * t))) := by
        rw [hsplit]
    _ = Real.exp (-(rncRadialSq v) / (8 * t))
          * (((Real.sqrt (4 * Real.pi * t))⁻¹) ^ n * Real.exp (-(rncRadialSq v) / (8 * t))) := by
        ring

/-! ### ★ THE ANNULUS BRICK — `(1/t)^k · gaussDdim ≤ C · gaussDdimWide` uniformly in `t`. -/

/-- **★ THE ANNULUS EXPONENTIAL-SMALLNESS BRICK (F1).**  On the annulus `a² ≤ rncRadialSq v`, the
    inverse-time-power-times-narrow-Gaussian is dominated by a CONSTANT times the WIDE Gaussian,
    uniformly in `t > 0`:
        `(1/t)^k · gaussDdim t v ≤ ((8/a²)^k · k!) · gaussDdimWide t v`.
    Proof: the ratio identity `gaussDdim t v = exp(−r²/(8t))·gaussDdimWide t v` splits off the extra
    wide-exponent factor, and the core annulus bound `invT_pow_exp_le` absorbs `(1/t)^k·exp(−r²/(8t))`
    into the constant `(8/a²)^k·k!`; `gaussDdimWide ≥ 0` carries the multiplication.  This controls the
    cutoff-derivative (annulus-supported) terms of the C4c cutoff-parametrix residual.  The annulus
    hypothesis is load-bearing (fails near the diagonal). -/
theorem invTpow_gaussDdim_le_gaussDdimWide (k : ℕ) (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : 0 < t)
    {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / t) ^ k * gaussDdim t v ≤ ((8 / a ^ 2) ^ k * (k.factorial : ℝ)) * gaussDdimWide t v := by
  have hwide : 0 ≤ gaussDdimWide t v := gaussDdimWide_nonneg t v
  calc (1 / t) ^ k * gaussDdim t v
      = ((1 / t) ^ k * Real.exp (-(rncRadialSq v) / (8 * t))) * gaussDdimWide t v := by
        rw [gaussDdim_eq_wide_mul ht v]; ring
    _ ≤ ((8 / a ^ 2) ^ k * (k.factorial : ℝ)) * gaussDdimWide t v :=
        mul_le_mul_of_nonneg_right (invT_pow_exp_le k a ha ht hv) hwide

end QIQTH.HeatResidualBound
