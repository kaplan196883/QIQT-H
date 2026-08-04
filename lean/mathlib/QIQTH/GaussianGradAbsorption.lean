/-
  GaussianGradAbsorption — J4-191: the hEgrad tail step (iii), the reusable SCALAR Gaussian
  ABSORPTION family of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (the honest boundary — read it).

  A reusable analytic BRICK — NOT `a₁ = R/6`.  The Sol `hEgrad` plan step (iii) needs the
  "near-region Gaussian absorption" levers: the E-gradient terms of the parametrix are shaped
  `{(∂A-fields)·G_τ , A·(−v_j/2τ)·G_τ}` with `τ²·A` bounded, so absorbing them into a doubled-width
  Gaussian requires the scalar powers `(|v_j|/τ)·G_τ`, `(‖v‖²/τ²)·G_τ`, and in general
  `(r/√τ)^k·G_τ`.  This file proves that family, all reducing to ONE 1-D core.

    • (1D CORE) `pow_mul_exp_neg_half_sq_le` / `exp_moment_absorption` — the boundedness of the
        weighted Gaussian: `∀ k, x ≥ 0, x^k·e^{−x²/2} ≤ 1 + 2^k·k!`, hence
        `x^k·e^{−x²} ≤ C_k·e^{−x²/2}` (the requested "keeps a Gaussian" form).  Route: AM-GM
        `x^k ≤ (1+(x^k)²)/2` + the banked single-term exp-series bound
        `GaussianPolyBound.pow_mul_exp_neg_le_factorial` (`v^m·e^{−v} ≤ m!`) applied at `v = x²/2`.
    • (SCALAR RADIAL) `radial_ratio_pow_exp_le` — `(r^k/(√τ)^k)·e^{−r²/8τ} ≤ 2^k·(1+2^k·k!)`,
        uniform in `τ > 0` (substitution `w = r/(2√τ)`, so `r²/8τ = w²/2` matches the core exactly).
    • (★ GENERAL LEVER) `gaussDdim_radial_pow_absorption` — the doubling-width absorption in
        `gaussDdim` form: `(rncRadial v)^k/(√τ)^k · gaussDdim τ v ≤ C · gaussDdim (2τ) v`.
        Route: the banked ratio identities `gaussDdim_eq_wide_mul` (narrow = `e^{−r²/8τ}·wide`) and
        `gaussDdimWide_eq_scaled_gaussDdim` (`wide = (√2)ⁿ·gaussDdim(2τ)`), then the scalar radial
        lever absorbs `(r^k/(√τ)^k)·e^{−r²/8τ}` into the constant.
    • (CAMPAIGN k=1) `gaussDdim_linear_absorption` — `(|v_j|/τ)·G_τ ≤ C·(√τ)⁻¹·gaussDdim(2τ)`.
    • (CAMPAIGN k=2) `gaussDdim_quadratic_absorption` — `(rncRadialSq v/τ²)·G_τ ≤ C·τ⁻¹·gaussDdim(2τ)`.
    • (ANNULUS) `sqrtInv_pow_exp_le` — off the diagonal (`r ≥ a > 0`, here `r = a`) EVERY negative
        power absorbs UNIFORMLY in `τ`: `((√τ)⁻¹)^j·e^{−a²/4τ} ≤ C`; and
        `annulus_negPow_exp_le` — the `√τ`-GAIN form `τ^{−m}·e^{−a²/4τ} ≤ C·√τ` (the exponential
        `e^{−a²/4τ}` kills `τ^{−m−1/2}` as `τ ↓ 0`).

  ⚠ HONEST FIREWALL.
    LANDED: the 1-D core (both forms), the scalar radial lever, the general `gaussDdim` doubling-width
      lever (any `k`), the `k = 1` (linear) and `k = 2` (quadratic) campaign consumers, and the two
      annulus levers (boundedness + `√τ`-gain).  The absorption powers covered — `k = 1`
      (`|v_j|/τ`), `k = 2` (`‖v‖²/τ²`), and general `k` (`(r/√τ)^k`) — are exactly the shapes the
      hEgrad assembly consumes from the J4-189/J4-187 gradient formulas.
    All hypotheses (`0 < τ`, `0 ≤ x`, `0 < a`) are genuine, load-bearing, non-vacuous (the bounds
      FAIL without them: near the diagonal the annulus bound is false; without `τ > 0` the Gaussian
      is undefined).  Parametric in the point `v` / radius `r`, decoupled from any concrete chart —
      a reusable BRICK.
    NOT DONE: this is NOT `a₁ = R/6`; the geometric wiring (the J4-189 gradient factorization, the
      sliver-integral assembly, the curvature source) lives downstream.
    No `sorry`, no new axioms, no `expRho` in statements.
-/
import Mathlib
import QIQTH.AnnulusGaussianBound
import QIQTH.GaussianPolyBound
import QIQTH.RadialDistance

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound QIQTH.GaussianPolyBound

namespace QIQTH.GaussianGradAbsorption

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-! ### The 1-D core: `x^k·e^{−x²/2}` is bounded. -/

/-- **THE 1-D CORE (boundedness form).**  For `k : ℕ` and `x ≥ 0`,
      `x^k · e^{−x²/2} ≤ 1 + 2^k · k!`.
    Route: AM-GM `x^k ≤ (1 + (x^k)²)/2`, then `e^{−x²/2} ≤ 1` on one half and the banked
    single-term exp-series bound `pow_mul_exp_neg_le_factorial` (`(x²/2)^k·e^{−x²/2} ≤ k!`) on the
    `(x^k)² = 2^k·(x²/2)^k` half. -/
theorem pow_mul_exp_neg_half_sq_le (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(x ^ 2 / 2)) ≤ 1 + 2 ^ k * (k.factorial : ℝ) := by
  have hv : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
  have hxk : 0 ≤ x ^ k := pow_nonneg hx k
  have hexp_le_one : Real.exp (-(x ^ 2 / 2)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hv])
  have hexp_pos : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  have e2 : (x ^ 2) ^ k = (x ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hsq : (x ^ k) ^ 2 = 2 ^ k * (x ^ 2 / 2) ^ k := by
    rw [div_pow, e2]; field_simp
  have hkey : (x ^ k) ^ 2 * Real.exp (-(x ^ 2 / 2)) ≤ 2 ^ k * (k.factorial : ℝ) := by
    rw [hsq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial hv k) (by positivity)
  have hamgm : x ^ k ≤ (1 + (x ^ k) ^ 2) / 2 := by nlinarith [sq_nonneg (x ^ k - 1)]
  calc x ^ k * Real.exp (-(x ^ 2 / 2))
      ≤ ((1 + (x ^ k) ^ 2) / 2) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hamgm hexp_pos.le
    _ = (1 / 2) * Real.exp (-(x ^ 2 / 2))
          + (1 / 2) * ((x ^ k) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by ring
    _ ≤ (1 / 2) * 1 + (1 / 2) * (2 ^ k * (k.factorial : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hexp_le_one (by norm_num)
        · exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ ≤ 1 + 2 ^ k * (k.factorial : ℝ) := by
        have h0 : (0 : ℝ) ≤ 2 ^ k * (k.factorial : ℝ) := by positivity
        linarith

/-- **THE 1-D CORE (absorption form — the requested statement).**  For `k : ℕ`,
      `∃ C > 0, ∀ x ≥ 0, x^k · e^{−x²} ≤ C · e^{−x²/2}`.
    Immediate from `pow_mul_exp_neg_half_sq_le` via `e^{−x²} = e^{−x²/2}·e^{−x²/2}`. -/
theorem exp_moment_absorption (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      x ^ k * Real.exp (-(x ^ 2)) ≤ C * Real.exp (-(x ^ 2 / 2)) := by
  refine ⟨1 + 2 ^ k * (k.factorial : ℝ), by positivity, fun x hx => ?_⟩
  have hb := pow_mul_exp_neg_half_sq_le k x hx
  have hfac : Real.exp (-(x ^ 2)) = Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
  calc x ^ k * Real.exp (-(x ^ 2))
      = (x ^ k * Real.exp (-(x ^ 2 / 2))) * Real.exp (-(x ^ 2 / 2)) := by rw [hfac]; ring
    _ ≤ (1 + 2 ^ k * (k.factorial : ℝ)) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hb he.le

/-! ### The scalar radial lever. -/

/-- **THE SCALAR RADIAL LEVER.**  For `τ > 0`, `r ≥ 0`, `k : ℕ`,
      `(r^k/(√τ)^k) · e^{−r²/8τ} ≤ 2^k · (1 + 2^k·k!)`,   uniform in `τ`.
    Substitution `w := r/(2√τ)`: then `r²/8τ = w²/2` (matching the 1-D core's exponent exactly) and
    `r/√τ = 2w`, so the left side is `2^k·(w^k·e^{−w²/2}) ≤ 2^k·(1+2^k·k!)`. -/
theorem radial_ratio_pow_exp_le (k : ℕ) (τ : ℝ) (hτ : 0 < τ) (r : ℝ) (hr : 0 ≤ r) :
    r ^ k / Real.sqrt τ ^ k * Real.exp (-(r ^ 2) / (8 * τ))
      ≤ 2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ)) := by
  have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hane : (2 : ℝ) ≠ 0 := by norm_num
  have hsqτ : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  set w : ℝ := r / (2 * Real.sqrt τ) with hwdef
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hw2 : w ^ 2 = r ^ 2 / (4 * τ) := by
    rw [hwdef, div_pow, show (2 * Real.sqrt τ) ^ 2 = 4 * τ from by rw [mul_pow, hsqτ]; ring]
  have hexp_arg : -(r ^ 2) / (8 * τ) = -(w ^ 2 / 2) := by rw [hw2]; ring
  have hratio : r / Real.sqrt τ = 2 * w := by
    rw [hwdef, ← mul_div_assoc, mul_div_mul_left r (Real.sqrt τ) hane]
  rw [hexp_arg, ← div_pow, hratio, mul_pow, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 ^ k)
  exact pow_mul_exp_neg_half_sq_le k w hw0

/-! ### ★ The general `gaussDdim` doubling-width absorption lever. -/

/-- **★ THE GENERAL DOUBLING-WIDTH ABSORPTION LEVER.**  For every `k`, there is a constant `C > 0`
    (depending on `n, k`) with, for all `τ > 0` and `v : Point n`,
      `(rncRadial v)^k / (√τ)^k · gaussDdim τ v ≤ C · gaussDdim (2τ) v`.
    Route: the banked ratio identities `gaussDdim_eq_wide_mul`
    (`gaussDdim τ v = e^{−r²/8τ}·gaussDdimWide τ v`) and `gaussDdimWide_eq_scaled_gaussDdim`
    (`gaussDdimWide τ v = (√2)ⁿ·gaussDdim (2τ) v`) split off the doubled Gaussian; the scalar radial
    lever `radial_ratio_pow_exp_le` absorbs `(r^k/(√τ)^k)·e^{−r²/8τ}` into the constant. -/
theorem gaussDdim_radial_pow_absorption (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ v : Point n,
      rncRadial v ^ k / Real.sqrt τ ^ k * gaussDdim τ v ≤ C * gaussDdim (2 * τ) v := by
  refine ⟨Real.sqrt 2 ^ n * (2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ))), by positivity,
    fun τ hτ v => ?_⟩
  have hgdd : gaussDdim τ v
      = Real.exp (-(rncRadialSq v) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) v) := by
    rw [gaussDdim_eq_wide_mul hτ v, gaussDdimWide_eq_scaled_gaussDdim hτ v]
  have hAE : rncRadial v ^ k / Real.sqrt τ ^ k * Real.exp (-(rncRadialSq v) / (8 * τ))
      ≤ 2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ)) := by
    rw [← rncRadial_sq v]
    exact radial_ratio_pow_exp_le k τ hτ (rncRadial v) (rncRadial_nonneg v)
  have hSG : 0 ≤ Real.sqrt 2 ^ n * gaussDdim (2 * τ) v :=
    mul_nonneg (by positivity) (gaussDdim_nonneg (2 * τ) v)
  rw [hgdd]
  calc rncRadial v ^ k / Real.sqrt τ ^ k
          * (Real.exp (-(rncRadialSq v) / (8 * τ)) * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) v))
      = (rncRadial v ^ k / Real.sqrt τ ^ k * Real.exp (-(rncRadialSq v) / (8 * τ)))
          * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) v) := by ring
    _ ≤ (2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ)))
          * (Real.sqrt 2 ^ n * gaussDdim (2 * τ) v) := mul_le_mul_of_nonneg_right hAE hSG
    _ = Real.sqrt 2 ^ n * (2 ^ k * (1 + 2 ^ k * (k.factorial : ℝ))) * gaussDdim (2 * τ) v := by ring

/-! ### The campaign consumers — `k = 1` (linear) and `k = 2` (quadratic). -/

/-- **★ CAMPAIGN LEVER `k = 1` (LINEAR).**  For every `n` there is `C > 0` with, for all `τ > 0`,
    `v : Point n`, `j : Fin n`,
      `(|v_j|/τ) · gaussDdim τ v ≤ C · (√τ)⁻¹ · gaussDdim (2τ) v`.
    From the general lever at `k = 1` via `|v_j| ≤ rncRadial v` and `1/τ = (√τ)⁻¹·(√τ)⁻¹`. -/
theorem gaussDdim_linear_absorption :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ (v : Point n) (j : Fin n),
      |v j| / τ * gaussDdim τ v ≤ C * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v := by
  obtain ⟨C, hC, hgen⟩ := gaussDdim_radial_pow_absorption (n := n) 1
  refine ⟨C, hC, fun τ hτ v j => ?_⟩
  have hgnnτ : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  have hcoord : |v j| ≤ rncRadial v := abs_coord_le_rncRadial v j
  have hRHSscalar : rncRadial v / Real.sqrt τ * (Real.sqrt τ)⁻¹ = rncRadial v * τ⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc, ← mul_inv, Real.mul_self_sqrt hτ.le]
  have h1 : |v j| / τ ≤ rncRadial v / Real.sqrt τ * (Real.sqrt τ)⁻¹ := by
    rw [hRHSscalar, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcoord (by positivity)
  have hg := hgen τ hτ v
  rw [pow_one, pow_one] at hg
  calc |v j| / τ * gaussDdim τ v
      ≤ (rncRadial v / Real.sqrt τ * (Real.sqrt τ)⁻¹) * gaussDdim τ v :=
        mul_le_mul_of_nonneg_right h1 hgnnτ
    _ = (rncRadial v / Real.sqrt τ * gaussDdim τ v) * (Real.sqrt τ)⁻¹ := by ring
    _ ≤ (C * gaussDdim (2 * τ) v) * (Real.sqrt τ)⁻¹ :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = C * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v := by ring

/-- **★ CAMPAIGN LEVER `k = 2` (QUADRATIC).**  For every `n` there is `C > 0` with, for all `τ > 0`,
    `v : Point n`,
      `(rncRadialSq v / τ²) · gaussDdim τ v ≤ C · τ⁻¹ · gaussDdim (2τ) v`.
    From the general lever at `k = 2` via `rncRadialSq v = (rncRadial v)²` and `(√τ)² = τ`. -/
theorem gaussDdim_quadratic_absorption :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ), 0 < τ → ∀ v : Point n,
      rncRadialSq v / τ ^ 2 * gaussDdim τ v ≤ C * τ⁻¹ * gaussDdim (2 * τ) v := by
  obtain ⟨C, hC, hgen⟩ := gaussDdim_radial_pow_absorption (n := n) 2
  refine ⟨C, hC, fun τ hτ v => ?_⟩
  have hτne : τ ≠ 0 := hτ.ne'
  have hsq2 : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hkey : rncRadialSq v / τ ^ 2 = rncRadial v ^ 2 / Real.sqrt τ ^ 2 * τ⁻¹ := by
    rw [rncRadial_sq, hsq2]; field_simp
  have hg := hgen τ hτ v
  rw [hkey]
  calc rncRadial v ^ 2 / Real.sqrt τ ^ 2 * τ⁻¹ * gaussDdim τ v
      = (rncRadial v ^ 2 / Real.sqrt τ ^ 2 * gaussDdim τ v) * τ⁻¹ := by ring
    _ ≤ (C * gaussDdim (2 * τ) v) * τ⁻¹ :=
        mul_le_mul_of_nonneg_right hg (inv_nonneg.mpr hτ.le)
    _ = C * τ⁻¹ * gaussDdim (2 * τ) v := by ring

/-! ### The annulus levers — negative powers absorb off the diagonal. -/

/-- **THE ANNULUS BOUNDEDNESS LEVER.**  For `a > 0` and any `j : ℕ`, there is `C > 0` with, for all
    `τ > 0`,
      `((√τ)⁻¹)^j · e^{−a²/4τ} ≤ C`,   uniform in `τ`.
    The exponential `e^{−a²/4τ}` beats EVERY negative power `(√τ)⁻¹^j = τ^{−j/2}` (→∞ as `τ ↓ 0`),
    uniformly in `τ`.  Substitution `y := a/(2√τ)`: then `a²/4τ = y²`, `(√τ)⁻¹ = (2/a)·y`, so the
    left side is `(2/a)^j·(y^j·e^{−y²}) ≤ (2/a)^j·(1+2^j·j!)` via the 1-D core (`e^{−y²} ≤ e^{−y²/2}`).
    The `a > 0` hypothesis is load-bearing (at `a = 0` the bound is false). -/
theorem sqrtInv_pow_exp_le (j : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      (Real.sqrt τ)⁻¹ ^ j * Real.exp (-(a ^ 2) / (4 * τ)) ≤ C := by
  refine ⟨(2 / a) ^ j * (1 + 2 ^ j * (j.factorial : ℝ)), by positivity, fun τ hτ => ?_⟩
  have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hτne : Real.sqrt τ ≠ 0 := hτs.ne'
  have hane : a ≠ 0 := ha.ne'
  have hsqτ : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  set y : ℝ := a / (2 * Real.sqrt τ) with hydef
  have hy0 : 0 ≤ y := by rw [hydef]; positivity
  have hy2 : y ^ 2 = a ^ 2 / (4 * τ) := by
    rw [hydef, div_pow, show (2 * Real.sqrt τ) ^ 2 = 4 * τ from by rw [mul_pow, hsqτ]; ring]
  have hexp_arg : -(a ^ 2) / (4 * τ) = -(y ^ 2) := by rw [hy2]; ring
  have hsinv : (Real.sqrt τ)⁻¹ = 2 / a * y := by
    rw [hydef]; field_simp
  rw [hexp_arg, hsinv, mul_pow, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ (2 / a) ^ j)
  calc y ^ j * Real.exp (-(y ^ 2))
      ≤ y ^ j * Real.exp (-(y ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hy0 j)
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
    _ ≤ 1 + 2 ^ j * (j.factorial : ℝ) := pow_mul_exp_neg_half_sq_le j y hy0

/-- **★ THE ANNULUS `√τ`-GAIN LEVER.**  For `a > 0` and `m : ℕ`, there is `C > 0` with, for all
    `τ > 0`,
      `τ^{−m} · e^{−a²/4τ} ≤ C · √τ`.
    The exponential kills the full `τ^{−m−1/2}`: `τ^{−m}·(√τ)⁻¹ = ((√τ)⁻¹)^{2m+1}`, and
    `sqrtInv_pow_exp_le` at `j = 2m+1` gives `((√τ)⁻¹)^{2m+1}·e^{−a²/4τ} ≤ C`; multiplying by
    `√τ > 0` and cancelling `(√τ)⁻¹·√τ = 1` yields the `√τ`-gain. -/
theorem annulus_negPow_exp_le (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      τ⁻¹ ^ m * Real.exp (-(a ^ 2) / (4 * τ)) ≤ C * Real.sqrt τ := by
  obtain ⟨C, hC, hb⟩ := sqrtInv_pow_exp_le (2 * m + 1) a ha
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hτne : Real.sqrt τ ≠ 0 := hτs.ne'
  have hinv2 : (Real.sqrt τ)⁻¹ ^ 2 = τ⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hτ.le]
  have hpow : (Real.sqrt τ)⁻¹ ^ (2 * m + 1) = τ⁻¹ ^ m * (Real.sqrt τ)⁻¹ := by
    rw [pow_succ, pow_mul, hinv2]
  have hb' := hb τ hτ
  rw [hpow] at hb'
  have hL : τ⁻¹ ^ m * (Real.sqrt τ)⁻¹ * Real.exp (-(a ^ 2) / (4 * τ)) * Real.sqrt τ
      = τ⁻¹ ^ m * Real.exp (-(a ^ 2) / (4 * τ)) := by
    field_simp
  have key := mul_le_mul_of_nonneg_right hb' hτs.le
  rwa [hL] at key

end QIQTH.GaussianGradAbsorption

section AxiomChecks

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.GaussianGradAbsorption.pow_mul_exp_neg_half_sq_le
#print axioms QIQTH.GaussianGradAbsorption.exp_moment_absorption
#print axioms QIQTH.GaussianGradAbsorption.radial_ratio_pow_exp_le
#print axioms QIQTH.GaussianGradAbsorption.gaussDdim_radial_pow_absorption
#print axioms QIQTH.GaussianGradAbsorption.gaussDdim_linear_absorption
#print axioms QIQTH.GaussianGradAbsorption.gaussDdim_quadratic_absorption
#print axioms QIQTH.GaussianGradAbsorption.sqrtInv_pow_exp_le
#print axioms QIQTH.GaussianGradAbsorption.annulus_negPow_exp_le

end AxiomChecks
