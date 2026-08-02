/-
  WidthMarginEngine — J4-95: the WIDTH-MARGIN re-plumb of the τ-uniform cutoff-residual engine.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## The obstruction (J4-94 finding, confirmed by gpt-5.6-sol).

  The τ-uniform residual engine (`UniformTauResidual.cutoffResidual_uniformFlow_unconditional_tau`)
  outputs `|residual| ≤ B · gaussDdimWide τ v`, and
      `gaussDdimWide τ v = 2^{n/2} · gaussDdim (2τ) v`   (WIDTH 8τ),
  the SAME width `8τ` as the consumer's `gaussDdim (2τ) (p − q)`.  Post-hoc chart transfer from a
  width-`8τ` bound is IMPOSSIBLE (the cubic error / τ is unbounded as τ → 0⁺).

  ## The fix (Sol) — re-run the engine at the NARROWER middle width `6τ`.

  Write `G_c(τ,v) := gaussDdim (c·τ) v` (width `4c·τ`).  The three widths are
      G₁  (width 4τ, the parametrix primitive `heatParametrix 0 Θ u τ = gaussDdim τ · foldedCoeff`),
      G_{3/2}  (width 6τ, the NEW engine target),  and  G₂ = gaussDdim(2τ)  (width 8τ, the consumer).
  Targeting `G_{3/2}` leaves a strict width budget for the chart transfer to `G₂`
  (`‖p−q‖ ≤ L‖v‖`, `L² ≤ 9/8`, `(3/2)·L² = 27/16 < 2`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What lands here (M1 — the three width-parametric absorption shapes).

    * `gaussDdim_width_ratio` — the shared ratio identity, for `c,d > 0`, `τ > 0`:
        `gaussDdim (c·τ) v = √(d/c)ⁿ · exp(−r²·(d−c)/(4cd·τ)) · gaussDdim (d·τ) v`.
    * `rncRadialSq_pow_mul_gaussDdim_le_width` (A1) — the polynomial absorption `r^{2m}·G_c ≤ C·τ^m·G_d`
      (`1 ≤ c < d`), constant `√(d/c)ⁿ·m!·(4cd/(d−c))^m`.
    * `invTpow_gaussDdim_le_width_annulus` (A2) — the annular absorption `(1/τ)^k·G_c ≤ C·G_d` on the
      annulus `a² ≤ r²`, constant `√(d/c)ⁿ·(4cd/((d−c)a²))^k·k!`.
    * `gaussDdim_le_gaussDdim_chart` (A3) — the CHART TRANSFER `G_c(τ,v) ≤ √(d/c)ⁿ·G_d(τ,w)` whenever
      `c·r²_w ≤ d·r²_v` (the near-isometry width budget), plus the `‖w‖ ≤ L‖v‖` wrapper.
    * `G32` specializations at `(c,d) = (1, 3/2)` used by the M2 engine re-run.

  All hypotheses genuine and load-bearing (the annulus / width-budget bounds FAIL without them).  No
  `sorry`, no new axioms, no `expRho` in statements.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ResidueBound
import QIQTH.AnnulusGaussianBound
import QIQTH.GaussianPolyBound
import QIQTH.UniformTauResidual
import QIQTH.GlobalWitnessHunif

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### M1.0 — the shared width-ratio identity. -/

/-- **THE WIDTH-RATIO IDENTITY.**  For `c, d > 0` and `τ > 0`, the width-`c` Gaussian relates to the
    width-`d` Gaussian by a bounded prefactor `√(d/c)ⁿ` and the extra exponential
    `exp(−r²·(d−c)/(4cd·τ))` (`r² = rncRadialSq v`):
        `gaussDdim (c·τ) v = √(d/c)ⁿ · exp(−r²·(d−c)/(4cd·τ)) · gaussDdim (d·τ) v`.
    The prefactor identity `(√(4πcτ))⁻¹ = √(d/c)·(√(4πdτ))⁻¹` (since `√(4πdτ) = √(d/c)·√(4πcτ)`) and
    the exponent split `−r²/(4cτ) = −r²/(4dτ) − r²(d−c)/(4cdτ)` are pure algebra.  This is the single
    fact underlying every width-parametric absorption below. -/
theorem gaussDdim_width_ratio {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim (c * τ) v
      = Real.sqrt (d / c) ^ n
          * Real.exp (-(rncRadialSq v * ((d - c) / (4 * c * d)) / τ))
          * gaussDdim (d * τ) v := by
  have hcne : c ≠ 0 := hc.ne'
  have hdne : d ≠ 0 := hd.ne'
  have hτne : τ ≠ 0 := hτ.ne'
  rw [gaussDdim_eq_exp (c * τ) v, gaussDdim_eq_exp (d * τ) v]
  have hsc : 0 < Real.sqrt (d / c) := Real.sqrt_pos.mpr (by positivity)
  have hmul : d / c * (4 * Real.pi * (c * τ)) = 4 * Real.pi * (d * τ) := by
    field_simp
  have hpre : (Real.sqrt (4 * Real.pi * (c * τ)))⁻¹
      = Real.sqrt (d / c) * (Real.sqrt (4 * Real.pi * (d * τ)))⁻¹ := by
    have h1 : Real.sqrt (4 * Real.pi * (d * τ))
        = Real.sqrt (d / c) * Real.sqrt (4 * Real.pi * (c * τ)) := by
      rw [← Real.sqrt_mul (by positivity), hmul]
    rw [h1, mul_inv, mul_inv_cancel_left₀ hsc.ne']
  rw [hpre, mul_pow]
  have hexp : Real.exp (-(rncRadialSq v) / (4 * (c * τ)))
      = Real.exp (-(rncRadialSq v) / (4 * (d * τ)))
          * Real.exp (-(rncRadialSq v * ((d - c) / (4 * c * d)) / τ)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hexp]; ring

/-! ### M1.A1 — the polynomial absorption `r^{2m}·G_c ≤ C·τ^m·G_d`. -/

/-- **A1 — THE WIDTH-PARAMETRIC POLYNOMIAL ABSORPTION.**  For `1 ≤ c < d`, `τ > 0`, `m : ℕ`,
        `(rncRadialSq v)^m · gaussDdim (c·τ) v
           ≤ √(d/c)ⁿ · (m! · (4cd/(d−c))^m) · τ^m · gaussDdim (d·τ) v`.
    The even power `r^{2m}` and the widening from `cτ` to `dτ` conspire: the ratio identity splits off
    `exp(−r²β/τ)` (`β = (d−c)/(4cd)`), and `r^{2m}·exp(−r²β/τ) ≤ (τ/β)^m·m!` (`x^m e^{−x} ≤ m!` at
    `x = r²β/τ`) deposits the polynomial into `τ^m`, the `1/β^m = (4cd/(d−c))^m` constant, and the
    factorial.  This is the `G_{3/2}` analogue of `rncRadialSq_pow_mul_gaussDdim_le`. -/
theorem rncRadialSq_pow_mul_gaussDdim_le_width (m : ℕ) {c d : ℝ} (hc : 0 < c) (hcd : c < d)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    (rncRadialSq v) ^ m * gaussDdim (c * τ) v
      ≤ Real.sqrt (d / c) ^ n * ((m.factorial : ℝ) * (4 * c * d / (d - c)) ^ m)
          * τ ^ m * gaussDdim (d * τ) v := by
  have hd : 0 < d := lt_trans hc hcd
  have hdc : 0 < d - c := by linarith
  have hcne : c ≠ 0 := hc.ne'
  have hdne : d ≠ 0 := hd.ne'
  have hτne : τ ≠ 0 := hτ.ne'
  have hdcne : d - c ≠ 0 := hdc.ne'
  rw [gaussDdim_width_ratio hc hd hτ v]
  set G := gaussDdim (d * τ) v with hG
  have hG0 : 0 ≤ G := gaussDdim_nonneg _ _
  set r2 := rncRadialSq v with hr2
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  set β := (d - c) / (4 * c * d) with hβ
  have hβ0 : 0 < β := div_pos hdc (by positivity)
  have hx : 0 ≤ r2 * β / τ := by positivity
  have hscalar : r2 ^ m * Real.exp (-(r2 * β / τ)) ≤ (τ / β) ^ m * (m.factorial : ℝ) := by
    have hkey := pow_mul_exp_neg_le_factorial hx m
    have hre : r2 ^ m = (τ / β) ^ m * (r2 * β / τ) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hre, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc r2 ^ m * (Real.sqrt (d / c) ^ n * Real.exp (-(r2 * β / τ)) * G)
      = Real.sqrt (d / c) ^ n * G * (r2 ^ m * Real.exp (-(r2 * β / τ))) := by ring
    _ ≤ Real.sqrt (d / c) ^ n * G * ((τ / β) ^ m * (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = Real.sqrt (d / c) ^ n * ((m.factorial : ℝ) * (4 * c * d / (d - c)) ^ m) * τ ^ m * G := by
        rw [hβ]; field_simp; ring

/-! ### M1.A2 — the annular absorption `(1/τ)^k·G_c ≤ C·G_d`. -/

/-- **A2 — THE WIDTH-PARAMETRIC ANNULAR ABSORPTION.**  On the annulus `a² ≤ rncRadialSq v` (`0 < a`),
    for `0 < c < d`, `τ > 0`, `k : ℕ`,
        `(1/τ)^k · gaussDdim (c·τ) v ≤ √(d/c)ⁿ · ((4cd/((d−c)a²))^k · k!) · gaussDdim (d·τ) v`,
    uniform in `τ`.  The width gap gives `exp(−r²β/τ)` (`β = (d−c)/(4cd)`), and on the annulus
    `1/τ ≤ (r²β/τ)/(a²β)`, so `(1/τ)^k·exp(−r²β/τ) ≤ (1/(a²β))^k·k!` (`x^k e^{−x} ≤ k!`).  The `G_{3/2}`
    analogue of `invTpow_gaussDdim_le_gaussDdimWide`; the annulus hypothesis is load-bearing. -/
theorem invTpow_gaussDdim_le_width_annulus (k : ℕ) (a : ℝ) (ha : 0 < a) {c d : ℝ}
    (hc : 0 < c) (hcd : c < d) {τ : ℝ} (hτ : 0 < τ) {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / τ) ^ k * gaussDdim (c * τ) v
      ≤ Real.sqrt (d / c) ^ n * ((4 * c * d / ((d - c) * a ^ 2)) ^ k * (k.factorial : ℝ))
          * gaussDdim (d * τ) v := by
  have hd : 0 < d := lt_trans hc hcd
  have hdc : 0 < d - c := by linarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hτne : τ ≠ 0 := hτ.ne'
  rw [gaussDdim_width_ratio hc hd hτ v]
  set G := gaussDdim (d * τ) v with hG
  have hG0 : 0 ≤ G := gaussDdim_nonneg _ _
  set r2 := rncRadialSq v with hr2
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  set β := (d - c) / (4 * c * d) with hβ
  have hβ0 : 0 < β := div_pos hdc (by positivity)
  have hx : 0 ≤ r2 * β / τ := by positivity
  -- annulus key: `1/τ ≤ (1/(a²β)) · (r²β/τ)`
  have h1t : 1 / τ ≤ (1 / (a ^ 2 * β)) * (r2 * β / τ) := by
    rw [div_le_iff₀ hτ]
    have : (1 / (a ^ 2 * β)) * (r2 * β / τ) * τ = r2 / a ^ 2 := by
      field_simp
    rw [this]
    rw [le_div_iff₀ ha2]
    calc (1 : ℝ) * a ^ 2 = a ^ 2 := by ring
      _ ≤ r2 := hv
  have hpow : (1 / τ) ^ k ≤ ((1 / (a ^ 2 * β)) * (r2 * β / τ)) ^ k :=
    pow_le_pow_left₀ (by positivity) h1t k
  have hscalar : (1 / τ) ^ k * Real.exp (-(r2 * β / τ))
      ≤ (1 / (a ^ 2 * β)) ^ k * (k.factorial : ℝ) := by
    calc (1 / τ) ^ k * Real.exp (-(r2 * β / τ))
        ≤ ((1 / (a ^ 2 * β)) * (r2 * β / τ)) ^ k * Real.exp (-(r2 * β / τ)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = (1 / (a ^ 2 * β)) ^ k * ((r2 * β / τ) ^ k * Real.exp (-(r2 * β / τ))) := by
          rw [mul_pow]; ring
      _ ≤ (1 / (a ^ 2 * β)) ^ k * (k.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial hx k) (by positivity)
  calc (1 / τ) ^ k * (Real.sqrt (d / c) ^ n * Real.exp (-(r2 * β / τ)) * G)
      = Real.sqrt (d / c) ^ n * G * ((1 / τ) ^ k * Real.exp (-(r2 * β / τ))) := by ring
    _ ≤ Real.sqrt (d / c) ^ n * G * ((1 / (a ^ 2 * β)) ^ k * (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = Real.sqrt (d / c) ^ n * ((4 * c * d / ((d - c) * a ^ 2)) ^ k * (k.factorial : ℝ)) * G := by
        rw [hβ]; field_simp

/-! ### M1.A3 — the chart transfer `G_c(τ,v) ≤ C·G_d(τ,w)`. -/

/-- **A3 — THE CHART TRANSFER (width budget).**  For `c, d > 0`, `τ > 0`, and the near-isometry width
    budget `c·rncRadialSq w ≤ d·rncRadialSq v`,
        `gaussDdim (c·τ) v ≤ √(d/c)ⁿ · gaussDdim (d·τ) w`.
    The prefactor `√(d/c)ⁿ` absorbs the width change and the exponent inequality is exactly the width
    budget: `exp(−r²_v/(4cτ)) ≤ exp(−r²_w/(4dτ)) ⟺ c·r²_w ≤ d·r²_v`.  No extra exponential constant.
    This is the consumer-facing transfer from the engine target `G_{3/2}` (`c=3/2`) to the consumer
    width `G₂ = gaussDdim(2τ)` (`d=2`); it needs `(3/2)·r²_w ≤ 2·r²_v`, e.g. `‖w‖ ≤ L‖v‖` with
    `L² ≤ 9/8` (`(3/2)L² = 27/16 < 2`). -/
theorem gaussDdim_le_gaussDdim_chart {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {τ : ℝ} (hτ : 0 < τ)
    {v w : Point n} (hnorm : c * rncRadialSq w ≤ d * rncRadialSq v) :
    gaussDdim (c * τ) v ≤ Real.sqrt (d / c) ^ n * gaussDdim (d * τ) w := by
  have hcne : c ≠ 0 := hc.ne'
  rw [gaussDdim_eq_exp (c * τ) v, gaussDdim_eq_exp (d * τ) w]
  have hsc : 0 < Real.sqrt (d / c) := Real.sqrt_pos.mpr (by positivity)
  have hmul : d / c * (4 * Real.pi * (c * τ)) = 4 * Real.pi * (d * τ) := by
    field_simp
  have hpre : (Real.sqrt (4 * Real.pi * (c * τ)))⁻¹
      = Real.sqrt (d / c) * (Real.sqrt (4 * Real.pi * (d * τ)))⁻¹ := by
    have h1 : Real.sqrt (4 * Real.pi * (d * τ))
        = Real.sqrt (d / c) * Real.sqrt (4 * Real.pi * (c * τ)) := by
      rw [← Real.sqrt_mul (by positivity), hmul]
    rw [h1, mul_inv, mul_inv_cancel_left₀ hsc.ne']
  rw [hpre, mul_pow, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h4c : (0:ℝ) < 4 * (c * τ) := by positivity
  have h4d : (0:ℝ) < 4 * (d * τ) := by positivity
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ h4d h4c]
  nlinarith [mul_le_mul_of_nonneg_left hnorm (show (0:ℝ) ≤ 4 * τ by positivity)]

/-! ### M1 specializations at `(c, d) = (1, 3/2)` — the shapes the M2 engine re-run consumes. -/

/-- `gaussDdim τ v ≤ √(3/2)ⁿ · gaussDdim ((3/2)·τ) v` — the `m = 0` polynomial absorption (T3 shape). -/
theorem gaussDdim_le_gaussDdim_narrow {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim τ v ≤ Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 0 (c := 1) (d := 3 / 2) (by norm_num) (by norm_num)
    hτ v
  simpa using h

/-- `r²·gaussDdim τ v ≤ (√(3/2)ⁿ·12)·τ·gaussDdim ((3/2)·τ) v` — the `m = 1` absorption (T1 shape). -/
theorem rncRadialSq_mul_gaussDdim_le_narrow {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadialSq v * gaussDdim τ v
      ≤ Real.sqrt (3 / 2) ^ n * 12 * τ * gaussDdim (3 / 2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 1 (c := 1) (d := 3 / 2) (by norm_num) (by norm_num)
    hτ v
  have e1 : (3 / 2 / 1 : ℝ) = 3 / 2 := by norm_num
  have e2 : ((1:ℕ).factorial : ℝ) * (4 * (1:ℝ) * (3 / 2) / (3 / 2 - 1)) ^ 1 = 12 := by
    norm_num [Nat.factorial]
  rw [e1, one_mul, e2] at h
  simpa using h

/-- `r⁴·gaussDdim τ v ≤ (√(3/2)ⁿ·288)·τ²·gaussDdim ((3/2)·τ) v` — the `m = 2` absorption (T2 shape). -/
theorem rncRadialSq_sq_mul_gaussDdim_le_narrow {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadialSq v ^ 2 * gaussDdim τ v
      ≤ Real.sqrt (3 / 2) ^ n * 288 * τ ^ 2 * gaussDdim (3 / 2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 2 (c := 1) (d := 3 / 2) (by norm_num) (by norm_num)
    hτ v
  have e1 : (3 / 2 / 1 : ℝ) = 3 / 2 := by norm_num
  have e2 : ((2:ℕ).factorial : ℝ) * (4 * (1:ℝ) * (3 / 2) / (3 / 2 - 1)) ^ 2 = 288 := by
    norm_num [Nat.factorial]
  rw [e1, one_mul, e2] at h
  simpa using h

/-- The annular `(1/τ)^k` absorption specialized to `(c,d) = (1, 3/2)`:
    `(1/τ)^k · gaussDdim τ v ≤ √(3/2)ⁿ · ((12/a²)^k·k!) · gaussDdim ((3/2)·τ) v` on `a² ≤ r²`. -/
theorem invTpow_gaussDdim_le_narrow (k : ℕ) (a : ℝ) (ha : 0 < a) {τ : ℝ} (hτ : 0 < τ)
    {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / τ) ^ k * gaussDdim τ v
      ≤ Real.sqrt (3 / 2) ^ n * ((12 / a ^ 2) ^ k * (k.factorial : ℝ)) * gaussDdim (3 / 2 * τ) v := by
  have h := invTpow_gaussDdim_le_width_annulus k a ha (c := 1) (d := 3 / 2) (by norm_num) (by norm_num)
    hτ hv
  have e1 : (3 / 2 / 1 : ℝ) = 3 / 2 := by norm_num
  have e3 : (4 * (1:ℝ) * (3 / 2) / ((3 / 2 - 1) * a ^ 2)) = 12 / a ^ 2 := by
    rw [show ((3 / 2 : ℝ) - 1) = 1 / 2 by norm_num]; ring
  rw [e1, one_mul, e3] at h
  exact h

/-! ### M2 — RE-RUNNING the τ-uniform cutoff-residual engine at the NARROW target `G_{3/2}`. -/

/-- **M2 — the T2 quadratic term, at width `G_{3/2}`.**  `residualQuadratic_pointwise` retargeted to
    `gaussDdim (3/2·t)`: the `m = 2` narrow absorption `r⁴·G ≤ √(3/2)ⁿ·288·t²·G_{3/2}` replaces the
    width-`8t` one (`r⁴·G ≤ 128·t²·G_wide`), giving `(1/4)·288 = 72` and the bounded prefactor
    `√(3/2)ⁿ`.  Same deviation / coefficient hypotheses. -/
theorem residualQuadratic_pointwise_narrow (gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) {t : ℝ} (ht : 0 < t) (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (v : Point n)
    (hdev_v : ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw_v : |foldedCoeff Θ u 0 v| ≤ W) :
    |(1 / t ^ 2) * gaussDdim t v
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
        * foldedCoeff Θ u 0 v|
      ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * gaussDdim (3 / 2 * t) v := by
  have htne : t ≠ 0 := ht.ne'
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w : ℝ := foldedCoeff Θ u 0 v with hwdef
  have hSabs : |S| ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
    calc |S| ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * rncRadialSq v ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := hdev_v i j
            have h2 : |v i * v j| ≤ rncRadialSq v := by
              rw [abs_mul]
              calc |v i| * |v j|
                  ≤ rncRadial v * rncRadial v :=
                    mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
                      (abs_nonneg _) (rncRadial_nonneg v)
                _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
            calc |gi v i j - (if i = j then (1 : ℝ) else 0)| * |v i * v j|
                ≤ (M * rncRadialSq v) * rncRadialSq v :=
                  mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (rncRadialSq_nonneg v))
              _ = M * rncRadialSq v ^ 2 := by ring
      _ = (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hrr2G : rncRadialSq v ^ 2 * gaussDdim t v
      ≤ Real.sqrt (3 / 2) ^ n * 288 * t ^ 2 * gaussDdim (3 / 2 * t) v :=
    rncRadialSq_sq_mul_gaussDdim_le_narrow ht v
  have hG : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  have hn2Mrr : 0 ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM) (sq_nonneg _)
  have hC0 : 0 ≤ (1 / t ^ 2) * (1 / 4) := by positivity
  have hK2 : 0 ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) := by
    apply mul_nonneg
    · apply div_nonneg _ (by norm_num)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hM) hW
    · positivity
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  calc |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * (1 / 4) * gaussDdim t v * (|S| * |w|) := by rw [habs2]; ring
    _ ≤ (1 / t ^ 2) * (1 / 4) * gaussDdim t v
          * (((n : ℝ) ^ 2 * M * rncRadialSq v ^ 2) * W) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hSabs hw_v (abs_nonneg _) hn2Mrr)
            (mul_nonneg hC0 hG)
    _ = (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (rncRadialSq v ^ 2 * gaussDdim t v) := by ring
    _ ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2)
          * (Real.sqrt (3 / 2) ^ n * 288 * t ^ 2 * gaussDdim (3 / 2 * t) v) :=
          mul_le_mul_of_nonneg_left hrr2G hK2
    _ = Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * gaussDdim (3 / 2 * t) v := by
        field_simp; ring

/-- **M2 — the N=0 near residual bound, at width `G_{3/2}`, ∀ τ > 0.**  `uniformResidual_gaussian_bound_tau`
    retargeted from `gaussDdimWide τ` to `gaussDdim (3/2·τ)`: the three terms use the NARROW absorptions
    (`rncRadialSq_mul_gaussDdim_le_narrow`, `residualQuadratic_pointwise_narrow`,
    `gaussDdim_le_gaussDdim_narrow`).  Same firewalled input `hCoeffU`; the constant carries the bounded
    prefactor `√(3/2)ⁿ`.  All constants `τ`-free. -/
theorem uniformResidual_gaussian_bound_tau_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ C * gaussDdim (3 / 2 * τ) v := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨rL, hrL0, L, hL0, hLapU⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u hw0smooth
  set ρ_u : ℝ := min rM (min rL ρ_c) with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hrM0 (lt_min hrL0 hρ_c)
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, Real.sqrt (3 / 2) ^ n * (12 * C_c + 72 * (n : ℝ) ^ 2 * M * W + L),
    by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  set Gn : ℝ := gaussDdim (3 / 2 * τ) v with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  have hT1bd : |T1| ≤ Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadialSq v * gaussDdim τ v) := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt (3 / 2) ^ n * 12 * τ * Gn) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_c0 (one_div_nonneg.mpr hτ.le))
          rw [hGndef]; exact rncRadialSq_mul_gaussDdim_le_narrow hτ v
      _ = Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn := by field_simp
  have hT2bd : |T2| ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_narrow (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W
      hM0 hW0 v (hdevU q hq v hvM) (hWbd v hvball)
  have hT3bd : |T3| ≤ Real.sqrt (3 / 2) ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt (3 / 2) ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_narrow hτ v) hL0
      _ = Real.sqrt (3 / 2) ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn
          + Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
          + Real.sqrt (3 / 2) ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = Real.sqrt (3 / 2) ^ n * (12 * C_c + 72 * (n : ℝ) ^ 2 * M * W + L) * Gn := by ring

/-- **M2 — the annulus DERIVATIVE absorption, at width `G_{3/2}`.**
    `parametrixCofactor_deriv_annulus_gaussDdimWide_tauUniform` retargeted to `gaussDdim (3/2·τ)`:
    the annulus `(1/τ)·G ≤ √(3/2)ⁿ·(12/a²)·G_{3/2}` (`invTpow_gaussDdim_le_narrow`, `k=1`) and
    `G ≤ √(3/2)ⁿ·G_{3/2}` (`gaussDdim_le_gaussDdim_narrow`) deposit the polynomial `wʲ`- and `(1/τ)`-
    factors into the narrow Gaussian; the `τ`-free `Kder` carries the bounded `√(3/2)ⁿ`. -/
theorem parametrixCofactor_deriv_annulus_narrow_tauUniform
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => gaussDdim τ y * cofactor y) j w| ≤ Kd * gaussDdim (3 / 2 * τ) w := by
  classical
  obtain ⟨Kcof, hKcof0, hKcof⟩ := exists_bound_on_annulus cofactor hcof_cont a b
  have hbd : ∀ j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ K :=
    fun j => exists_bound_on_annulus (fun w => pd cofactor j w) (hdcof_cont j) a b
  choose Kd' hKd'0 hKdbd using hbd
  set Kdcof : ℝ := ∑ j, Kd' j with hKdcof_def
  have hKdcof0 : 0 ≤ Kdcof := Finset.sum_nonneg fun j _ => hKd'0 j
  have hKdcof : ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ Kdcof := by
    intro w j h1 h2
    refine (hKdbd j w h1 h2).trans ?_
    exact Finset.single_le_sum (f := fun j' => Kd' j') (fun j' _ => hKd'0 j') (Finset.mem_univ j)
  refine ⟨Real.sqrt (3 / 2) ^ n * (b * Kcof / 2 * (12 / a ^ 2) + Kdcof), by positivity, ?_⟩
  intro τ hτ w j h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  set Gn : ℝ := gaussDdim (3 / 2 * τ) w with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ w
  have h2tpos : (0 : ℝ) < 2 * τ := by linarith
  have hwj : |w j| ≤ b := by
    have hle : (w j) ^ 2 ≤ b ^ 2 :=
      calc (w j) ^ 2 ≤ ∑ i, (w i) ^ 2 :=
            Finset.single_le_sum (f := fun i => (w i) ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ j)
        _ = rncRadialSq w := rfl
        _ ≤ b ^ 2 := h2
    calc |w j| = Real.sqrt ((w j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
      _ = |b| := Real.sqrt_sq_eq_abs _
      _ = b := abs_of_pos hb
  have hpg : PdiffAt (fun y => gaussDdim τ y) j w :=
    PdiffAt_of_contDiff (fun y => gaussDdim τ y) (gaussDdim_contDiff τ) j w
  have hpc : PdiffAt cofactor j w := hcof_pdiff j w
  rw [pd_mul (fun y => gaussDdim τ y) cofactor j w hpg hpc, gaussDdim_pd_eq τ hτ w j]
  have hinvT : (1 / τ) * gaussDdim τ w ≤ Real.sqrt (3 / 2) ^ n * (12 / a ^ 2) * Gn := by
    have h := invTpow_gaussDdim_le_narrow 1 a ha hτ h1
    rw [hGndef]
    simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
  have hGle : gaussDdim τ w ≤ Real.sqrt (3 / 2) ^ n * Gn := by
    rw [hGndef]; exact gaussDdim_le_gaussDdim_narrow hτ w
  have hT1 : |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w|
      ≤ b / (2 * τ) * gaussDdim τ w * Kcof := by
    rw [abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2tpos]
    have hGA : 0 ≤ |w j| / (2 * τ) * gaussDdim τ w :=
      mul_nonneg (div_nonneg (abs_nonneg _) (le_of_lt h2tpos)) hG0
    calc |w j| / (2 * τ) * gaussDdim τ w * |cofactor w|
        ≤ |w j| / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_left (hKcof w h1 h2) hGA
      _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right h2tpos).mpr hwj) hG0)
            hKcof0
  have hT2 : |gaussDdim τ w * pd cofactor j w| ≤ gaussDdim τ w * Kdcof := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul_of_nonneg_left (hKdcof w j h1 h2) hG0
  have hT1abs : b / (2 * τ) * gaussDdim τ w * Kcof
      ≤ b * Kcof / 2 * (Real.sqrt (3 / 2) ^ n * (12 / a ^ 2)) * Gn := by
    have hcoef : (0 : ℝ) ≤ b * Kcof / 2 := by positivity
    calc b / (2 * τ) * gaussDdim τ w * Kcof
        = (b * Kcof / 2) * ((1 / τ) * gaussDdim τ w) := by ring
      _ ≤ (b * Kcof / 2) * (Real.sqrt (3 / 2) ^ n * (12 / a ^ 2) * Gn) :=
          mul_le_mul_of_nonneg_left hinvT hcoef
      _ = b * Kcof / 2 * (Real.sqrt (3 / 2) ^ n * (12 / a ^ 2)) * Gn := by ring
  have hT2abs : gaussDdim τ w * Kdcof ≤ Kdcof * (Real.sqrt (3 / 2) ^ n * Gn) := by
    calc gaussDdim τ w * Kdcof = Kdcof * gaussDdim τ w := by ring
      _ ≤ Kdcof * (Real.sqrt (3 / 2) ^ n * Gn) := mul_le_mul_of_nonneg_left hGle hKdcof0
  calc |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w + gaussDdim τ w * pd cofactor j w|
      ≤ |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w| + |gaussDdim τ w * pd cofactor j w| :=
        abs_add_le _ _
    _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof + gaussDdim τ w * Kdcof := add_le_add hT1 hT2
    _ ≤ b * Kcof / 2 * (Real.sqrt (3 / 2) ^ n * (12 / a ^ 2)) * Gn
          + Kdcof * (Real.sqrt (3 / 2) ^ n * Gn) := add_le_add hT1abs hT2abs
    _ = Real.sqrt (3 / 2) ^ n * (b * Kcof / 2 * (12 / a ^ 2) + Kdcof) * Gn := by ring

/-- **M2 — the cutoff engine assembly, at width `G_{3/2}`.**  `cutoffResidual_gaussianWide_tauUniform_engine`
    retargeted so EVERY dominating Gaussian is `gaussDdim (3/2·t)` — including the annulus VALUE bound
    `hHann` (already narrow, so the internal `gaussDdim t ≤ gaussDdimWide` conversion of the wide engine
    is unnecessary).  Region split (near/annulus/far) identical; `B = C + Kcof·Kc2 + 2n²·Kg·Kc1·Kder`. -/
theorem cutoffResidual_narrow_tauUniform_engine
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * gaussDdim (3 / 2 * t) w)
    (Kcof : ℝ) (hKcof : 0 ≤ Kcof)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ Kcof * gaussDdim (3 / 2 * t) w)
    (Kder : ℝ) (hKder : 0 ≤ Kder)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ Kder * gaussDdim (3 / 2 * t) w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    0 ≤ C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v := by
  have hb2 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof hKc2
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
  refine ⟨by linarith, ?_⟩
  intro v
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hWnn : 0 ≤ gaussDdim (3 / 2 * t) v := gaussDdim_nonneg _ v
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rcases lt_or_ge (rncRadialSq v) (a ^ 2) with hnear | ha2
  · have hb : rncRadialSq v ≤ b ^ 2 := le_trans (le_of_lt hnear) ha2b2
    have hχ1 : radialCutoff a b v = 1 := radialCutoff_eq_one ha hab (le_of_lt hnear)
    have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
    have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
      laplaceBeltrami_radialCutoff_zero_near g gi ha hab hnear
    have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
      fun i => pd_radialCutoff_eq_zero_of_near ha hab hnear i
    have hRcut : radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
          = dtH v - laplaceBeltrami g gi H v := by
      rw [hlbmul, hχ1, hlapχ]; simp [hpdχ]
    rw [hRcut]
    calc |dtH v - laplaceBeltrami g gi H v| ≤ C * gaussDdim (3 / 2 * t) v := hEnear v hb
      _ ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v := by
          apply mul_le_mul_of_nonneg_right _ hWnn; linarith
  · rcases le_or_gt (rncRadialSq v) (b ^ 2) with hb | hfar
    · have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
            = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
              - H v * laplaceBeltrami g gi (radialCutoff a b) v
              - 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v := by
        rw [hlbmul]; ring
      rw [hRcut]
      have hsub2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
        rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
      set A := radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v) with hA
      set B' := H v * laplaceBeltrami g gi (radialCutoff a b) v with hB'
      set Cc := 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v with hCc
      have htri : |A - B' - Cc| ≤ |A| + |B'| + |Cc| :=
        (hsub2 (A - B') Cc).trans (by have := hsub2 A B'; linarith)
      have hAbd : |A| ≤ C * gaussDdim (3 / 2 * t) v := by
        rw [hA, abs_mul]
        have hχle : |radialCutoff a b v| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
        calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
            ≤ 1 * (C * gaussDdim (3 / 2 * t) v) :=
              mul_le_mul hχle (hEnear v hb) (abs_nonneg _) (by norm_num)
          _ = C * gaussDdim (3 / 2 * t) v := by ring
      have hBbd : |B'| ≤ (Kcof * Kc2) * gaussDdim (3 / 2 * t) v := by
        rw [hB', abs_mul]
        calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
            ≤ (Kcof * gaussDdim (3 / 2 * t) v) * Kc2 :=
              mul_le_mul (hHann v ha2 hb) (hLapChi v ha2 hb) (abs_nonneg _)
                (mul_nonneg hKcof (gaussDdim_nonneg _ v))
          _ = (Kcof * Kc2) * gaussDdim (3 / 2 * t) v := by ring
      have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ Kg * Kc1 * (Kder * gaussDdim (3 / 2 * t) v) := by
        intro i j
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hgibd v i j ha2 hb) (hDchi v i ha2 hb) (abs_nonneg _) hKg)
          (hDHann v j ha2 hb) (abs_nonneg _) (mul_nonneg hKg hKc1)
      have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * gaussDdim (3 / 2 * t) v)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * gaussDdim (3 / 2 * t) v)))
          = (n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * gaussDdim (3 / 2 * t) v)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v := by
        rw [hCc]
        calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
            = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
              mul_le_mul_of_nonneg_left hSabs (by norm_num)
          _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * gaussDdim (3 / 2 * t) v))) :=
              mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v := by ring
      calc |A - B' - Cc|
          ≤ C * gaussDdim (3 / 2 * t) v + (Kcof * Kc2) * gaussDdim (3 / 2 * t) v
              + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v :=
            htri.trans (add_le_add (add_le_add hAbd hBbd) hCcbd)
        _ = (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdim (3 / 2 * t) v := by ring
    · have hχ0 : radialCutoff a b v = 0 := radialCutoff_eq_zero ha hab (le_of_lt hfar)
      have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
        laplaceBeltrami_radialCutoff_zero_far g gi ha hab hfar
      have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
        fun i => pd_radialCutoff_eq_zero_of_far ha hab hfar i
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v = 0 := by
        rw [hlbmul, hχ0, hlapχ]; simp [hpdχ]
      rw [hRcut, abs_zero]
      have : (0 : ℝ) ≤ C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by linarith
      exact mul_nonneg this hWnn

/-- **M2 — the near engine wrapper, at width `G_{3/2}`.**  `near_uncutResidual_uniform_tau` verbatim,
    Gaussian shape `gaussDdim (3/2·τ)`; the ball conversion is `τ`-independent. -/
theorem near_uncutResidual_uniform_tau_narrow
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (C ρ_u : ℝ) (hρ_u : 0 < ρ_u)
    (hResU : ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ C * gaussDdim (3 / 2 * τ) v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u τ) w|
          ≤ C * gaussDdim (3 / 2 * τ) w := by
  refine ⟨ρ_u / 2, by linarith, fun τ hτ q hq w hw => ?_⟩
  have hb0 : (0 : ℝ) ≤ ρ_u / 2 := by linarith
  have hnw : ‖w‖ < ρ_u := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ_u / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ_u / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  have hs := hResU τ hτ q hq w hnw
  simpa only [parametrixResidualN] using hs

/-- **★ M2 CAPSTONE — the cutoff engine UNIFORM over `K` AND all `τ > 0`, at the NARROW width `G_{3/2}`.**
    `cutoffResidual_uniformFlow_unconditional_tau` retargeted: a single `τ`-free `(a, b, B)` with, for
    EVERY `τ > 0` and `q ∈ K`, the cutoff-parametrix residual on `g̃_q` dominated by
    `B · gaussDdim (3/2·τ) v` — WIDTH `6τ`, strictly narrower than the consumer's `gaussDdim (2τ)`
    (width `8τ`), leaving room for the M3 chart transfer.  Same genuine geometric + heat-side
    hypotheses as the wide capstone; the narrow near bound + narrow annulus value/derivative
    absorptions feed the narrow engine.  NO `expRho`; NOT `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_unconditional_tau_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
        ≤ B * gaussDdim (3 / 2 * τ) v := by
  classical
  obtain ⟨ρ_c, hρ_c, C_c, hC_c0, hCoeffU⟩ :=
    uniformCoeff_bound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
  obtain ⟨ρ_u, hρ_u0, C, hC0, hResU⟩ :=
    uniformResidual_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth
      ρ_c C_c hρ_c hC_c0 hCoeffU
  obtain ⟨bN, hbN0, hEnearU⟩ :=
    near_uncutResidual_uniform_tau_narrow g gi hC hK Θ u C ρ_u hρ_u0 hResU
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min bN (rmin / 2) with hb_def
  have hb0 : 0 < b := lt_min hbN0 (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_le_bN : b ≤ bN := min_le_left _ _
  have hb_lt_rmin : b < rmin := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kcof, hKcof0, hHannU⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) hw0smooth.continuous
  obtain ⟨Kder, hKder0, hDHannU⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  set Kcof' : ℝ := Kcof * Real.sqrt (3 / 2) ^ n with hKcof'_def
  have hKcof'0 : 0 ≤ Kcof' := by positivity
  have hBnn : 0 ≤ C + Kcof' * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
    have h1 : 0 ≤ Kcof' * Kc2 := mul_nonneg hKcof'0 hKc20
    have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
    linarith
  refine ⟨a, b, C + Kcof' * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder, ha0, hab, hBnn, ?_⟩
  intro τ hτ q hq v
  have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
    funext x; rw [heatParametrix_folded]; simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u τ w = gaussDdim τ w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
    rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u τ) w :=
    fun w => hH.contDiffAt.of_le le_top
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u τ w| ≤ Kcof' * gaussDdim (3 / 2 * τ) w := by
    intro w h1 h2
    rw [hHeqw w]
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w|
        ≤ Kcof * gaussDdim τ w := hHannU τ hτ w h1 h2
      _ ≤ Kcof * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) w) :=
          mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow hτ w) hKcof0
      _ = Kcof' * gaussDdim (3 / 2 * τ) w := by rw [hKcof'_def]; ring
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u τ) j w| ≤ Kder * gaussDdim (3 / 2 * τ) w := by
    intro w j h1 h2; rw [hHeq]; exact hDHannU τ hτ w j h1 h2
  have hb2_le : b ^ 2 ≤ bN ^ 2 := by nlinarith [hb_le_bN, hb0, hbN0]
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 0 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u τ) w|
        ≤ C * gaussDdim (3 / 2 * τ) w :=
    fun w hw => hEnearU τ hτ q hq w (le_trans hw hb2_le)
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  exact (cutoffResidual_narrow_tauUniform_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 0 Θ u τ) (fun x => deriv (fun s => heatParametrix 0 Θ u s x) τ)
    a b τ ha0 hab hτ hH2 hgisymm_q
    C hC0 hEnear_q Kcof' hKcof'0 hHann Kder hKder0 hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v

/-! ### M3 — the CHART-TRANSFER transport chain, at width `G_{3/2}`, and the consumer-width payoff. -/

/-- **M3 — narrow W3.**  `globalWitness_residual_bound_inChart` composed with the NARROW capstone: the
    in-chart per-base-point residual bound at width `gaussDdim (3/2·τ)`.  W2 transport is width-agnostic
    (an equality), so only the residual input changes. -/
theorem globalWitness_residual_bound_inChart_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (Vmap : Point n → Point n → Point n) (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
          (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
          ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
              (uniformFlowExp g gi hC hK q v) →
          IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
          (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
              * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
          (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
              * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b Vmap) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨a, b, B, ha, hab, hB, hAbound⟩ :=
    cutoffResidual_uniformFlow_unconditional_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro Vmap τ q hq hτ
  obtain ⟨r₀, hr₀, htrans⟩ :=
    heatOp_globalWitness_eq_recentred_inChart g gi hC hK hgsymm Θ u a b Vmap τ q hq
  refine ⟨r₀, hr₀, ?_⟩
  intro v hv hgerm hg1 hf hU hGGi hGiG
  rw [htrans v hv hgerm hg1 hf hU hGGi hGiG]
  exact hAbound τ hτ q hq v

/-- **M3 — narrow I4.**  `globalWitness_residual_bound_inChart_unconditional` at width `gaussDdim (3/2·τ)`:
    the germ + inverse-chart regularity antecedents are discharged by the SAME IFT infrastructure
    (`globalWitness_hypotheses_discharged`, width-agnostic); only narrow W3 replaces wide W3. -/
theorem globalWitness_residual_bound_inChart_unconditional_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
          IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
          (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
              * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
          (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
              * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀W, hr₀W, hboundinner⟩ := hbound (basepointInverseChart g gi hC hK) τ q hq hτ
  obtain ⟨δ, hδ, hdisch⟩ :=
    globalWitness_hypotheses_discharged g gi hC hK Θ u a b hw0smooth τ q hq
  refine ⟨min r₀W δ, lt_min hr₀W hδ, ?_⟩
  intro v hv hg1 hU hGGi hGiG
  have hvW : ‖v‖ < r₀W := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδ : ‖v‖ < δ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hgerm, hf⟩ := hdisch v hvδ
  exact hboundinner v hvW hgerm hg1 hf hU hGGi hGiG

/-- **★ M3 — narrow H1.**  `globalWitness_residual_bound_inChart_final` at width `gaussDdim (3/2·τ)`:
    the four far-point antecedents (`hg1`/`hU`/`hGGi`/`hGiG`) are discharged from the global data
    exactly as in the wide H1 (`metricInv_left_of_right` for the `gi·g = 1` side), leaving the clean
    per-base-point NARROW bound with ONLY genuine geometric/heat-side hypotheses. -/
theorem globalWitness_residual_bound_inChart_final_narrow (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart_unconditional_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀, hr₀, hboundinner⟩ := hbound τ q hq hτ
  refine ⟨r₀, hr₀, ?_⟩
  intro v hv
  refine hboundinner v hv ?_ ?_ ?_ ?_
  · intro a' b'; exact (hg a' b').contDiffAt.of_le le_top
  · exact hgnd (uniformFlowExp g gi hC hK q v)
  · intro pp cc; exact hinvF (uniformFlowExp g gi hC hK q v) pp cc
  · exact metricInv_left_of_right
      (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
      (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
      (hgnd (uniformFlowExp g gi hC hK q v))
      (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)

/-- **★★ M3 CAPSTONE — the CONSUMER-WIDTH per-base-point chart-Gaussian bound.**  Composing the narrow
    per-base-point bound (`globalWitness_residual_bound_inChart_final_narrow`, width `6τ`) with the A3
    chart transfer (`gaussDdim_le_gaussDdim_chart`, `c=3/2`, `d=2`) under the near-isometry width budget
    `hdisp` gives the CONSUMER width `gaussDdim (2τ) (φ_q v − q)`:
        `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdim (2τ) (φ_q v − q)`   (`‖v‖ < r₀`).
    This is the shape `RecenterReduction.hEboundW_of_uniform_perBasePoint` consumes — the width-margin
    re-plumb DELIVERS the consumer width, resolving the τ→0 obstruction of J4-94.

    `hdisp` is the ONE genuine, load-bearing physical input remaining: the recentring chart `φ_q` must be
    near-isometric enough that `(3/2)·‖φ_q v − q‖² ≤ 2·‖v‖²` (i.e. `‖φ_q v − q‖ ≤ √(4/3)·‖v‖`).  It is
    satisfiable and NON-vacuous (e.g. flat `g` with `φ_q v = q + v` gives `‖φ_q v − q‖ = ‖v‖`, and
    `3/2 ≤ 2`).  It is NOT derivable from the repo's current bounds (only a CONSTANT displacement bound
    `‖φ_q v − q‖ ≤ M` and a tube-confinement `≤ C₀‖v‖` with unbounded `C₀` exist; the near-isometry needs
    the joint jet-2 identity linearization `Dφ_q(0) = id`, part of the unbuilt uniform sub-tower).  NOT
    `a₁ = R/6`. -/
theorem globalWitness_residual_bound_chartGaussian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hdisp : ∀ q ∈ K, ∀ v : Point n,
        3 / 2 * rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ 2 * rncRadialSq v) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart_final_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B * Real.sqrt (2 / (3 / 2)) ^ n, ha, hab, by positivity, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀, hr₀, hboundinner⟩ := hbound τ q hq hτ
  refine ⟨r₀, hr₀, ?_⟩
  intro v hv
  have hnarrow := hboundinner v hv
  have htransfer :
      gaussDdim (3 / 2 * τ) v
        ≤ Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
    gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
      (hdisp q hq v)
  calc |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q|
      ≤ B * gaussDdim (3 / 2 * τ) v := hnarrow
    _ ≤ B * (Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) :=
        mul_le_mul_of_nonneg_left htransfer hB
    _ = B * Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by ring

end QIQTH.HeatResidualBound
