/-
  GaussianPolyBound — the polynomial-absorption Gaussian bound (Phase C4a).

  WHAT IS DERIVED HERE (the honest boundary — read it).
  This is the self-contained ANALYTIC TOOL that turns "Gaussian × polynomial" (the shape of the
  heat-parametrix residual `E`) into a clean Gaussian bound with a slightly widened Gaussian and an
  explicit `t`-power prefactor. Two facts:

    • `pow_mul_exp_neg_le_factorial` — the crude single-term exp-series bound:
        for `v ≥ 0`, `v^m · exp(−v) ≤ m!`.
      Route: Mathlib's `Real.pow_div_factorial_le_exp` gives `v^m / m! ≤ exp v`, hence
      `v^m ≤ exp v · m!`; multiply by `exp(−v)` and use `exp v · exp(−v) = 1`.

    • `gaussian_poly_absorb` — THE deliverable: for `m : ℕ`, `t > 0`, `x : ℝ`,
        `(x²)^m · exp(−x²/(4t)) ≤ (8^m · m!) · t^m · exp(−x²/(8t))`.
      Route: set `v = x²/(8t) ≥ 0`, so `x² = 8t·v`, `(x²)^m = 8^m t^m v^m`,
      `exp(−x²/(4t)) = exp(−2v) = exp(−v)·exp(−v)`, and absorb one `v^m·exp(−v) ≤ m!` by the
      lemma above. The surviving `exp(−v) = exp(−x²/(8t))` is the widened Gaussian.

  ⚠ HONEST SCOPE. This is the polynomial-absorption TOOL that the residual bound C4 will consume; it
  is NOT itself the residual bound (C4 still needs the off-diagonal parametrix — geodesic `r`,
  van-Vleck `Θ` as functions — a separate wall) and NOT the `a₁ = R/6` coefficient. The `m!` constant
  is deliberately crude (we do NOT chase the sharp `m^m e^{−m}`). All powers are `Nat`-powers on `x²`,
  so no `rpow`/`|x|` appears. No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.FlatHeatEquation

namespace QIQTH.GaussianPolyBound

set_option maxHeartbeats 400000

/-- **#1 — the crude single-term exp-series bound.** For `v ≥ 0` and `m : ℕ`,
    `v^m · exp(−v) ≤ m!`. From Mathlib's `Real.pow_div_factorial_le_exp` (`v^m/m! ≤ exp v`):
    `v^m ≤ exp v · m!`, then multiply by `exp(−v)` and use `exp v · exp(−v) = 1`. -/
theorem pow_mul_exp_neg_le_factorial {v : ℝ} (hv : 0 ≤ v) (m : ℕ) :
    v ^ m * Real.exp (-v) ≤ (m.factorial : ℝ) := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have h := Real.pow_div_factorial_le_exp v hv m
  -- `v^m / m! ≤ exp v` ⟹ `v^m ≤ exp v · m!`
  rw [div_le_iff₀ hfac] at h
  calc v ^ m * Real.exp (-v)
        ≤ (Real.exp v * (m.factorial : ℝ)) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (m.factorial : ℝ) * (Real.exp v * Real.exp (-v)) := by ring
    _ = (m.factorial : ℝ) := by rw [← Real.exp_add]; simp

/-- **#2 (THE DELIVERABLE) — the polynomial-absorption Gaussian bound.** For `m : ℕ`, `t > 0`,
    `x : ℝ`,
      `(x²)^m · exp(−x²/(4t)) ≤ (8^m · m!) · t^m · exp(−x²/(8t))`.
    Set `v = x²/(8t) ≥ 0`: then `x² = 8t·v`, `(x²)^m = 8^m t^m v^m`,
    `exp(−x²/(4t)) = exp(−2v) = exp(−v)·exp(−v)`; absorb one `v^m·exp(−v) ≤ m!` by `#1`, and the
    remaining `exp(−v) = exp(−x²/(8t))` is the widened Gaussian. All powers are `Nat`-powers. -/
theorem gaussian_poly_absorb (m : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (x ^ 2) ^ m * Real.exp (-(x ^ 2) / (4 * t)) ≤
      (8 ^ m * (m.factorial : ℝ)) * t ^ m * Real.exp (-(x ^ 2) / (8 * t)) := by
  have htne : t ≠ 0 := ht.ne'
  set v : ℝ := x ^ 2 / (8 * t) with hv_def
  have hv : 0 ≤ v := by rw [hv_def]; positivity
  -- `x² = 8t·v`
  have hx2 : x ^ 2 = 8 * t * v := by rw [hv_def]; field_simp
  -- `(x²)^m = 8^m · t^m · v^m`
  have hpow : (x ^ 2) ^ m = 8 ^ m * t ^ m * v ^ m := by
    rw [hx2, mul_pow, mul_pow]
  -- exponents in terms of `v`
  have hexp1 : -(x ^ 2) / (4 * t) = -v + -v := by rw [hx2]; field_simp; ring
  have hexp2 : -(x ^ 2) / (8 * t) = -v := by rw [hx2]; field_simp
  rw [hpow, hexp1, hexp2, Real.exp_add]
  -- crude single-term absorption
  have hkey : v ^ m * Real.exp (-v) ≤ (m.factorial : ℝ) := pow_mul_exp_neg_le_factorial hv m
  have hC : (0 : ℝ) ≤ 8 ^ m * t ^ m * Real.exp (-v) := by positivity
  calc 8 ^ m * t ^ m * v ^ m * (Real.exp (-v) * Real.exp (-v))
        = (8 ^ m * t ^ m * Real.exp (-v)) * (v ^ m * Real.exp (-v)) := by ring
    _ ≤ (8 ^ m * t ^ m * Real.exp (-v)) * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hkey hC
    _ = 8 ^ m * (m.factorial : ℝ) * t ^ m * Real.exp (-v) := by ring

/-! ### C4b — flat-Gaussian derivative bounds.

  The flat heat kernel's spatial derivatives, written as `(polynomial) × (kernel)` and bounded by a
  clean widened Gaussian via the C4a absorption tool `gaussian_poly_absorb`. These are the analytic
  TOOLS the C4 residual bound `E = (∂_t − Δ_g)H_N` will consume (differentiating the Gaussian factor
  of the parametrix ansatz). Recall `heatKernel1D t x = (√(4πt))⁻¹·exp(−x²/(4t))`.

  ⚠ HONEST SCOPE. These are the FLAT-Gaussian derivative tools only; they are NOT the residual bound
  itself (that needs the off-diagonal parametrix — geodesic `r`, van-Vleck `Θ` — C4c, a separate
  wall) and NOT the `a₁ = R/6` coefficient. No axioms, no `sorry`. -/

open QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation

/-- **C4b #1 — the first spatial derivative in product form.** For `t > 0`,
    `∂_x G_t(x) = (−x/(2t))·G_t(x)`. Immediate from `heatKernel1D_hasDerivAt_x`. -/
theorem heatKernel1D_deriv_x_eq (t x : ℝ) (ht : 0 < t) :
    deriv (fun x => heatKernel1D t x) x = (-x / (2 * t)) * heatKernel1D t x :=
  (heatKernel1D_hasDerivAt_x t x ht).deriv

/-- **C4b #2 — the second spatial derivative in product form.** For `t > 0`,
    `∂²_x G_t(x) = ((x² − 2t)/(4t²))·G_t(x)` (the `(x²/(4t²) − 1/(2t))·G` of `heatKernel1D_deriv2_x`
    put over the common denominator `4t²`). -/
theorem heatKernel1D_deriv2_x_eq (t x : ℝ) (ht : 0 < t) :
    deriv (fun x => deriv (fun x => heatKernel1D t x) x) x
      = ((x ^ 2 - 2 * t) / (4 * t ^ 2)) * heatKernel1D t x := by
  rw [heatKernel1D_deriv2_x t x ht]
  have htne : t ≠ 0 := ht.ne'
  congr 1
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **C4b #3 (THE REACHABLE PAYOFF) — the Gaussian bound on the Laplacian term.** For `t > 0`,
    `|∂²_x G_t(x)| ≤ (5/2)·t⁻¹·(√(4πt))⁻¹·exp(−x²/(8t))`.
    Route: `|∂²_x G| = (|x²−2t|/(4t²))·G ≤ ((x²+2t)/(4t²))·G` (split `|x²−2t| ≤ x²+2t`), then absorb
    `x²·exp(−x²/4t) ≤ 8t·exp(−x²/8t)` (C4a, `m=1`) and `exp(−x²/4t) ≤ exp(−x²/8t)` (C4a, `m=0`), giving
    numerator `≤ 10t·exp(−x²/8t)` and, over `4t²`, the constant `Cabs = 5/2`. The `(√(4πt))⁻¹`
    prefactor is kept (the widened Gaussian is `(√(4πt))⁻¹·exp(−x²/8t)`, NOT `heatKernel1D (2t)`). -/
theorem heatKernel1D_deriv2_x_abs_le (t x : ℝ) (ht : 0 < t) :
    |deriv (fun x => deriv (fun x => heatKernel1D t x) x) x|
      ≤ 5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (8 * t)) := by
  have htne : t ≠ 0 := ht.ne'
  have h4pit : (0 : ℝ) < 4 * Real.pi * t := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hApos : (0 : ℝ) < (Real.sqrt (4 * Real.pi * t))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr h4pit)
  have ht2 : (0 : ℝ) < 4 * t ^ 2 := mul_pos (by norm_num) (pow_pos ht 2)
  have h4t2ne : (4 : ℝ) * t ^ 2 ≠ 0 := ht2.ne'
  -- C4a single-term absorptions (m = 1 and m = 0)
  have hm1 : x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) ≤ 8 * t * Real.exp (-x ^ 2 / (8 * t)) := by
    simpa using gaussian_poly_absorb 1 ht x
  have hm0 : Real.exp (-x ^ 2 / (4 * t)) ≤ Real.exp (-x ^ 2 / (8 * t)) := by
    simpa using gaussian_poly_absorb 0 ht x
  -- |x²−2t| ≤ x²+2t
  have hnum_abs : |x ^ 2 - 2 * t| ≤ x ^ 2 + 2 * t := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, ht.le]
  have habs : |(x ^ 2 - 2 * t) / (4 * t ^ 2)| ≤ (x ^ 2 + 2 * t) / (4 * t ^ 2) := by
    rw [abs_div, abs_of_pos ht2, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum_abs (by positivity)
  -- numerator bound: (x²+2t)·exp(−x²/4t) ≤ 10t·exp(−x²/8t)
  have h2texp : 2 * t * Real.exp (-x ^ 2 / (4 * t)) ≤ 2 * t * Real.exp (-x ^ 2 / (8 * t)) :=
    mul_le_mul_of_nonneg_left hm0 (by linarith)
  have hnum : (x ^ 2 + 2 * t) * Real.exp (-x ^ 2 / (4 * t))
      ≤ 10 * t * Real.exp (-x ^ 2 / (8 * t)) := by
    calc (x ^ 2 + 2 * t) * Real.exp (-x ^ 2 / (4 * t))
        = x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) + 2 * t * Real.exp (-x ^ 2 / (4 * t)) := by ring
      _ ≤ 8 * t * Real.exp (-x ^ 2 / (8 * t)) + 2 * t * Real.exp (-x ^ 2 / (8 * t)) :=
          add_le_add hm1 h2texp
      _ = 10 * t * Real.exp (-x ^ 2 / (8 * t)) := by ring
  -- core Gaussian bound with the (√(4πt))⁻¹ prefactor stripped
  have hcore : (x ^ 2 + 2 * t) / (4 * t ^ 2) * Real.exp (-x ^ 2 / (4 * t))
      ≤ 5 / 2 * t⁻¹ * Real.exp (-x ^ 2 / (8 * t)) := by
    calc (x ^ 2 + 2 * t) / (4 * t ^ 2) * Real.exp (-x ^ 2 / (4 * t))
        = (x ^ 2 + 2 * t) * Real.exp (-x ^ 2 / (4 * t)) * (4 * t ^ 2)⁻¹ := by ring
      _ ≤ 10 * t * Real.exp (-x ^ 2 / (8 * t)) * (4 * t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = 5 / 2 * t⁻¹ * Real.exp (-x ^ 2 / (8 * t)) := by field_simp; ring
  rw [heatKernel1D_deriv2_x_eq t x ht, heatKernel1D]
  calc |(x ^ 2 - 2 * t) / (4 * t ^ 2)
          * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t)))|
      = |(x ^ 2 - 2 * t) / (4 * t ^ 2)|
          * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))) := by
        rw [abs_mul, abs_of_pos (mul_pos hApos (Real.exp_pos _))]
    _ ≤ (x ^ 2 + 2 * t) / (4 * t ^ 2)
          * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
    _ = (Real.sqrt (4 * Real.pi * t))⁻¹
          * ((x ^ 2 + 2 * t) / (4 * t ^ 2) * Real.exp (-x ^ 2 / (4 * t))) := by ring
    _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹
          * (5 / 2 * t⁻¹ * Real.exp (-x ^ 2 / (8 * t))) :=
        mul_le_mul_of_nonneg_left hcore hApos.le
    _ = 5 / 2 * t⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (8 * t)) := by ring

set_option maxHeartbeats 1000000 in
/-- **C4b #4 (THE ODD FIRST DERIVATIVE, √t honestly) — the Gaussian bound on the gradient term.**
    For `t > 0`, `|∂_x G_t(x)| ≤ √2·(√t)⁻¹·(√(4πt))⁻¹·exp(−x²/(8t))`.
    The odd `|x|` forces a `√t` (NOT an `rpow`): the crux is `|x|·exp(−x²/8t) ≤ √(8t)`, proved by
    squaring — `(|x|·exp(−x²/8t))² = x²·exp(−x²/4t) ≤ 8t` via C4a (`m=1`) and `exp(−x²/8t) ≤ 1`.
    Splitting `exp(−x²/4t) = exp(−x²/8t)²` then gives `|x|·exp(−x²/4t) ≤ √(8t)·exp(−x²/8t)`, and
    `√(8t)/(2t) = √2·(√t)⁻¹` yields the constant `√2`. -/
theorem heatKernel1D_deriv_x_abs_le (t x : ℝ) (ht : 0 < t) :
    |deriv (fun x => heatKernel1D t x) x|
      ≤ Real.sqrt 2 * (Real.sqrt t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹
        * Real.exp (-x ^ 2 / (8 * t)) := by
  have htne : t ≠ 0 := ht.ne'
  have h4pit : (0 : ℝ) < 4 * Real.pi * t := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hApos : (0 : ℝ) < (Real.sqrt (4 * Real.pi * t))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr h4pit)
  have h2t : (0 : ℝ) < 2 * t := by linarith
  -- C4a (m = 1): x²·exp(−x²/4t) ≤ 8t·exp(−x²/8t)
  have hm1 : x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) ≤ 8 * t * Real.exp (-x ^ 2 / (8 * t)) := by
    simpa using gaussian_poly_absorb 1 ht x
  -- exp(−x²/8t) ≤ 1
  have hle0 : -x ^ 2 / (8 * t) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 8 * t)]; nlinarith [sq_nonneg x]
  have hexp1 : Real.exp (-x ^ 2 / (8 * t)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hle0
  -- x²·exp(−x²/4t) ≤ 8t
  have hle8t : x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) ≤ 8 * t := by
    calc x ^ 2 * Real.exp (-x ^ 2 / (4 * t))
          ≤ 8 * t * Real.exp (-x ^ 2 / (8 * t)) := hm1
      _ ≤ 8 * t * 1 := by apply mul_le_mul_of_nonneg_left hexp1; linarith
      _ = 8 * t := by ring
  -- (|x|·exp(−x²/8t))² = x²·exp(−x²/4t)
  have hsq : (|x| * Real.exp (-x ^ 2 / (8 * t))) ^ 2 = x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) := by
    have hexp : -x ^ 2 / (8 * t) + -x ^ 2 / (8 * t) = -x ^ 2 / (4 * t) := by field_simp; ring
    rw [mul_pow, sq_abs, pow_two (Real.exp (-x ^ 2 / (8 * t))), ← Real.exp_add, hexp]
  -- crux odd bound: |x|·exp(−x²/8t) ≤ √(8t)
  have hcrux : |x| * Real.exp (-x ^ 2 / (8 * t)) ≤ Real.sqrt (8 * t) := by
    rw [show |x| * Real.exp (-x ^ 2 / (8 * t))
          = Real.sqrt ((|x| * Real.exp (-x ^ 2 / (8 * t))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [hsq]; exact hle8t
  -- split the exponent
  have hexp_split : Real.exp (-x ^ 2 / (4 * t))
      = Real.exp (-x ^ 2 / (8 * t)) * Real.exp (-x ^ 2 / (8 * t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hxexp4 : |x| * Real.exp (-x ^ 2 / (4 * t))
      ≤ Real.sqrt (8 * t) * Real.exp (-x ^ 2 / (8 * t)) := by
    rw [hexp_split, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcrux (Real.exp_pos _).le
  -- √(8t) = 2·√2·√t  and  √(8t)/(2t) = √2·(√t)⁻¹
  have h8t : Real.sqrt (8 * t) = 2 * Real.sqrt 2 * Real.sqrt t := by
    rw [show (8 : ℝ) * t = 2 ^ 2 * (2 * t) from by ring,
        Real.sqrt_mul (by positivity) (2 * t), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) t]
    ring
  have hsqrt8 : Real.sqrt (8 * t) / (2 * t) = Real.sqrt 2 * (Real.sqrt t)⁻¹ := by
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    rw [h8t, show (2 : ℝ) * t = 2 * (Real.sqrt t * Real.sqrt t) from by
          rw [Real.mul_self_sqrt ht.le]]
    field_simp
  rw [heatKernel1D_deriv_x_eq t x ht, heatKernel1D]
  calc |(-x / (2 * t)) * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t)))|
      = |x| / (2 * t) * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))) := by
        rw [abs_mul, abs_of_pos (mul_pos hApos (Real.exp_pos _)), abs_div, abs_neg,
            abs_of_pos h2t]
    _ = (Real.sqrt (4 * Real.pi * t))⁻¹ / (2 * t) * (|x| * Real.exp (-x ^ 2 / (4 * t))) := by
        ring
    _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ / (2 * t)
          * (Real.sqrt (8 * t) * Real.exp (-x ^ 2 / (8 * t))) :=
        mul_le_mul_of_nonneg_left hxexp4 (div_nonneg hApos.le (by linarith))
    _ = Real.sqrt (8 * t) / (2 * t) * (Real.sqrt (4 * Real.pi * t))⁻¹
          * Real.exp (-x ^ 2 / (8 * t)) := by ring
    _ = Real.sqrt 2 * (Real.sqrt t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹
          * Real.exp (-x ^ 2 / (8 * t)) := by rw [hsqrt8]

end QIQTH.GaussianPolyBound
