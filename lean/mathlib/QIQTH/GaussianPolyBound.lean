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

end QIQTH.GaussianPolyBound
