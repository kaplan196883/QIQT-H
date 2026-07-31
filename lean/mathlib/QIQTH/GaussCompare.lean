/-
  GaussCompare — the Gaussian width-comparison tool for the hcoord width-fix (Brick H2).

  This file provides the elementary real-analysis lemma that converts a near-isometry displacement
  bound `c²·‖w‖² ≤ ‖u‖²` (i.e. `‖u‖ ≥ c‖w‖`, `0 < c ≤ 1`) into a Gaussian comparison with a WIDENED
  right-hand Gaussian:

      `gaussDdim (2τ) u  ≤  (cⁿ)⁻¹ · gaussDdim (2τ/c²) w` .

  The point: distorting the argument of a Gaussian by a near-isometry `c` is absorbed by (i) widening
  the Gaussian (`2τ → 2τ/c²`, larger variance) and (ii) a bounded normalization constant `c⁻ⁿ`.  This
  is the shape the exp-local-inverse `hcoord` width-fix consumes.

  Fully DERIVED from `gaussDdim_eq_exp` (closed exponential form).  Both sides are computed explicitly:
    • LHS = `(√(8πτ))⁻ⁿ · exp(−‖u‖²/(8τ))`;
    • the widened partner `gaussDdim (2τ/c²) w = (√(8πτ/c²))⁻ⁿ · exp(−c²‖w‖²/(8τ))`, and the prefactor
      `(√(8πτ/c²))⁻ⁿ = cⁿ·(√(8πτ))⁻ⁿ` (since `√(x/c²)=√x/c`), so `c⁻ⁿ` cancels the `cⁿ`.
  The claim then reduces to `exp(−‖u‖²/(8τ)) ≤ exp(−c²‖w‖²/(8τ))`, i.e. `c²‖w‖² ≤ ‖u‖²` — the hypothesis.

  No axioms beyond `propext, Classical.choice, Quot.sound`.  No `sorry`.
-/
import Mathlib
import QIQTH.ResidueBound

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.ResidueBound
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **Gaussian width-comparison (near-isometry ⟹ widened Gaussian).**  If `c²·‖w‖² ≤ ‖u‖²`
    (a near-isometry displacement bound `‖u‖ ≥ c‖w‖`, `0 < c`), then the heat Gaussian at `u` and
    width `2τ` is dominated by the WIDENED Gaussian at `w` and width `2τ/c²`, up to the bounded
    normalization constant `c⁻ⁿ`:

        `gaussDdim (2τ) u ≤ (cⁿ)⁻¹ · gaussDdim (2τ/c²) w` .

    Derived from the closed exponential form `gaussDdim_eq_exp`: the prefactor
    `(√(8πτ/c²))⁻ⁿ = cⁿ·(√(8πτ))⁻ⁿ` cancels the `c⁻ⁿ`, reducing the claim to the monotone
    `exp(−‖u‖²/(8τ)) ≤ exp(−c²‖w‖²/(8τ))`, which is exactly the hypothesis `hnorm` (with `8τ > 0`). -/
theorem gaussDdim_le_of_norm_ge {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    {u w : Point n} (hnorm : c ^ 2 * rncRadialSq w ≤ rncRadialSq u) :
    gaussDdim (2 * τ) u ≤ (c ^ n)⁻¹ * gaussDdim (2 * τ / c ^ 2) w := by
  have hcn0 : (c : ℝ) ^ n ≠ 0 := by positivity
  have h8t : (0 : ℝ) < 8 * τ := by positivity
  have harg0 : (0 : ℝ) ≤ 4 * Real.pi * (2 * τ) := by positivity
  -- Prefactor identity: `(√(4π·2τ/c²))⁻¹ = c · (√(4π·2τ))⁻¹`.
  have hpre : (Real.sqrt (4 * Real.pi * (2 * τ / c ^ 2)))⁻¹
      = c * (Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹ := by
    have harg : 4 * Real.pi * (2 * τ / c ^ 2) = (4 * Real.pi * (2 * τ)) * (1 / c) ^ 2 := by ring
    rw [harg, Real.sqrt_mul harg0, Real.sqrt_sq_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / c by positivity), mul_inv, one_div, inv_inv, mul_comm]
  -- Exponent monotonicity: `exp(−‖u‖²/(8τ)) ≤ exp(−c²‖w‖²/(8τ))`, from `hnorm`.
  have hExpLe : Real.exp (-(rncRadialSq u) / (4 * (2 * τ)))
      ≤ Real.exp (-(rncRadialSq w) / (4 * (2 * τ / c ^ 2))) := by
    apply Real.exp_le_exp.mpr
    rw [show (4 : ℝ) * (2 * τ) = 8 * τ by ring,
        show (4 : ℝ) * (2 * τ / c ^ 2) = (8 * τ) / c ^ 2 by ring,
        div_div_eq_mul_div, div_le_div_iff_of_pos_right h8t]
    nlinarith [hnorm]
  -- Assemble: compute both Gaussians, cancel `c⁻ⁿ·cⁿ`, compare exponentials.
  rw [gaussDdim_eq_exp (2 * τ) u, gaussDdim_eq_exp (2 * τ / c ^ 2) w, hpre, mul_pow,
      mul_assoc ((c : ℝ) ^ n) (((Real.sqrt (4 * Real.pi * (2 * τ)))⁻¹) ^ n)
        (Real.exp (-(rncRadialSq w) / (4 * (2 * τ / c ^ 2)))),
      inv_mul_cancel_left₀ hcn0]
  exact mul_le_mul_of_nonneg_left hExpLe (by positivity)

end QIQTH.HeatResidualBound
