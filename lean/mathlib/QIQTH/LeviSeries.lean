/-
  LeviSeries — the MODEL Levi/Duhamel Neumann series CONVERGES (Phase C5a of the
  convergence-infrastructure campaign, docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md).

  This is the conceptual payoff of C3 (`TimeSimplexBeta.iterKernel_eq`): the factorial (Γ)
  decay actually PRODUCES a convergent series.

  WHAT LANDS HERE.

    • `modelCoeff α t k = Γ(α+1)^k / Γ(k·(α+1)) · t^(k·(α+1) − 1)` — the `iterKernel_eq` RHS
      stripped of the k-constant Gaussian factor `gaussDdim t (x−y)`.

    • `gamma_ratio_tendsto_zero` — the crux Γ estimate: for `β ≥ 1`,
        `Γ((k+1)β) / Γ((k+2)β) → 0`  as  `k → ∞`,
      because `Γ((k+2)β) = Γ((k+1)β + β) ≥ ((k+1)β)·Γ((k+1)β)` (Γ_add_one for the +1 step,
      Γ-monotonicity on `[2,∞)` for the remaining `β−1 ≥ 0`), so the ratio `≤ 1/((k+1)β) → 0`.

    • `modelCoeff_summable` — THE deliverable: for `α ≥ 0`, `t > 0`,
        `Summable (fun k => modelCoeff α t (k+1))`,
      via Mathlib's ratio test (`summable_of_ratio_test_tendsto_lt_one`, l = 0) fed the ratio
      estimate above.

    • `iterKernel_series_summable` — the corollary tying back to C3: for `α ≥ 0`, `t > 0`,
        `Summable (fun k => iterKernel α (k+1) t x y)`,
      since each term is `modelCoeff α t (k+1) · gaussDdim t (x−y)` (`iterKernel_eq`, `k+1 ≥ 1`).

  ⚠ HONEST SCOPE.  This is the MODEL (flat self-similar) series convergence.  It is NOT the true
  curved-kernel residual bound (C4), the domination step (C5b), the capstone (C6), or `a₁ = R/6`.
  No axioms beyond the standard three, no `sorry`.
-/
import Mathlib
import QIQTH.TimeSimplexBeta

open Real MeasureTheory Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TimeSimplexBeta

namespace QIQTH.LeviSeries

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ### 1. The model coefficient. -/

/-- **The model coefficient** `modelCoeff α t k = Γ(α+1)^k / Γ(k·(α+1)) · t^(k·(α+1) − 1)` — the
    RHS of `TimeSimplexBeta.iterKernel_eq` with the `k`-constant Gaussian factor removed (`^` on
    `t` is `Real.rpow`). -/
noncomputable def modelCoeff (α t : ℝ) (k : ℕ) : ℝ :=
  Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)) * t ^ ((k : ℝ) * (α + 1) - 1)

/-- Positivity of the model coefficient for `α > −1`, `t > 0`, and `k ≥ 1` (so `k·(α+1) > 0`). -/
theorem modelCoeff_pos (α t : ℝ) (hα : -1 < α) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    0 < modelCoeff α t k := by
  have hβ0 : (0 : ℝ) < α + 1 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkβ : (0 : ℝ) < (k : ℝ) * (α + 1) := mul_pos (by linarith) hβ0
  have hC : (0 : ℝ) < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos hβ0
  have hGk : (0 : ℝ) < Real.Gamma ((k : ℝ) * (α + 1)) := Real.Gamma_pos_of_pos hkβ
  unfold modelCoeff
  exact mul_pos (div_pos (pow_pos hC k) hGk) (Real.rpow_pos_of_pos ht _)

/-! ### 2. The crux Γ-ratio estimate. -/

/-- **★ THE CRUX Γ ESTIMATE.**  For `β ≥ 1`, the ratio `Γ((k+1)β) / Γ((k+2)β) → 0` as `k → ∞`.
    Bounded above by `1/((k+1)β)` because `Γ((k+2)β) = Γ((k+1)β + β) ≥ ((k+1)β)·Γ((k+1)β)`
    (the `+1` step is `Real.Gamma_add_one` EXACTLY; the remaining `+1 → +β` bump is Γ-monotonicity
    on `[2,∞)`, `Real.Gamma_strictMonoOn_Ici`), and `1/((k+1)β) → 0`. -/
theorem gamma_ratio_tendsto_zero (β : ℝ) (hβ : 1 ≤ β) :
    Tendsto (fun k : ℕ => Real.Gamma (((k : ℝ) + 1) * β) / Real.Gamma (((k : ℝ) + 2) * β))
      atTop (𝓝 0) := by
  have hβ0 : (0 : ℝ) < β := by linarith
  -- Upper bound function `u k = (((k:ℝ)+1)*β)⁻¹ → 0`.
  have hu_top : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * β) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact h1.atTop_mul_const hβ0
  have hu : Tendsto (fun k : ℕ => (((k : ℝ) + 1) * β)⁻¹) atTop (𝓝 0) :=
    hu_top.inv_tendsto_atTop
  -- Squeeze `0 ≤ ratio ≤ u`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    tendsto_const_nhds hu (fun k => ?_) (fun k => ?_)
  · -- lower bound: ratio ≥ 0
    have h1 : (0 : ℝ) < ((k : ℝ) + 1) * β := mul_pos (by positivity) hβ0
    have h2 : (0 : ℝ) < ((k : ℝ) + 2) * β := mul_pos (by positivity) hβ0
    exact le_of_lt (div_pos (Real.Gamma_pos_of_pos h1) (Real.Gamma_pos_of_pos h2))
  · -- upper bound: ratio ≤ (((k:ℝ)+1)*β)⁻¹
    set z : ℝ := ((k : ℝ) + 1) * β with hzdef
    have hz : 0 < z := mul_pos (by positivity) hβ0
    have hz1 : (1 : ℝ) ≤ z := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((k : ℝ) + 1) * β := mul_le_mul (by linarith) hβ (by norm_num) (by linarith)
    have hΓz : (0 : ℝ) < Real.Gamma z := Real.Gamma_pos_of_pos hz
    -- key: z · Γ(z) ≤ Γ((k+2)β) = Γ(z + β)
    have hzb : ((k : ℝ) + 2) * β = z + β := by rw [hzdef]; ring
    have hmem1 : z + 1 ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr (by linarith)
    have hmem2 : z + β ∈ Set.Ici (2 : ℝ) := Set.mem_Ici.mpr (by linarith)
    have hmono : Real.Gamma (z + 1) ≤ Real.Gamma (z + β) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hmem1 hmem2 (by linarith)
    have hbound : z * Real.Gamma z ≤ Real.Gamma (((k : ℝ) + 2) * β) := by
      rw [hzb, ← Real.Gamma_add_one hz.ne']
      exact hmono
    -- turn the bound into the ratio bound
    rw [hzb]
    rw [div_le_iff₀ (Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < z + β))]
    have hstep : Real.Gamma z ≤ z⁻¹ * Real.Gamma (z + β) := by
      have hb2 : z * Real.Gamma z ≤ Real.Gamma (z + β) := by rw [hzb] at hbound; exact hbound
      have := mul_le_mul_of_nonneg_left hb2 (le_of_lt (inv_pos.mpr hz))
      rwa [inv_mul_cancel_left₀ hz.ne'] at this
    exact hstep

/-! ### 3. The model coefficient series is summable (THE deliverable). -/

/-- The successive-coefficient ratio, computed explicitly:
    `modelCoeff α t (k+2) / modelCoeff α t (k+1)
       = (Γ(α+1)·t^(α+1)) · (Γ((k+1)(α+1)) / Γ((k+2)(α+1)))`. -/
theorem modelCoeff_ratio_eq (α t : ℝ) (hα : 0 ≤ α) (ht : 0 < t) (k : ℕ) :
    modelCoeff α t (k + 2) / modelCoeff α t (k + 1)
      = (Real.Gamma (α + 1) * t ^ (α + 1))
          * (Real.Gamma (((k : ℝ) + 1) * (α + 1)) / Real.Gamma (((k : ℝ) + 2) * (α + 1))) := by
  have hβ0 : (0 : ℝ) < α + 1 := by linarith
  have hC : (0 : ℝ) < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos hβ0
  have ha1 : (0 : ℝ) < ((k : ℝ) + 1) * (α + 1) := mul_pos (by positivity) hβ0
  have ha2 : (0 : ℝ) < ((k : ℝ) + 2) * (α + 1) := mul_pos (by positivity) hβ0
  have hGa1 : Real.Gamma (((k : ℝ) + 1) * (α + 1)) ≠ 0 := (Real.Gamma_pos_of_pos ha1).ne'
  have hGa2 : Real.Gamma (((k : ℝ) + 2) * (α + 1)) ≠ 0 := (Real.Gamma_pos_of_pos ha2).ne'
  have hden : modelCoeff α t (k + 1) ≠ 0 :=
    (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1)).ne'
  -- Prove the product identity `modelCoeff (k+2) = RHS · modelCoeff (k+1)`, then divide.
  have hprod : modelCoeff α t (k + 2)
      = ((Real.Gamma (α + 1) * t ^ (α + 1))
          * (Real.Gamma (((k : ℝ) + 1) * (α + 1)) / Real.Gamma (((k : ℝ) + 2) * (α + 1))))
        * modelCoeff α t (k + 1) := by
    simp only [modelCoeff]
    push_cast
    rw [show ((k : ℝ) + 2) * (α + 1) - 1 = (α + 1) + (((k : ℝ) + 1) * (α + 1) - 1) from by ring,
        Real.rpow_add ht (α + 1) (((k : ℝ) + 1) * (α + 1) - 1),
        pow_succ (Real.Gamma (α + 1)) (k + 1)]
    field_simp
  rw [hprod, mul_div_assoc, div_self hden, mul_one]

/-- The successive-coefficient ratio tends to `0`. -/
theorem modelCoeff_ratio_tendsto_zero (α t : ℝ) (hα : 0 ≤ α) (ht : 0 < t) :
    Tendsto (fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1)) atTop (𝓝 0) := by
  have hkey : (fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1))
      = fun k : ℕ => (Real.Gamma (α + 1) * t ^ (α + 1))
          * (Real.Gamma (((k : ℝ) + 1) * (α + 1)) / Real.Gamma (((k : ℝ) + 2) * (α + 1))) := by
    funext k; exact modelCoeff_ratio_eq α t hα ht k
  rw [hkey]
  have hg := gamma_ratio_tendsto_zero (α + 1) (by linarith)
  simpa using hg.const_mul (Real.Gamma (α + 1) * t ^ (α + 1))

/-- **★ THE DELIVERABLE (Phase C5a).**  For `α ≥ 0` (so `β = α+1 ≥ 1`) and `t > 0`, the model
    coefficient series (index shifted so the `k+1 ≥ 1` branch applies) is summable:
        `Summable (fun k => modelCoeff α t (k+1))`.
    The Γ-ratio estimate (`gamma_ratio_tendsto_zero`) drives the term ratio to `0`, and Mathlib's
    ratio test (`summable_of_ratio_test_tendsto_lt_one`, `l = 0 < 1`) concludes.  This is the
    "convergence is real" theorem: the factorial (Γ) decay produces a convergent Neumann series. -/
theorem modelCoeff_summable (α t : ℝ) (hα : 0 ≤ α) (ht : 0 < t) :
    Summable (fun k : ℕ => modelCoeff α t (k + 1)) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
  · -- eventually nonzero (in fact all terms positive)
    exact Eventually.of_forall
      (fun k => (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1)).ne')
  · -- the norm-ratio tends to 0
    have hnorm : (fun k : ℕ => ‖modelCoeff α t (k + 1 + 1)‖ / ‖modelCoeff α t (k + 1)‖)
        = fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1) := by
      funext k
      rw [Real.norm_of_nonneg (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1 + 1)).le,
          Real.norm_of_nonneg (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1)).le]
    rw [hnorm]
    exact modelCoeff_ratio_tendsto_zero α t hα ht

/-! ### 4. Corollary: the iterated-kernel series converges (ties back to C3). -/

/-- **The model iterated-kernel series converges.**  For `α ≥ 0`, `t > 0`, and `x y : Point n`,
        `Summable (fun k => iterKernel α (k+1) t x y)`.
    Each term factors as `modelCoeff α t (k+1) · gaussDdim t (x−y)` by `TimeSimplexBeta.iterKernel_eq`
    (`k+1 ≥ 1`), a `k`-constant Gaussian times the summable model coefficient. -/
theorem iterKernel_series_summable (α t : ℝ) (hα : 0 ≤ α) (ht : 0 < t) (x y : Point n) :
    Summable (fun k : ℕ => iterKernel α (k + 1) t x y) := by
  have heq : (fun k : ℕ => iterKernel α (k + 1) t x y)
      = fun k : ℕ => modelCoeff α t (k + 1) * gaussDdim t (x - y) := by
    funext k
    rw [iterKernel_eq α (by linarith) t ht x y (by omega : 1 ≤ k + 1)]
    unfold modelCoeff
    ring
  rw [heq]
  exact (modelCoeff_summable α t hα ht).mul_right _

end QIQTH.LeviSeries
