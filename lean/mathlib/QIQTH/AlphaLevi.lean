/-
  AlphaLevi — J4-611: the α-generalization slice of the Levi-series summability engine.

  WHY.  J4-610 (FrozenDefect) banked the τ^{−1/2} frozen-defect bound
      `|E| ≤ (C/√τ)·G_{2τ}`  =  `C · baseKernelW 2 (−1/2) τ p q`,
  i.e. an α = −1/2, κ = 2 one-step Levi bound.  The per-step engine (`betaTimeIntegral_eq`,
  `iterKernelW_eq`, `gaussTimePow_conv_beta_scaled`, `iterConvW_bound_le`) already works for all
  `α > −1` UNCHANGED.  Exactly TWO localized blockers kept the D2 Neumann machinery at `α ≥ 0`:

    BLOCKER 1 — `LeviSeries.gamma_ratio_tendsto_zero` (the series-summability Γ-ratio crux) was
    proved only for `β = α+1 ≥ 1`, via Γ-monotonicity on `[2,∞)` (`Γ(z+β) ≥ Γ(z+1)` needs `β ≥ 1`).
    THE FIX (this file, `gamma_ratio_tendsto_zero_general`): for `0 < β ≤ 1` use LOG-CONVEXITY of Γ
    (`Real.convexOn_log_Gamma`, Bohr–Mollerup) the OTHER way: interpolate `x+1` between `x+β` and
    `x+β+1` with weights `(β, 1−β)`:
        `Γ(x+1) ≤ Γ(x+β)^β · Γ(x+β+1)^{1−β} = Γ(x+β) · (x+β)^{1−β}`   (Γ_add_one),
    i.e. `x·Γ(x) ≤ Γ(x+β)·(x+β)^{1−β}`, whence
        `Γ(x)/Γ(x+β) ≤ (x+β)^{1−β}/x ≤ 2^{1−β}·x^{−β} → 0`   (x = (k+1)β → ∞).
    This is the Gautschi-type lower Γ-ratio bound, derived directly from log-convexity.

    BLOCKER 2 — `leviSeries_dominatedW_le` (GatedWitnessPackage, the top D2 consumer) hard-coded
    `κ = 2, α = 0`, AND its `τ ↦ T` coefficient-monotonicity step (`τ^k ≤ T^k`) fails at `α < 0`
    (the `k = 0` term carries `τ^α`, DECREASING in `τ`).
    THE FIX (`leviSeries_dominatedW_le_alpha`): split the exponent honestly,
        `τ^{(k+1)(α+1)−1} = τ^α · τ^{k(α+1)}`,   `k(α+1) ≥ 0`,
    so only the NONNEGATIVE part is sent `τ ↦ T`; the sharp `τ^α` weight survives into the
    conclusion, which keeps the SAME shape as the one-step bound:
        `|leviSeries E τ p q| ≤ C_L · baseKernelW 2 α τ p q`,
        `C_L = T^{−α} · ∑' k, C^{k+1}·modelCoeff α T (k+1)`.

  ⚠ HONEST α = −1/2 SHAPE (NO-FALSE-BOUND).  At α = −1/2 the series bound is
      `|leviSeries E τ p q| ≤ (C_L/√τ) · G_{2τ}(p−q)`  —  the series INHERITS the `τ^{−1/2}`
  weight of the one-step defect bound.  It is NOT bounded by any clean `const · G_{2τ}` as
  `τ → 0` (certified: `negHalf_weight_exceeds_one`, `negHalf_weight_unbounded`).  Who downstream
  can consume a `τ^{−1/2}`-weighted series bound (the hContDom/hInnerCont window, the final-rate
  audit) is the NEXT brick's question — nothing about that is claimed here.

  ⚠ SPLICE DISCIPLINE.  The existing engine files (LeviSeries, GaussianWidthTolerant,
  ParametrixHEboundWiring, RestrictedEboundW, GatedWitnessPackage) are NOT modified; this file
  adds `_general` VARIANTS that re-prove the four summability lemmas at `α > −1` and an
  α-parametrized top consumer, reusing the unchanged per-step engine.

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL (flat tower non-vacuous and closed; curved
  owes: the downstream consumer of the τ^{−1/2}-weighted series bound, the per-q re-based
  producer re-assembly, the fat-K hEmeas/hAdom/hcont piles, the capstone co-instantiation, and
  the prior piles).  This brick is the α series slice ONLY.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.RestrictedEboundW
import QIQTH.ParametrixHEboundWiring

open Filter Topology MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound

namespace QIQTH.AlphaLevi

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. BLOCKER 1 — the Γ-ratio estimate for `0 < β ≤ 1` via log-convexity. -/

/-- **The Gautschi-type log-convexity lower bound.**  For `x > 0` and `0 < β ≤ 1`,
        `x·Γ(x) ≤ Γ(x+β)·(x+β)^{1−β}`.
    Route: `x+1 = β·(x+β) + (1−β)·(x+β+1)`, so log-convexity of Γ (`Real.convexOn_log_Gamma`)
    gives `Γ(x+1) ≤ Γ(x+β)^β·Γ(x+β+1)^{1−β}`; then `Γ(x+β+1) = (x+β)·Γ(x+β)` telescopes the
    right side to `Γ(x+β)·(x+β)^{1−β}` and `Γ(x+1) = x·Γ(x)` the left. -/
theorem gamma_mul_le_gamma_add_rpow (x β : ℝ) (hx : 0 < x) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    x * Real.Gamma x ≤ Real.Gamma (x + β) * (x + β) ^ (1 - β) := by
  have ha : (0 : ℝ) < x + β := by linarith
  have ha1 : (0 : ℝ) < x + β + 1 := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hΓa : (0 : ℝ) < Real.Gamma (x + β) := Real.Gamma_pos_of_pos ha
  have hΓa1 : (0 : ℝ) < Real.Gamma (x + β + 1) := Real.Gamma_pos_of_pos ha1
  have hΓx1 : (0 : ℝ) < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos hx1
  -- log-convexity at the pair (x+β, x+β+1) with weights (β, 1−β)
  have hconv := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr ha1)
    hβ0.le (by linarith : (0 : ℝ) ≤ 1 - β) (by ring : β + (1 - β) = 1)
  have hpt : β • (x + β) + (1 - β) • (x + β + 1) = x + 1 := by
    simp only [smul_eq_mul]; ring
  rw [hpt] at hconv
  simp only [Function.comp_apply, smul_eq_mul] at hconv
  -- exponentiate: Γ(x+1) ≤ Γ(x+β)^β · Γ(x+β+1)^{1−β}
  have key : Real.Gamma (x + 1)
      ≤ Real.Gamma (x + β) ^ (β : ℝ) * Real.Gamma (x + β + 1) ^ (1 - β) := by
    calc Real.Gamma (x + 1)
        = Real.exp (Real.log (Real.Gamma (x + 1))) := (Real.exp_log hΓx1).symm
      _ ≤ Real.exp (β * Real.log (Real.Gamma (x + β))
            + (1 - β) * Real.log (Real.Gamma (x + β + 1))) := Real.exp_le_exp.mpr hconv
      _ = Real.exp (Real.log (Real.Gamma (x + β)) * β)
            * Real.exp (Real.log (Real.Gamma (x + β + 1)) * (1 - β)) := by
          rw [Real.exp_add, mul_comm β, mul_comm (1 - β)]
      _ = Real.Gamma (x + β) ^ (β : ℝ) * Real.Gamma (x + β + 1) ^ (1 - β) := by
          rw [← Real.rpow_def_of_pos hΓa, ← Real.rpow_def_of_pos hΓa1]
  -- telescope both sides
  rw [Real.Gamma_add_one hx.ne', Real.Gamma_add_one ha.ne'] at key
  have hRHS : Real.Gamma (x + β) ^ (β : ℝ) * ((x + β) * Real.Gamma (x + β)) ^ (1 - β)
      = Real.Gamma (x + β) * (x + β) ^ (1 - β) := by
    rw [Real.mul_rpow ha.le hΓa.le,
        show Real.Gamma (x + β) ^ (β : ℝ) * ((x + β) ^ (1 - β) * Real.Gamma (x + β) ^ (1 - β))
          = (Real.Gamma (x + β) ^ (β : ℝ) * Real.Gamma (x + β) ^ (1 - β)) * (x + β) ^ (1 - β)
          from by ring,
        ← Real.rpow_add hΓa, show β + (1 - β) = (1 : ℝ) from by ring, Real.rpow_one]
  rw [hRHS] at key
  exact key

/-- **The Γ-ratio upper bound for `0 < β ≤ 1`.**  For `x > 0`,
        `Γ(x)/Γ(x+β) ≤ (x+β)^{1−β}/x`. -/
theorem gamma_ratio_le_rpow (x β : ℝ) (hx : 0 < x) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Real.Gamma x / Real.Gamma (x + β) ≤ (x + β) ^ (1 - β) / x := by
  have ha : (0 : ℝ) < x + β := by linarith
  have hΓa : (0 : ℝ) < Real.Gamma (x + β) := Real.Gamma_pos_of_pos ha
  rw [div_le_div_iff₀ hΓa hx]
  have h := gamma_mul_le_gamma_add_rpow x β hx hβ0 hβ1
  have h1 : Real.Gamma x * x = x * Real.Gamma x := mul_comm _ _
  have h2 : (x + β) ^ (1 - β) * Real.Gamma (x + β)
      = Real.Gamma (x + β) * (x + β) ^ (1 - β) := mul_comm _ _
  linarith

/-- **The Γ-ratio tends to zero for `0 < β ≤ 1`** (the sub-unit companion of
    `LeviSeries.gamma_ratio_tendsto_zero`).  Squeeze against
    `2^{1−β}·((k+1)β)^{−β} → 0` (`tendsto_rpow_neg_atTop`), the Gautschi-type bound supplying
        `Γ((k+1)β)/Γ((k+2)β) ≤ ((k+2)β)^{1−β}/((k+1)β) ≤ 2^{1−β}·((k+1)β)^{−β}`
    (`(k+2)β ≤ 2·(k+1)β`). -/
theorem gamma_ratio_tendsto_zero_lt_one (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Tendsto (fun k : ℕ => Real.Gamma (((k : ℝ) + 1) * β) / Real.Gamma (((k : ℝ) + 2) * β))
      atTop (𝓝 0) := by
  -- the upper-bound sequence tends to 0
  have hu_top : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * β) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact h1.atTop_mul_const hβ0
  have hu0 : Tendsto (fun k : ℕ => (((k : ℝ) + 1) * β) ^ (-β)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hβ0).comp hu_top
  have hu : Tendsto (fun k : ℕ => (2 : ℝ) ^ (1 - β) * (((k : ℝ) + 1) * β) ^ (-β))
      atTop (𝓝 0) := by
    simpa using hu0.const_mul ((2 : ℝ) ^ (1 - β))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    tendsto_const_nhds hu (fun k => ?_) (fun k => ?_)
  · -- lower bound: ratio ≥ 0
    have h1 : (0 : ℝ) < ((k : ℝ) + 1) * β := mul_pos (by positivity) hβ0
    have h2 : (0 : ℝ) < ((k : ℝ) + 2) * β := mul_pos (by positivity) hβ0
    exact le_of_lt (div_pos (Real.Gamma_pos_of_pos h1) (Real.Gamma_pos_of_pos h2))
  · -- upper bound
    set x : ℝ := ((k : ℝ) + 1) * β with hxdef
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hx : 0 < x := mul_pos (by positivity) hβ0
    have hβx : β ≤ x := by
      rw [hxdef]; nlinarith
    have hxβ : ((k : ℝ) + 2) * β = x + β := by rw [hxdef]; ring
    rw [hxβ]
    calc Real.Gamma x / Real.Gamma (x + β)
        ≤ (x + β) ^ (1 - β) / x := gamma_ratio_le_rpow x β hx hβ0 hβ1
      _ ≤ (2 * x) ^ (1 - β) / x := by
          have hbase : x + β ≤ 2 * x := by linarith
          have hnum : (x + β) ^ (1 - β) ≤ (2 * x) ^ (1 - β) :=
            Real.rpow_le_rpow (by positivity) hbase (by linarith)
          exact div_le_div_of_nonneg_right hnum hx.le
      _ = (2 : ℝ) ^ (1 - β) * x ^ (-β) := by
          have hxpow : x ^ (1 - β) = x * x ^ (-β) := by
            rw [show (1 - β : ℝ) = 1 + -β from by ring, Real.rpow_add hx, Real.rpow_one]
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le, hxpow,
              mul_comm x (x ^ (-β)), ← mul_assoc, mul_div_assoc, div_self hx.ne', mul_one]

/-- **★ BLOCKER 1 DISCHARGED — the Γ-ratio estimate for ALL `β > 0`.**
        `Γ((k+1)β)/Γ((k+2)β) → 0`  as  `k → ∞`.
    Case `β ≥ 1`: the banked monotonicity proof (`LeviSeries.gamma_ratio_tendsto_zero`).
    Case `β ≤ 1`: the log-convexity/Gautschi route (`gamma_ratio_tendsto_zero_lt_one`). -/
theorem gamma_ratio_tendsto_zero_general (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun k : ℕ => Real.Gamma (((k : ℝ) + 1) * β) / Real.Gamma (((k : ℝ) + 2) * β))
      atTop (𝓝 0) := by
  by_cases h1 : 1 ≤ β
  · exact gamma_ratio_tendsto_zero β h1
  · push Not at h1
    exact gamma_ratio_tendsto_zero_lt_one β hβ h1.le

/-! ### 2. The model-coefficient summability at `α > −1`. -/

/-- The successive-coefficient ratio, computed explicitly, now for all `α > −1` (verbatim mirror of
    `LeviSeries.modelCoeff_ratio_eq`, whose proof never needed `α ≥ 0`). -/
theorem modelCoeff_ratio_eq_general (α t : ℝ) (hα : -1 < α) (ht : 0 < t) (k : ℕ) :
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
    (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1)).ne'
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

/-- The successive-coefficient ratio tends to `0`, for all `α > −1` (the generalized Γ-ratio crux
    feeding the ratio test). -/
theorem modelCoeff_ratio_tendsto_zero_general (α t : ℝ) (hα : -1 < α) (ht : 0 < t) :
    Tendsto (fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1)) atTop (𝓝 0) := by
  have hkey : (fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1))
      = fun k : ℕ => (Real.Gamma (α + 1) * t ^ (α + 1))
          * (Real.Gamma (((k : ℝ) + 1) * (α + 1)) / Real.Gamma (((k : ℝ) + 2) * (α + 1))) := by
    funext k; exact modelCoeff_ratio_eq_general α t hα ht k
  rw [hkey]
  have hg := gamma_ratio_tendsto_zero_general (α + 1) (by linarith)
  simpa using hg.const_mul (Real.Gamma (α + 1) * t ^ (α + 1))

/-- **★ The model-coefficient series is summable for ALL `α > −1`** (generalizes
    `LeviSeries.modelCoeff_summable` from `α ≥ 0`; in particular α = −1/2 is now admitted). -/
theorem modelCoeff_summable_general (α t : ℝ) (hα : -1 < α) (ht : 0 < t) :
    Summable (fun k : ℕ => modelCoeff α t (k + 1)) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
  · exact Eventually.of_forall
      (fun k => (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1)).ne')
  · have hnorm : (fun k : ℕ => ‖modelCoeff α t (k + 1 + 1)‖ / ‖modelCoeff α t (k + 1)‖)
        = fun k : ℕ => modelCoeff α t (k + 2) / modelCoeff α t (k + 1) := by
      funext k
      rw [Real.norm_of_nonneg (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1 + 1)).le,
          Real.norm_of_nonneg (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1)).le]
    rw [hnorm]
    exact modelCoeff_ratio_tendsto_zero_general α t hα ht

/-- **The scaled model-coefficient series is summable for ALL `α > −1`** (generalizes
    `LeviSeries.scaledModelCoeff_summable`). -/
theorem scaledModelCoeff_summable_general (α t C : ℝ) (hα : -1 < α) (ht : 0 < t) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff α t (k + 1)) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have hz : (fun k : ℕ => C ^ (k + 1) * modelCoeff α t (k + 1)) = fun _ => (0 : ℝ) := by
      funext k
      rw [← hC0, zero_pow (Nat.succ_ne_zero k), zero_mul]
    rw [hz]; exact summable_zero
  · refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
    · exact Eventually.of_forall (fun k =>
        (mul_pos (pow_pos hCpos (k + 1))
          (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1))).ne')
    · have hCne : C ≠ 0 := hCpos.ne'
      have hratio :
          (fun k : ℕ => ‖C ^ (k + 1 + 1) * modelCoeff α t (k + 1 + 1)‖
              / ‖C ^ (k + 1) * modelCoeff α t (k + 1)‖)
            = fun k : ℕ => C * (modelCoeff α t (k + 2) / modelCoeff α t (k + 1)) := by
        funext k
        have hden1 : (0 : ℝ) ≤ C ^ (k + 1 + 1) * modelCoeff α t (k + 1 + 1) :=
          (mul_pos (pow_pos hCpos _)
            (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1 + 1))).le
        have hden2 : (0 : ℝ) ≤ C ^ (k + 1) * modelCoeff α t (k + 1) :=
          (mul_pos (pow_pos hCpos _)
            (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1))).le
        rw [Real.norm_of_nonneg hden1, Real.norm_of_nonneg hden2, pow_succ]
        have hCk : C ^ (k + 1) ≠ 0 := pow_ne_zero _ hCne
        have hmk : modelCoeff α t (k + 1) ≠ 0 :=
          (modelCoeff_pos α t hα ht (by omega : 1 ≤ k + 1)).ne'
        field_simp
      rw [hratio]
      simpa using (modelCoeff_ratio_tendsto_zero_general α t hα ht).const_mul C

/-- **The scaled width-`κ` iterated-kernel series is summable for ALL `α > −1`** (generalizes
    `HeatResidualBound.scaledIterKernelW_summable`; the width-`κ` factorization `iterKernelW_eq`
    already held at `α > −1`, only the coefficient summability was `α ≥ 0`-locked). -/
theorem scaledIterKernelW_summable_general (κ α t C : ℝ) (hκ : 0 < κ) (hα : -1 < α) (ht : 0 < t)
    (hC : 0 ≤ C) (x y : Point n) :
    Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW κ α (k + 1) t x y) := by
  have heq : (fun k : ℕ => C ^ (k + 1) * iterKernelW κ α (k + 1) t x y)
      = fun k : ℕ => (C ^ (k + 1) * modelCoeff α t (k + 1)) * gaussDdim (κ * t) (x - y) := by
    funext k
    rw [iterKernelW_eq κ α hκ hα t ht x y (by omega : 1 ≤ k + 1)]
    unfold modelCoeff
    ring
  rw [heq]
  exact (scaledModelCoeff_summable_general α t C hα ht hC).mul_right _

/-! ### 3. BLOCKER 2 — the α-parametrized top consumer. -/

/-- **The honest `τ ↦ T` coefficient bound at general `α > −1`.**  For `0 < τ ≤ T`,
        `modelCoeff α τ (k+1) ≤ τ^α · (T^{−α} · modelCoeff α T (k+1))`.
    The exponent splits as `(k+1)(α+1) − 1 = α + k(α+1)` with `k(α+1) ≥ 0`: only the nonnegative
    part is sent `τ ↦ T` (`Real.rpow_le_rpow`); the possibly-NEGATIVE sharp weight `τ^α` stays.
    At `α = 0` this recovers the old `modelCoeff 0 τ ≤ modelCoeff 0 T` (`τ^0 = T^0 = 1`). -/
theorem modelCoeff_le_weight (α τ T : ℝ) (hα : -1 < α) (hτ : 0 < τ) (hτT : τ ≤ T) (k : ℕ) :
    modelCoeff α τ (k + 1) ≤ τ ^ α * (T ^ (-α) * modelCoeff α T (k + 1)) := by
  have hT : 0 < T := lt_of_lt_of_le hτ hτT
  have hβ0 : (0 : ℝ) < α + 1 := by linarith
  have hkc : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hΓnn : (0 : ℝ) ≤ Real.Gamma (α + 1) ^ (k + 1)
      / Real.Gamma (((k + 1 : ℕ) : ℝ) * (α + 1)) :=
    div_nonneg (pow_nonneg (Real.Gamma_pos_of_pos hβ0).le _)
      (Real.Gamma_pos_of_pos (mul_pos hkc hβ0)).le
  have hE : ((k + 1 : ℕ) : ℝ) * (α + 1) - 1 = α + (k : ℝ) * (α + 1) := by push_cast; ring
  have hpow : τ ^ (((k + 1 : ℕ) : ℝ) * (α + 1) - 1)
      ≤ τ ^ α * (T ^ (-α) * T ^ (((k + 1 : ℕ) : ℝ) * (α + 1) - 1)) := by
    rw [hE, Real.rpow_add hτ, Real.rpow_add hT]
    have h1 : τ ^ ((k : ℝ) * (α + 1)) ≤ T ^ ((k : ℝ) * (α + 1)) :=
      Real.rpow_le_rpow hτ.le hτT (mul_nonneg (Nat.cast_nonneg k) hβ0.le)
    have h2 : T ^ (-α) * T ^ α = 1 := by
      rw [← Real.rpow_add hT, neg_add_cancel, Real.rpow_zero]
    calc τ ^ α * τ ^ ((k : ℝ) * (α + 1))
        ≤ τ ^ α * T ^ ((k : ℝ) * (α + 1)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hτ.le α)
      _ = τ ^ α * (T ^ (-α) * (T ^ α * T ^ ((k : ℝ) * (α + 1)))) := by
          rw [show T ^ (-α) * (T ^ α * T ^ ((k : ℝ) * (α + 1)))
              = (T ^ (-α) * T ^ α) * T ^ ((k : ℝ) * (α + 1)) from by ring, h2, one_mul]
  unfold modelCoeff
  calc Real.Gamma (α + 1) ^ (k + 1) / Real.Gamma (((k + 1 : ℕ) : ℝ) * (α + 1))
          * τ ^ (((k + 1 : ℕ) : ℝ) * (α + 1) - 1)
      ≤ Real.Gamma (α + 1) ^ (k + 1) / Real.Gamma (((k + 1 : ℕ) : ℝ) * (α + 1))
          * (τ ^ α * (T ^ (-α) * T ^ (((k + 1 : ℕ) : ℝ) * (α + 1) - 1))) :=
        mul_le_mul_of_nonneg_left hpow hΓnn
    _ = τ ^ α * (T ^ (-α)
          * (Real.Gamma (α + 1) ^ (k + 1) / Real.Gamma (((k + 1 : ℕ) : ℝ) * (α + 1))
              * T ^ (((k + 1 : ℕ) : ℝ) * (α + 1) - 1))) := by ring

/-- **★ BLOCKER 2 DISCHARGED — THE α-PARAMETRIZED LEVI-SERIES DOMINATION (D2 at `α > −1`).**
    For a residual `E` with the `(0,T]`-restricted width-2 order-`α` one-step bound and the carried
    per-step integrability, the SIGNED Levi series is dominated on `(0,T]` with the SAME
    `baseKernelW 2 α` shape as the one-step bound:
        `|leviSeries E τ p q| ≤ C_L · baseKernelW 2 α τ p q`,
        `C_L := T^{−α} · ∑' k, C^{k+1}·modelCoeff α T (k+1)`  (finite by the generalized ratio test).
    ⚠ HONEST WEIGHT: the conclusion's `τ`-weight is `τ^α` (inside `baseKernelW 2 α`) — for `α < 0`
    the series bound BLOWS UP as `τ → 0` exactly like the one-step bound; no clean
    `const·G_{2τ}` bound is (or could be) claimed.  NOT `a₁ = R/6`. -/
theorem leviSeries_dominatedW_le_alpha (E : ℝ → Point n → Point n → ℝ) (α C T : ℝ)
    (hα : -1 < α) (hC : 0 ≤ C) (hT : 0 < T)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW (2 : ℝ) α τ p q)
    (hInt : IterConvIntegrableW E (2 : ℝ) α C) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ τ p q, 0 < τ → τ ≤ T →
      |leviSeries E τ p q| ≤ C_L * baseKernelW (2 : ℝ) α τ p q := by
  classical
  refine ⟨T ^ (-α) * ∑' k : ℕ, C ^ (k + 1) * modelCoeff α T (k + 1), ?_, ?_⟩
  · exact mul_nonneg (Real.rpow_nonneg (lt_of_lt_of_le (by linarith : (0:ℝ) < T) le_rfl).le _)
      (tsum_nonneg (fun k => mul_nonneg (pow_nonneg hC _)
        (modelCoeff_pos α T hα hT (by omega : 1 ≤ k + 1)).le))
  · intro τ p q hτ hτT
    -- termwise iterated-convolution domination and the model summabilities
    have hterm : ∀ k : ℕ, |iterE E (k + 1) τ p q|
        ≤ C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q :=
      fun k => iterConvW_bound_le E 2 α C T hEbound hInt (k + 1) (by omega) τ hτ hτT p q
    have hmodelSum : Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q) :=
      scaledIterKernelW_summable_general 2 α τ C (by norm_num) hα hτ hC p q
    have hAbsSum : Summable (fun k : ℕ => |iterE E (k + 1) τ p q|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm hmodelSum
    have hnormeq : (fun k : ℕ => ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖)
        = fun k : ℕ => |iterE E (k + 1) τ p q| := by
      funext k
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    -- (i) `|leviSeries| ≤ ∑' |iterE|`
    have hstep1 : |leviSeries E τ p q| ≤ ∑' k : ℕ, |iterE E (k + 1) τ p q| := by
      simp only [leviSeries, ← Real.norm_eq_abs]
      calc ‖∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖
          ≤ ∑' k : ℕ, ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖ :=
            norm_tsum_le_tsum_norm (by rw [hnormeq]; exact hAbsSum)
        _ = ∑' k : ℕ, |iterE E (k + 1) τ p q| := by rw [hnormeq]
    -- (ii) `∑' |iterE| ≤ ∑' C^(k+1)·iterKernelW`
    have hstep2 : ∑' k : ℕ, |iterE E (k + 1) τ p q|
        ≤ ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q :=
      hAbsSum.tsum_le_tsum hterm hmodelSum
    -- (iii) factor the model tsum through `iterKernelW_eq` and `tsum_mul_right`
    have hfactor : ∀ k : ℕ, C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q
        = (C ^ (k + 1) * modelCoeff α τ (k + 1)) * gaussDdim (2 * τ) (p - q) := by
      intro k
      rw [iterKernelW_eq 2 α (by norm_num) hα τ hτ p q (by omega : 1 ≤ k + 1)]
      unfold modelCoeff; ring
    have hmodeltsum : ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q
        = (∑' k : ℕ, C ^ (k + 1) * modelCoeff α τ (k + 1)) * gaussDdim (2 * τ) (p - q) := by
      rw [tsum_congr hfactor, tsum_mul_right]
    -- (iv) bound the model-coefficient tsum via the honest `τ^α`-weighted `τ ↦ T` step
    have hcoeffSumτ : Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff α τ (k + 1)) :=
      scaledModelCoeff_summable_general α τ C hα hτ hC
    have hcoeffSumW : Summable
        (fun k : ℕ => C ^ (k + 1) * (τ ^ α * (T ^ (-α) * modelCoeff α T (k + 1)))) := by
      have h0 : Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff α T (k + 1)) :=
        scaledModelCoeff_summable_general α T C hα hT hC
      exact (h0.mul_left (τ ^ α * T ^ (-α))).congr (fun k => by ring)
    have hcoeffbound : ∑' k : ℕ, C ^ (k + 1) * modelCoeff α τ (k + 1)
        ≤ ∑' k : ℕ, C ^ (k + 1) * (τ ^ α * (T ^ (-α) * modelCoeff α T (k + 1))) :=
      hcoeffSumτ.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_left
          (modelCoeff_le_weight α τ T hα hτ hτT k) (pow_nonneg hC _))
        hcoeffSumW
    have hpull : ∑' k : ℕ, C ^ (k + 1) * (τ ^ α * (T ^ (-α) * modelCoeff α T (k + 1)))
        = (τ ^ α * T ^ (-α)) * ∑' k : ℕ, C ^ (k + 1) * modelCoeff α T (k + 1) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun k => by ring)
    calc |leviSeries E τ p q|
        ≤ ∑' k : ℕ, |iterE E (k + 1) τ p q| := hstep1
      _ ≤ ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 α (k + 1) τ p q := hstep2
      _ = (∑' k : ℕ, C ^ (k + 1) * modelCoeff α τ (k + 1)) * gaussDdim (2 * τ) (p - q) :=
          hmodeltsum
      _ ≤ (∑' k : ℕ, C ^ (k + 1) * (τ ^ α * (T ^ (-α) * modelCoeff α T (k + 1))))
            * gaussDdim (2 * τ) (p - q) :=
          mul_le_mul_of_nonneg_right hcoeffbound (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
      _ = ((τ ^ α * T ^ (-α)) * ∑' k : ℕ, C ^ (k + 1) * modelCoeff α T (k + 1))
            * gaussDdim (2 * τ) (p - q) := by rw [hpull]
      _ = (T ^ (-α) * ∑' k : ℕ, C ^ (k + 1) * modelCoeff α T (k + 1))
            * baseKernelW (2 : ℝ) α τ p q := by
          simp only [baseKernelW]; ring

/-! ### 4. The α = −1/2 instantiation (the J4-610 frozen-defect shape). -/

/-- **The width-2 base kernel at `α = −1/2` IS the frozen-defect shape**:
    `baseKernelW 2 (−1/2) τ p q = G_{2τ}(p−q)/√τ`  (for `τ > 0`) — exactly the RHS shape of
    `FrozenGauss.FrozenDefectBound` (`C/√τ · gaussDdim (2τ)`). -/
theorem baseKernelW_negHalf_apply (τ : ℝ) (hτ : 0 < τ) (p q : Point n) :
    baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q = gaussDdim (2 * τ) (p - q) / Real.sqrt τ := by
  simp only [baseKernelW]
  rw [Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow, inv_mul_eq_div]

/-- **★ THE α = −1/2 LEVI-SERIES DOMINATION — the D2 engine opened to the J4-610 frozen defect.**
    Stated in the J4-610 shape on BOTH sides: from the one-step bound
        `|E τ p q| ≤ (C/√τ)·G_{2τ}(p−q)`   (`0 < τ ≤ T`)
    (the `FrozenDefectBound` shape, = `C·baseKernelW 2 (−1/2)`) and the carried α = −1/2 per-step
    integrability, the Levi series obeys
        `|leviSeries E τ p q| ≤ (C_L/√τ)·G_{2τ}(p−q)`   on `(0,T]`.
    ⚠ HONEST WEIGHT: the series bound INHERITS the `τ^{−1/2}` weight (the `k = 1` term dominates at
    small `τ`); it is NOT `≤ const·G_{2τ}` as `τ → 0` (see `negHalf_weight_unbounded`).  Which
    downstream consumer can ingest a `τ^{−1/2}`-weighted series bound is the NEXT brick's scope. -/
theorem leviSeries_dominatedW_le_negHalf (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T →
      |E τ p q| ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ τ p q, 0 < τ → τ ≤ T →
      |leviSeries E τ p q| ≤ C_L / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := by
  obtain ⟨C_L, hC_L0, hbound⟩ := leviSeries_dominatedW_le_alpha E (-(1 / 2)) C T
    (by norm_num) hC hT
    (fun τ p q hτ hτT => by
      rw [baseKernelW_negHalf_apply τ hτ]
      calc |E τ p q| ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := hEbound τ p q hτ hτT
        _ = C * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := by ring)
    hInt
  refine ⟨C_L, hC_L0, fun τ p q hτ hτT => ?_⟩
  have h := hbound τ p q hτ hτT
  rw [baseKernelW_negHalf_apply τ hτ] at h
  calc |leviSeries E τ p q|
      ≤ C_L * (gaussDdim (2 * τ) (p - q) / Real.sqrt τ) := h
    _ = C_L / Real.sqrt τ * gaussDdim (2 * τ) (p - q) := by ring

/-! ### 5. Non-vacuity / honesty gates. -/

/-- **NON-VACUITY (blocker 1): the α = −1/2 model series is a genuinely positive summable
    series** — the generalized ratio test sums strictly positive terms; nothing degenerates. -/
theorem negHalf_model_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℕ => modelCoeff (-(1 / 2) : ℝ) t (k + 1)) :=
  modelCoeff_summable_general (-(1 / 2)) t (by norm_num) ht

/-- The α = −1/2 model sum is strictly positive (`tsum_pos` at the first term). -/
theorem negHalf_model_sum_pos (t : ℝ) (ht : 0 < t) :
    0 < ∑' k : ℕ, modelCoeff (-(1 / 2) : ℝ) t (k + 1) :=
  (negHalf_model_summable t ht).tsum_pos
    (fun k => (modelCoeff_pos _ t (by norm_num) ht (by omega : 1 ≤ k + 1)).le) 0
    (modelCoeff_pos _ t (by norm_num) ht (by omega : 1 ≤ 0 + 1))

/-- The `k`-fold iterated convolution of the ZERO residual vanishes (each step's integrand carries
    a literal `0` left factor). -/
theorem iterE_zero_eq_zero (k : ℕ) (t : ℝ) (x y : Point n) :
    iterE (fun _ _ _ => (0 : ℝ)) k t x y = 0 := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | (m + 2) =>
    show heatConvK (fun _ _ _ => (0 : ℝ)) (iterE (fun _ _ _ => (0 : ℝ)) (m + 1)) t x y = 0
    simp [heatConvK_apply, heatConv]

/-- The zero residual carries the α = −1/2 per-step integrability family at `C = 0` (every
    conjunct is the integrability of the zero function). -/
theorem iterConvIntegrableW_zero (α : ℝ) :
    IterConvIntegrableW (n := n) (fun _ _ _ => (0 : ℝ)) 2 α 0 := by
  intro k hk t ht x y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : (fun s => ‖∫ z : Point n,
        (0 : ℝ) * iterE (fun _ _ _ => (0 : ℝ)) k s z y‖) = fun _ => (0 : ℝ) := by
      funext s; simp
    rw [h]; exact intervalIntegrable_const
  · have h : (fun s => ∫ z : Point n,
        |(0 : ℝ)| * |iterE (fun _ _ _ => (0 : ℝ)) k s z y|) = fun _ => (0 : ℝ) := by
      funext s; simp
    rw [h]; exact intervalIntegrable_const
  · intro s
    have h : (fun z : Point n =>
        |(0 : ℝ)| * |iterE (fun _ _ _ => (0 : ℝ)) k s z y|) = fun _ => (0 : ℝ) := by
      funext z; simp
    rw [h]; exact integrable_zero _ _ _
  · intro s
    have h : (fun z : Point n => (0 : ℝ) * baseKernelW 2 α (t - s) x z
        * ((0 : ℝ) ^ k * iterKernelW 2 α k s z y)) = fun _ => (0 : ℝ) := by
      funext z; simp
    rw [h]; exact integrable_zero _ _ _
  · have h : (fun s => ∫ z : Point n, (0 : ℝ) * baseKernelW 2 α (t - s) x z
        * ((0 : ℝ) ^ k * iterKernelW 2 α k s z y)) = fun _ => (0 : ℝ) := by
      funext s; simp
    rw [h]; exact intervalIntegrable_const

/-- **NON-VACUITY (blocker 2, antecedent satisfiability — the axiom-budget-blind-spot check):**
    the antecedent bundle of `leviSeries_dominatedW_le_negHalf` is jointly INHABITED (witness
    `E = 0, C = 0`).  ⚠ HONEST: this certifies mere satisfiability of the hypothesis bundle
    (the theorem is not vacuously conditioned); the GENUINELY NONZERO consumer is the J4-610
    frozen defect `E`, whose `IterConvIntegrableW` family is a carried pile for a later brick. -/
theorem negHalf_consumer_antecedent_satisfiable (T : ℝ) :
    ∃ (E : ℝ → Point n → Point n → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ τ p q, 0 < τ → τ ≤ T →
        |E τ p q| ≤ C / Real.sqrt τ * gaussDdim (2 * τ) (p - q)) ∧
      IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C :=
  ⟨fun _ _ _ => 0, 0, le_rfl, fun τ p q _ _ => by simp, iterConvIntegrableW_zero _⟩

/-- **NO-FALSE-BOUND honesty certificate 1**: the α = −1/2 weight strictly exceeds the α = 0
    (constant) weight on `0 < τ < 1` — the series bound is genuinely WEAKER than a clean
    `const·G_{2τ}` bound. -/
theorem negHalf_weight_exceeds_one (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (1 : ℝ) < τ ^ (-(1 / 2) : ℝ) :=
  (Real.one_lt_rpow_iff_of_pos hτ0).mpr (Or.inr ⟨hτ1, by norm_num⟩)

/-- **NO-FALSE-BOUND honesty certificate 2**: the α = −1/2 weight is UNBOUNDED as `τ → 0` along
    `τ = 1/(m+1)` — no `τ`-uniform constant can dominate `τ^{−1/2}`; the τ-weight in
    `leviSeries_dominatedW_le_negHalf` is irreducible. -/
theorem negHalf_weight_unbounded :
    Tendsto (fun m : ℕ => ((((m : ℝ) + 1))⁻¹) ^ (-(1 / 2) : ℝ)) atTop atTop := by
  have heq : (fun m : ℕ => ((((m : ℝ) + 1))⁻¹) ^ (-(1 / 2) : ℝ))
      = fun m : ℕ => ((m : ℝ) + 1) ^ ((1 / 2) : ℝ) := by
    funext m
    have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    rw [Real.inv_rpow hm, Real.rpow_neg hm, inv_inv]
  rw [heq]
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1

end QIQTH.AlphaLevi
