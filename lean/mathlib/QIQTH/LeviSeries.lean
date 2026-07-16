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
import QIQTH.HeatDuhamel

open Real MeasureTheory Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TimeSimplexBeta QIQTH.HeatDuhamel
open scoped Interval

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

/-! ### C5b — domination lemmas for the space-time Duhamel convolution `heatConv`.

    These bridge the MODEL bound (C3/C5a above) to the ACTUAL residual: they are the clean integral
    inequalities on `heatConv` that let `|E^{*k}| ≤ C^k · iterKernel` be proved (C5c) from a one-step
    bound on `E`.  Three lemmas:

    * `heatConv_abs_le` (#1) — the integral **triangle inequality**
        `|heatConv A B| ≤ heatConv |A| |B|`
      (interval triangle `intervalIntegral.norm_integral_le_integral_norm`, needs only `0 ≤ t`, then
      the inner Lebesgue triangle `norm_integral_le_integral_norm`, then `‖a·b‖ = |a|·|b|`);
    * `heatConv_mono` (#2) — **monotonicity** under pointwise domination of nonnegative kernels
      (`mul_le_mul` pointwise, then `MeasureTheory.integral_mono` on `∫z`, then
      `intervalIntegral.integral_mono_on` on `∫s`);
    * `heatConv_le_of_abs_le` (#3) — the C5c-facing combination
        `|heatConv A B| ≤ heatConv A' B'`  from  `|A| ≤ A'`, `|B| ≤ B'`.

    All integrability / nonnegativity hypotheses are carried EXACTLY as the underlying Mathlib
    triangle / monotonicity lemmas demand — genuine (each fails without them), none vacuous, none the
    conclusion.  This is phase C5b (domination); NOT the true kernel / `a₁ = R/6`. -/

/-- **#1 — the integral triangle inequality for `heatConv`.**  For `0 ≤ t` and the two genuine
    interval-integrabilities the triangle steps need,
        `|heatConv A B t x y| ≤ heatConv |A| |B| t x y`.
    Route: `|∫s ∫z A·B| = ‖∫s ∫z A·B‖ ≤ ∫s ‖∫z A·B‖`
    (`intervalIntegral.norm_integral_le_integral_norm`, needs `0 ≤ t`),
    then pointwise in `s`, `‖∫z A·B‖ ≤ ∫z ‖A·B‖ = ∫z |A|·|B|`
    (`norm_integral_le_integral_norm` + `Real.norm_eq_abs`/`abs_mul`),
    lifted through `intervalIntegral.integral_mono_on` (whence `hI1`/`hI2`). -/
theorem heatConv_abs_le (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (ht : 0 ≤ t)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t) :
    |heatConv A B t x y|
      ≤ heatConv (fun τ p q => |A τ p q|) (fun τ p q => |B τ p q|) t x y := by
  simp only [heatConv]
  conv_lhs => rw [← Real.norm_eq_abs]
  calc ‖∫ s in (0)..t, ∫ z, A (t - s) x z * B s z y‖
      ≤ ∫ s in (0)..t, ‖∫ z, A (t - s) x z * B s z y‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ s in (0)..t, ∫ z, |A (t - s) x z| * |B s z y| := by
        refine intervalIntegral.integral_mono_on ht hI1 hI2 (fun s _ => ?_)
        calc ‖∫ z, A (t - s) x z * B s z y‖
            ≤ ∫ z, ‖A (t - s) x z * B s z y‖ := norm_integral_le_integral_norm _
          _ = ∫ z, |A (t - s) x z| * |B s z y| := by
                refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
                simp only [Real.norm_eq_abs, abs_mul]

/-- **#2 — monotonicity of `heatConv` under pointwise domination.**  For `0 ≤ t`, nonnegative
    kernels dominated pointwise (`A ≤ A'`, `B ≤ B'`), and the four genuine integrabilities the
    monotonicity steps need,
        `heatConv A B t x y ≤ heatConv A' B' t x y`.
    Route: pointwise `A·B ≤ A'·B'` (`mul_le_mul` with `0 ≤ B`, `0 ≤ A'`), then
    `MeasureTheory.integral_mono` on the `∫z`, then `intervalIntegral.integral_mono_on` on the `∫s`. -/
theorem heatConv_mono (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (ht : 0 ≤ t)
    (hA0 : ∀ s z, 0 ≤ A (t - s) x z) (hB0 : ∀ s z, 0 ≤ B s z y)
    (hAle : ∀ s z, A (t - s) x z ≤ A' (t - s) x z)
    (hBle : ∀ s z, B s z y ≤ B' s z y)
    (hIf : ∀ s, Integrable (fun z => A (t - s) x z * B s z y))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsf : IntervalIntegrable (fun s => ∫ z, A (t - s) x z * B s z y) volume 0 t)
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    heatConv A B t x y ≤ heatConv A' B' t x y := by
  simp only [heatConv]
  refine intervalIntegral.integral_mono_on ht hIsf hIsg (fun s _ => ?_)
  refine integral_mono (hIf s) (hIg s) ?_
  intro z
  exact mul_le_mul (hAle s z) (hBle s z) (hB0 s z) (le_trans (hA0 s z) (hAle s z))

/-- **#3 — the C5c-facing combination.**  If `|A| ≤ A'` and `|B| ≤ B'` pointwise (so `A', B' ≥ 0`
    are FORCED, `0 ≤ |·| ≤ ·`), `0 ≤ t`, and the genuine integrabilities hold, then
        `|heatConv A B t x y| ≤ heatConv A' B' t x y`.
    Proof: `heatConv_abs_le` (`|heatConv A B| ≤ heatConv |A| |B|`) then `heatConv_mono`
    (`0 ≤ |A|,|B|`, `|A| ≤ A'`, `|B| ≤ B'`). -/
theorem heatConv_le_of_abs_le (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (ht : 0 ≤ t)
    (hA : ∀ τ p q, |A τ p q| ≤ A' τ p q) (hB : ∀ τ p q, |B τ p q| ≤ B' τ p q)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t)
    (hIf : ∀ s, Integrable (fun z => |A (t - s) x z| * |B s z y|))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    |heatConv A B t x y| ≤ heatConv A' B' t x y := by
  refine le_trans (heatConv_abs_le A B t x y ht hI1 hI2) ?_
  refine heatConv_mono (fun τ p q => |A τ p q|) (fun τ p q => |B τ p q|) A' B' t x y ht
    (fun s z => abs_nonneg _) (fun s z => abs_nonneg _)
    (fun s z => hA (t - s) x z) (fun s z => hB s z y)
    hIf hIg hI2 hIsg

/-! ### C5c — iterated bound + Neumann convergence.

    This ties C5b (domination) + C3 (`iterKernel`) + C5a (model summable) together for the ACTUAL
    residual `E`.  We bound the iterated residual convolutions `E^{*k}` (`iterE`) by the model
    `C^k · iterKernel`, then conclude the Levi/Duhamel Neumann series for `E` CONVERGES.

    * `iterE E k` — the `k`-fold iterated convolution of the residual `E` (mirrors `iterKernel`).
    * `heatConv_le_of_abs_le_pos` — the positive-time domination step: it needs the one-step bounds
      only for POSITIVE times (`0 < τ`), because `heatConv` integrates over `s ∈ (0,t)` where both
      inner times `t−s` and `s` are positive.  This is what lets the one-step residual bound
      (`hEbound`, stated for `0 < τ`) and the inductive hypothesis (positive-time bound on
      `iterE E k`) actually feed the induction — `intervalIntegral.integral_mono_on_of_le_Ioo`
      only needs the pointwise inequality on the OPEN interval.
    * `iterConv_bound` — THE deliverable: `|iterE E k t x y| ≤ C^k · iterKernel α k t x y`, by
      `Nat.le_induction` on `k` (base `k=1` = `hEbound`; step = `heatConv_le_of_abs_le_pos` +
      scalar pull-out + `iterKernel_succ`).  The per-step integrability is CARRIED honestly as an
      explicit indexed family `IterConvIntegrable` (genuine integral facts, never the conclusion).
    * `leviSeries_summable` — the convergence conclusion: `Summable (fun k => iterE E (k+1) t x y)`,
      by comparison (`Summable.of_norm_bounded`) with the dominating model series
      `C^(k+1) · iterKernel α (k+1) t x y`, whose summability (`scaledIterKernel_summable`) follows
      from the C5a ratio test — the `Γ` (factorial) decay beats any geometric `C^k`.

    ⚠ HONEST SCOPE.  The one-step residual bound `hEbound` is CARRIED here (C4 discharges it, and C4
    reduces to the off-diagonal parametrix — a separate wall).  This is C5c (actual-residual bound +
    convergence), NOT the true curved kernel / `a₁ = R/6` (C6).  No axioms beyond the standard three,
    no `sorry`. -/

/-- **Positivity of the `d`-dim Gaussian** for `t > 0`: a product of strictly positive 1-D kernels. -/
theorem gaussDdim_pos (t : ℝ) (ht : 0 < t) (x : Point n) : 0 < gaussDdim t x := by
  unfold gaussDdim
  exact Finset.prod_pos (fun k _ => QIQTH.GaussianConvolution.heatKernel1D_pos t (x k) ht)

/-- **Nonnegativity of the model iterated kernel** for `α > −1`, `t > 0`, `k ≥ 1`: it equals
    `modelCoeff α t k · gaussDdim t (x−y)`, a product of a positive coefficient and a positive
    Gaussian (`iterKernel_eq`). -/
theorem iterKernel_nonneg (α t : ℝ) (hα : -1 < α) (ht : 0 < t) (x y : Point n) {k : ℕ}
    (hk : 1 ≤ k) : 0 ≤ iterKernel α k t x y := by
  have hfac : iterKernel α k t x y = modelCoeff α t k * gaussDdim t (x - y) := by
    rw [iterKernel_eq α hα t ht x y hk]; unfold modelCoeff; ring
  rw [hfac]
  exact mul_nonneg (modelCoeff_pos α t hα ht hk).le (gaussDdim_pos t ht (x - y)).le

/-! #### The iterated residual convolution `iterE`. -/

/-- **The `k`-fold iterated convolution of the residual kernel `E`** (the actual Levi/Duhamel
    Neumann term).  Mirrors `TimeSimplexBeta.iterKernel`: `iterE E 1 = E`, and each step
    left-convolves once more by `E`, `iterE E (k+1) = heatConvK E (iterE E k)` for `k ≥ 1`. -/
noncomputable def iterE (E : ℝ → Point n → Point n → ℝ) : ℕ → (ℝ → Point n → Point n → ℝ)
  | 0 => E
  | 1 => E
  | (k + 2) => heatConvK E (iterE E (k + 1))

/-- One residual factor: `iterE E 1 = E`. -/
theorem iterE_one (E : ℝ → Point n → Point n → ℝ) :
    (iterE E 1 : ℝ → Point n → Point n → ℝ) = E := rfl

/-- The recursion step (for `k ≥ 1`): `iterE E (k+1) = heatConvK E (iterE E k)`. -/
theorem iterE_succ (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (iterE E (k + 1) : ℝ → Point n → Point n → ℝ) = heatConvK E (iterE E k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rfl

/-! #### The positive-time domination step. -/

/-- **The positive-time `heatConv` domination step.**  If `|A| ≤ A'` and `|B| ≤ B'` hold for all
    POSITIVE times (`0 < τ`), `0 < t`, and the genuine integrabilities hold, then
        `|heatConv A B t x y| ≤ heatConv A' B' t x y`.
    Unlike `heatConv_le_of_abs_le` (which needs the bounds at ALL times), this only needs them for
    `0 < τ`: `heatConv` integrates over `s ∈ (0,t)`, where the inner times `t−s` and `s` are both
    positive, and `intervalIntegral.integral_mono_on_of_le_Ioo` only demands the pointwise
    inequality on the OPEN interval `Ioo 0 t`.  This is exactly what lets the residual's one-step
    bound (valid for `0 < τ`) and the positive-time inductive hypothesis feed the C5c induction.

    Route: `heatConv_abs_le` (`|heatConv A B| ≤ heatConv |A| |B|`, all times), then
    `integral_mono_on_of_le_Ioo` on the `∫s` (bounds only on `Ioo 0 t`) with `integral_mono` on the
    inner `∫z` (`mul_le_mul` from `|A| ≤ A'`, `|B| ≤ B'`, both at positive inner times). -/
theorem heatConv_le_of_abs_le_pos (A B A' B' : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (ht : 0 < t)
    (hA : ∀ τ p q, 0 < τ → |A τ p q| ≤ A' τ p q)
    (hB : ∀ τ p q, 0 < τ → |B τ p q| ≤ B' τ p q)
    (hI1 : IntervalIntegrable (fun s => ‖∫ z, A (t - s) x z * B s z y‖) volume 0 t)
    (hI2 : IntervalIntegrable (fun s => ∫ z, |A (t - s) x z| * |B s z y|) volume 0 t)
    (hIf : ∀ s, Integrable (fun z => |A (t - s) x z| * |B s z y|))
    (hIg : ∀ s, Integrable (fun z => A' (t - s) x z * B' s z y))
    (hIsg : IntervalIntegrable (fun s => ∫ z, A' (t - s) x z * B' s z y) volume 0 t) :
    |heatConv A B t x y| ≤ heatConv A' B' t x y := by
  refine le_trans (heatConv_abs_le A B t x y ht.le hI1 hI2) ?_
  simp only [heatConv]
  refine intervalIntegral.integral_mono_on_of_le_Ioo ht.le hI2 hIsg (fun s hs => ?_)
  obtain ⟨hs0, hst⟩ := hs
  have hts : 0 < t - s := by linarith
  refine integral_mono (hIf s) (hIg s) (fun z => ?_)
  have hAz := hA (t - s) x z hts
  have hBz := hB s z y hs0
  exact mul_le_mul hAz hBz (abs_nonneg _) (le_trans (abs_nonneg _) hAz)

/-! #### The iterated residual bound (THE deliverable) and Neumann convergence. -/

/-- **The carried per-step integrability family** for `iterConv_bound`.  For every `k ≥ 1`, positive
    time `t`, and points `x y`, this bundles the five genuine integral facts that
    `heatConv_le_of_abs_le_pos` demands with `A = E`, `B = iterE E k`, `A' = C · baseKernel α`,
    `B' = C^k · iterKernel α k`.  These are honest analytic hypotheses on the ACTUAL residual and its
    model dominators — orthogonal to (never a restatement of) the conclusion `|iterE| ≤ …`. -/
def IterConvIntegrable (E : ℝ → Point n → Point n → ℝ) (α C : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
    IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
    IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
    (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
    (∀ s, Integrable (fun z => C * baseKernel α (t - s) x z * (C ^ k * iterKernel α k s z y))) ∧
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernel α (t - s) x z * (C ^ k * iterKernel α k s z y)) volume 0 t

/-- **★ THE C5c DELIVERABLE — the iterated residual bound.**  For `α ≥ 0`, `C ≥ 0`, the one-step
    residual bound `hEbound : |E τ p q| ≤ C · baseKernel α τ p q` (all positive times), and the
    carried per-step integrability family, the actual `k`-fold iterated residual convolution is
    dominated by the model:
        `|iterE E k t x y| ≤ C^k · iterKernel α k t x y`   (for `k ≥ 1`, `t > 0`).
    Proof: `Nat.le_induction` on `k` from `1`.  Base `k = 1`: `iterE E 1 = E`, `iterKernel α 1 =
    baseKernel α`, so the goal IS `hEbound`.  Step: `iterE E (k+1) = heatConv E (iterE E k)`
    (`iterE_succ`); apply `heatConv_le_of_abs_le_pos` with `A' = C·base`, `B' = C^k·iterKernel α k`
    (`hA` from `hEbound`, `hB` from the IH, both at positive inner times), then pull the scalars `C`,
    `C^k` out (`heatConv_smul_left`/`_right`) and fold with `iterKernel_succ` and `pow_succ`. -/
theorem iterConv_bound (E : ℝ → Point n → Point n → ℝ) (α C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernel α τ p q)
    (hInt : IterConvIntegrable E α C) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      |iterE E k t x y| ≤ C ^ k * iterKernel α k t x y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht x y
      rw [iterE_one, pow_one, iterKernel_one]
      exact hEbound t x y ht
  | succ m hm ih =>
      intro t ht x y
      obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := hInt m hm t ht x y
      rw [iterE_succ E hm, iterKernel_succ α hm]
      simp only [heatConvK_apply]
      have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
        (fun τ p q => C * baseKernel α τ p q) (fun τ p q => C ^ m * iterKernel α m τ p q)
        t x y ht
        (fun τ p q hτ => hEbound τ p q hτ)
        (fun τ p q hτ => ih τ hτ p q)
        hI1 hI2 hIf hIg hIsg
      calc |heatConv E (iterE E m) t x y|
          ≤ heatConv (fun τ p q => C * baseKernel α τ p q)
              (fun τ p q => C ^ m * iterKernel α m τ p q) t x y := hbound
        _ = C ^ (m + 1) * heatConv (baseKernel α) (iterKernel α m) t x y := by
              rw [heatConv_smul_left C (baseKernel α)
                    (fun τ p q => C ^ m * iterKernel α m τ p q),
                  heatConv_smul_right (C ^ m) (baseKernel α) (iterKernel α m), pow_succ]
              ring

/-- **The scaled model coefficient series is summable.**  For `α ≥ 0`, `t > 0`, `C ≥ 0`,
        `Summable (fun k => C^(k+1) · modelCoeff α t (k+1))`.
    The extra geometric factor `C^(k+1)` does not spoil summability: the successive-term ratio picks
    up an extra `C` but still `→ C · 0 = 0 < 1` (the `Γ` decay dominates), so the C5a ratio test
    (`summable_of_ratio_test_tendsto_lt_one`) closes.  (`C = 0` handled separately: all terms `0`.) -/
theorem scaledModelCoeff_summable (α t C : ℝ) (hα : 0 ≤ α) (ht : 0 < t) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff α t (k + 1)) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- C = 0: every term is 0.
    have hz : (fun k : ℕ => C ^ (k + 1) * modelCoeff α t (k + 1)) = fun _ => (0 : ℝ) := by
      funext k
      rw [← hC0, zero_pow (Nat.succ_ne_zero k), zero_mul]
    rw [hz]; exact summable_zero
  · -- 0 < C: ratio test.
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
    · exact Eventually.of_forall (fun k =>
        (mul_pos (pow_pos hCpos (k + 1))
          (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1))).ne')
    · have hCne : C ≠ 0 := hCpos.ne'
      have hratio :
          (fun k : ℕ => ‖C ^ (k + 1 + 1) * modelCoeff α t (k + 1 + 1)‖
              / ‖C ^ (k + 1) * modelCoeff α t (k + 1)‖)
            = fun k : ℕ => C * (modelCoeff α t (k + 2) / modelCoeff α t (k + 1)) := by
        funext k
        have hden1 : (0 : ℝ) ≤ C ^ (k + 1 + 1) * modelCoeff α t (k + 1 + 1) :=
          (mul_pos (pow_pos hCpos _)
            (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1 + 1))).le
        have hden2 : (0 : ℝ) ≤ C ^ (k + 1) * modelCoeff α t (k + 1) :=
          (mul_pos (pow_pos hCpos _)
            (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1))).le
        rw [Real.norm_of_nonneg hden1, Real.norm_of_nonneg hden2, pow_succ]
        have hCk : C ^ (k + 1) ≠ 0 := pow_ne_zero _ hCne
        have hmk : modelCoeff α t (k + 1) ≠ 0 :=
          (modelCoeff_pos α t (by linarith) ht (by omega : 1 ≤ k + 1)).ne'
        field_simp
      rw [hratio]
      simpa using (modelCoeff_ratio_tendsto_zero α t hα ht).const_mul C

/-- **The scaled model iterated-kernel series is summable.**  For `α ≥ 0`, `t > 0`, `C ≥ 0`, and
    `x y`, `Summable (fun k => C^(k+1) · iterKernel α (k+1) t x y)`: each term factors as
    `(C^(k+1) · modelCoeff α t (k+1)) · gaussDdim t (x−y)` (`iterKernel_eq`), a `k`-constant Gaussian
    times the summable scaled coefficient. -/
theorem scaledIterKernel_summable (α t C : ℝ) (hα : 0 ≤ α) (ht : 0 < t) (hC : 0 ≤ C)
    (x y : Point n) :
    Summable (fun k : ℕ => C ^ (k + 1) * iterKernel α (k + 1) t x y) := by
  have heq : (fun k : ℕ => C ^ (k + 1) * iterKernel α (k + 1) t x y)
      = fun k : ℕ => (C ^ (k + 1) * modelCoeff α t (k + 1)) * gaussDdim t (x - y) := by
    funext k
    rw [iterKernel_eq α (by linarith) t ht x y (by omega : 1 ≤ k + 1)]
    unfold modelCoeff
    ring
  rw [heq]
  exact (scaledModelCoeff_summable α t C hα ht hC).mul_right _

/-- **★ THE C5c CONVERGENCE CONCLUSION — the Levi/Duhamel Neumann series for the residual `E`
    converges.**  For `α ≥ 0`, `C ≥ 0`, the one-step residual bound `hEbound`, and the carried
    per-step integrability, at every `t > 0` and `x y`,
        `Summable (fun k => iterE E (k+1) t x y)`.
    Route: each term is dominated in norm by `C^(k+1) · iterKernel α (k+1) t x y` (`iterConv_bound`),
    and that model series is summable (`scaledIterKernel_summable` — the `Γ` decay beats the geometric
    `C^k`), so the comparison test `Summable.of_norm_bounded` concludes. -/
theorem leviSeries_summable (E : ℝ → Point n → Point n → ℝ) (α C : ℝ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernel α τ p q)
    (hInt : IterConvIntegrable E α C) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  refine Summable.of_norm_bounded (scaledIterKernel_summable α t C hα ht hC x y) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact iterConv_bound E α C hEbound hInt (k + 1) (by omega) t ht x y

end QIQTH.LeviSeries
