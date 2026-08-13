/-
  Width1QuadCutoff — J4-677 (file 1 of 2): the WIDTH-1 QUADRATIC CUTOFF `N = 1` RESIDUAL CHAIN —
  the in-chart side of the gluing brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE IS (the missing in-chart supply for the on-gate width-4/3 quadratic `hgate`).

  The banked chain ends at (J4-676) `uniformResidual_quadPoly_bound_tau_width1` — the width-1 in-chart
  QUADRATIC bound for the `N = 0` UNCUT parametrix residual.  But the concrete witness the `hgate`
  consumers name is the `N = 1` CUTOFF parametrix (`globalCutoffParametrixWitnessN 1 …` inside
  `vanVleckGatedWitness`), whose in-chart transport-identity value is the CUTOFF `N = 1` residual
      `χ_{a,b}·∂_τ P₁ − Δ_{g̃_q}(χ_{a,b}·P₁)`.
  The banked producer for THAT object (`CoeffU1Fix.cutoffResidualN1_uniformFlow_narrow_mixed_below_lin`)
  collapses everything to the width-3/2 PURE Gaussian — too wide for the width-4/3-quadratic route (β).
  This file re-runs the SAME assembly keeping the WIDTH-1 QUADRATIC envelope
      `E_τ(v) := ((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v`
  explicit, with the honest AFFINE `(B₀ + B₁·τ)` outer factor (Sol #15: the `τ·R₀[u′]` branch of the
  `N = 1` split genuinely grows linearly in `τ`).

  ## THE FIVE BRICKS.
    • (W0)  `gaussDdim_le_quadEnv` / `sqrt_le_one_add_w1` — envelope trivia (`G ≤ E`, `√x ≤ 1+x`).
    • (W1L) `uniformResidualLinear_quadPoly_bound_tau_width1` — the width-1 analogue of
            `CoeffU1Fix.uniformResidualLinear_gaussian_bound_tau_narrow`: `N = 0` residual with the
            `O(r)` coefficient (the shifted van-Vleck profile), bound `(C₀ + C₁·(√τ/τ))·E_τ`; the
            `T1` odd power rides `√X ≤ 1 + X ≤ X² + X + 1` instead of a width absorption.
    • (W1N) `uniformResidualN1_quadPoly_width1_affine` — the width-1 QUADRATIC AFFINE `N = 1`
            near-packet bound, via the J4-103 split `R₁ = R₀[u] + H₀[u′] + τ·R₀[u′]`: `R₀[u]` from the
            banked J4-676 star, `H₀[u′] = G·w₁ ≤ W₁·E`, `τ·R₀[u′]` from (W1L) + `√τ ≤ 1+τ`.
    • (ENG) `cutoffResidual_envelope_engine` — the M2 cutoff glue engine with the dominating Gaussian
            replaced by an ABSTRACT nonneg envelope `E` (the banked engine's proof only ever used
            nonnegativity of the width-3/2 Gaussian; this exposes that).
    • (ANN) `parametrixCofactor_deriv_annulus_quadEnv_tauUniform` — the annulus `∂ⱼ(G·cof)` bound at
            the width-1 quadratic envelope: the `(1/τ)·G` factor deposits into the POLYNOMIAL
            (`1/τ ≤ X/a²` on the annulus) instead of into a wider Gaussian.
    • (CUT) `cutoffResidualN1_uniformFlow_width1_quad_affine` — ★★ the capstone: the CUTOFF `N = 1`
            residual at the width-1 QUADRATIC envelope, affine in `τ`, uniform over `q ∈ K`, ∀ v —
            the EXACT in-chart input of the J4-677 chart-transfer glue (file 2).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  width-1 quadratic re-grading of the banked cutoff `N = 1` residual chain — pure width bookkeeping over
  the SAME load-bearing suppliers (`hCoeffU0`/`hCoeffLin1` remain the genuine firewalled coefficient
  inputs, identical to the banked producers').  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthOneQuadResidual
import QIQTH.CoeffU1Fix

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (W0) — envelope trivia. -/

/-- `√x ≤ 1 + x` for `x ≥ 0` (local copy; keeps the import closure light).  NOT `a₁ = R/6`. -/
theorem sqrt_le_one_add_w1 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1x : (0 : ℝ) ≤ 1 + x := by linarith
  have h : Real.sqrt x ≤ Real.sqrt ((1 + x) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hx])
  rwa [Real.sqrt_sq h1x] at h

/-- **(W0) — `gaussDdim_le_quadEnv`.**  The pure Gaussian is dominated by the width-1 QUADRATIC
    envelope (`1 ≤ X² + X + 1` for `X = r²/τ ≥ 0`).  NOT `a₁ = R/6`. -/
theorem gaussDdim_le_quadEnv {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim τ v
      ≤ ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v := by
  have hX0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hG0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  nlinarith [mul_nonneg (mul_nonneg hX0 hX0) hG0, mul_nonneg hX0 hG0]

/-! ### (W1L) — the `O(r)`-coefficient width-1 quadratic `N = 0` residual. -/

/-- **★ (W1L) — `uniformResidualLinear_quadPoly_bound_tau_width1`.**  The width-1 QUADRATIC analogue of
    `CoeffU1Fix.uniformResidualLinear_gaussian_bound_tau_narrow`: the `N = 0` parametrix residual with an
    `O(r)` (LINEAR) coefficient input `hCoeffLin` (the shifted van-Vleck profile's honest bound) obeys
        `|parametrixResidualN 0 g̃_q g̃⁻¹_q Θ u τ v| ≤ (C₀ + C₁·(√τ/τ))·(((r²_v/τ)² + r²_v/τ + 1)·G_τ(v))`
    for all `τ > 0`, `q ∈ K`, `‖v‖ < ρ_u`.  `T1 = (1/τ)·G·coeff`: `|coeff| ≤ C_c·r` and
    `r/τ = √X·(√τ/τ)` (`X = r²/τ`), then `√X ≤ 1 + X ≤ X² + X + 1` — the odd power rides the POLYNOMIAL,
    no width absorption.  `T2` via `residualQuadratic_pointwise_width1` (J4-676), `T3` via the uniform
    Laplacian supplier.  `C₀ = n²MW/4 + L`, `C₁ = C_c`.  NOT `a₁ = R/6`. -/
theorem uniformResidualLinear_quadPoly_bound_tau_width1 (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hCoeffLin : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadial v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (C₀ + C₁ * (Real.sqrt τ / τ))
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
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
  refine ⟨ρ_u, hρ_u0, (n : ℝ) ^ 2 * M * W / 4 + L, C_c, by positivity, hC_c0, ?_⟩
  intro τ hτ q hq v hv
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set X : ℝ := rncRadialSq v / τ with hXdef
  have hX0 : 0 ≤ X := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hP0 : 0 ≤ X ^ 2 + X + 1 := by nlinarith [sq_nonneg X]
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  -- the odd-power identity: `r/τ = √X·(√τ/τ)`.
  have hrid : rncRadial v = Real.sqrt X * Real.sqrt τ := by
    rw [← Real.sqrt_mul hX0]
    have : X * τ = rncRadialSq v := by rw [hXdef]; field_simp
    rw [this, rncRadial]
  -- T1 — LINEAR in `r`, riding `√X ≤ X² + X + 1`.
  have hsX : Real.sqrt X ≤ X ^ 2 + X + 1 := by
    have h1 := sqrt_le_one_add_w1 hX0
    nlinarith [sq_nonneg X]
  have hT1bd : |T1| ≤ C_c * (Real.sqrt τ / τ) * ((X ^ 2 + X + 1) * gaussDdim τ v) := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hs0 : 0 ≤ Real.sqrt τ / τ := div_nonneg (Real.sqrt_nonneg τ) hτ.le
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadial v) :=
          mul_le_mul_of_nonneg_left (hCoeffLin q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (Real.sqrt τ / τ) * (Real.sqrt X * gaussDdim τ v) := by
          rw [hrid]; field_simp
      _ ≤ C_c * (Real.sqrt τ / τ) * ((X ^ 2 + X + 1) * gaussDdim τ v) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_c0 hs0)
          exact mul_le_mul_of_nonneg_right hsX hGτ0
  -- T2 — QUADRATIC in `X` (J4-676 pointwise brick).
  have hT2bd : |T2| ≤ (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v := by
    rw [hT2def, hXdef]
    exact residualQuadratic_pointwise_width1 (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W
      hM0 hW0 v (hdevU q hq v hvM) (hWbd v hvball)
  -- T3 — CONSTANT term.
  have hT3bd : |T3| ≤ L * gaussDdim τ v := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ = L * gaussDdim τ v := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  have hq0 : 0 ≤ (n : ℝ) ^ 2 * M * W / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM0) hW0) (by norm_num)
  -- T2/T3 monomials into the envelope: `X² ≤ X²+X+1`, `1 ≤ X²+X+1`.
  have hT2env : (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v
      ≤ (n : ℝ) ^ 2 * M * W / 4 * ((X ^ 2 + X + 1) * gaussDdim τ v) := by
    have hmono : X ^ 2 * gaussDdim τ v ≤ (X ^ 2 + X + 1) * gaussDdim τ v := by
      apply mul_le_mul_of_nonneg_right _ hGτ0; nlinarith
    calc (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v
        = (n : ℝ) ^ 2 * M * W / 4 * (X ^ 2 * gaussDdim τ v) := by ring
      _ ≤ (n : ℝ) ^ 2 * M * W / 4 * ((X ^ 2 + X + 1) * gaussDdim τ v) :=
          mul_le_mul_of_nonneg_left hmono hq0
  have hT3env : L * gaussDdim τ v ≤ L * ((X ^ 2 + X + 1) * gaussDdim τ v) :=
    mul_le_mul_of_nonneg_left (gaussDdim_le_quadEnv hτ v) hL0
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ C_c * (Real.sqrt τ / τ) * ((X ^ 2 + X + 1) * gaussDdim τ v)
          + (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v + L * gaussDdim τ v :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ ≤ C_c * (Real.sqrt τ / τ) * ((X ^ 2 + X + 1) * gaussDdim τ v)
          + (n : ℝ) ^ 2 * M * W / 4 * ((X ^ 2 + X + 1) * gaussDdim τ v)
          + L * ((X ^ 2 + X + 1) * gaussDdim τ v) := by
        exact add_le_add (add_le_add le_rfl hT2env) hT3env
    _ = ((n : ℝ) ^ 2 * M * W / 4 + L + C_c * (Real.sqrt τ / τ))
          * ((X ^ 2 + X + 1) * gaussDdim τ v) := by ring

/-! ### (W1N) — the `N = 1` width-1 quadratic affine near-packet bound. -/

/-- **★★ (W1N) — `uniformResidualN1_quadPoly_width1_affine`.**  The width-1 QUADRATIC AFFINE `N = 1`
    near-packet residual bound — the width-1 analogue of `CoeffU1Fix.uniformResidualN1_narrow_mixed_lin`:
        `|parametrixResidualN 1 g̃_q g̃⁻¹_q Θ u τ v|
            ≤ (B₀ + B₁·τ)·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v)`,   ∀ τ > 0, q ∈ K, ‖v‖ < ρ_u.
    ROUTE (J4-103 split `R₁ = R₀[u] + H₀[u′] + τ·R₀[u′]`): `R₀[u]` via the banked J4-676 star
    (`uniformResidual_quadPoly_bound_tau_width1`, `O(r²)` input); `H₀[u′] = G·w₁ ≤ W₁·G ≤ W₁·E`;
    `τ·R₀[u′]` via (W1L) and `√τ ≤ 1 + τ` (`τ·(C₀ + C₁√τ/τ) = C₀τ + C₁√τ ≤ C₁ + (C₀+C₁)τ`).  The
    affine `(B₀ + B₁·τ)` is the honest Sol-#15 shape (the `τ`-branch genuinely grows).  Same firewalled
    coefficient inputs as the banked `N = 1` chain.  NOT `a₁ = R/6`. -/
theorem uniformResidualN1_quadPoly_width1_affine (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (B₀ + B₁ * τ)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  obtain ⟨ρ₀, hρ₀0, Cu, hCu0, hbnd0⟩ :=
    uniformResidual_quadPoly_bound_tau_width1 g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u (hw 0) ρ_c C_c0 hρ_c hC_c0 hCoeffU0
  obtain ⟨ρ₁, hρ₁0, Cs₀, Cs₁, hCs00, hCs10, hbnd1⟩ :=
    uniformResidualLinear_quadPoly_bound_tau_width1 g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ (fun j => u (j + 1)) (hw 1) ρ_c C_c1 hρ_c hC_c1 hCoeffLin1
  set ρ_u : ℝ := min ρ₀ ρ₁ with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hρ₀0 hρ₁0
  obtain ⟨W₁, hW₁0, hW₁bd⟩ : ∃ W₁ : ℝ, 0 ≤ W₁ ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 1 v| ≤ W₁ := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, Cu + W₁ + Cs₁, Cs₀ + Cs₁, by positivity, by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hv0 : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_right _ _)
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  rw [parametrixResidual_one_split (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw]
  set X : ℝ := rncRadialSq v / τ with hXdef
  have hX0 : 0 ≤ X := div_nonneg (rncRadialSq_nonneg v) hτ.le
  set E : ℝ := (X ^ 2 + X + 1) * gaussDdim τ v with hEdef
  have hE0 : 0 ≤ E := by
    have : 0 ≤ X ^ 2 + X + 1 := by nlinarith [sq_nonneg X]
    exact mul_nonneg this (gaussDdim_nonneg τ v)
  set R0 : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v with hR0def
  set Mid : ℝ := heatParametrix 0 Θ (fun j => u (j + 1)) τ v with hMiddef
  set R0' : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) τ v with hR0'def
  have hb0 : |R0| ≤ Cu * E := hbnd0 τ hτ q hq v hv0
  have hb1 : |R0'| ≤ (Cs₀ + Cs₁ * (Real.sqrt τ / τ)) * E := hbnd1 τ hτ q hq v hv1
  have hmid : |Mid| ≤ W₁ * E := by
    have hfold : Mid = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
      rw [hMiddef, heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
    rw [hfold, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    have hv' : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W₁ := hW₁bd v hvball
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W₁ := mul_le_mul_of_nonneg_left hv' (gaussDdim_nonneg τ v)
      _ = W₁ * gaussDdim τ v := by ring
      _ ≤ W₁ * E := by
          rw [hEdef, hXdef]
          exact mul_le_mul_of_nonneg_left (gaussDdim_le_quadEnv hτ v) hW₁0
  -- `τ·R₀[u′]` branch: `√τ ≤ 1+τ`.
  have hττ : τ * (Real.sqrt τ / τ) = Real.sqrt τ := by field_simp
  have hsqle : Real.sqrt τ ≤ 1 + τ := sqrt_le_one_add_w1 hτ.le
  have hb1τ : τ * |R0'| ≤ (Cs₀ * τ + Cs₁ * (1 + τ)) * E := by
    calc τ * |R0'|
        ≤ τ * ((Cs₀ + Cs₁ * (Real.sqrt τ / τ)) * E) := mul_le_mul_of_nonneg_left hb1 hτ.le
      _ = (Cs₀ * τ + Cs₁ * (τ * (Real.sqrt τ / τ))) * E := by ring
      _ = (Cs₀ * τ + Cs₁ * Real.sqrt τ) * E := by rw [hττ]
      _ ≤ (Cs₀ * τ + Cs₁ * (1 + τ)) * E := by
          apply mul_le_mul_of_nonneg_right _ hE0
          have := mul_le_mul_of_nonneg_left hsqle hCs10
          linarith
  calc |R0 + Mid + τ * R0'|
      ≤ |R0 + Mid| + |τ * R0'| := abs_add_le _ _
    _ ≤ (|R0| + |Mid|) + |τ * R0'| := add_le_add (abs_add_le _ _) le_rfl
    _ = (|R0| + |Mid|) + τ * |R0'| := by rw [abs_mul, abs_of_pos hτ]
    _ ≤ (Cu * E + W₁ * E) + (Cs₀ * τ + Cs₁ * (1 + τ)) * E :=
        add_le_add (add_le_add hb0 hmid) hb1τ
    _ = ((Cu + W₁ + Cs₁) + (Cs₀ + Cs₁) * τ) * E := by ring

/-! ### (ENG) — the cutoff glue engine at an ABSTRACT nonneg envelope. -/

/-- **★ (ENG) — `cutoffResidual_envelope_engine`.**  The M2 cutoff glue engine
    (`WidthMarginEngine.cutoffResidual_narrow_tauUniform_engine`) with the dominating width-3/2 Gaussian
    replaced by an ABSTRACT nonneg envelope `E : Point n → ℝ` — the banked engine's proof only ever used
    `0 ≤ gaussDdim (3/2·t) v`, so this is the honest generality.  Region split (near / annulus / far)
    identical; `B = C + Kcof·Kc2 + 2n²·Kg·Kc1·Kder`.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_envelope_engine
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (E : Point n → ℝ) (hE0 : ∀ w, 0 ≤ E w)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * E w)
    (Kcof : ℝ) (hKcof : 0 ≤ Kcof)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ Kcof * E w)
    (Kder : ℝ) (hKder : 0 ≤ Kder)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ Kder * E w)
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
        ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v := by
  have hb2 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof hKc2
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
  refine ⟨by linarith, ?_⟩
  intro v
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hWnn : 0 ≤ E v := hE0 v
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
    calc |dtH v - laplaceBeltrami g gi H v| ≤ C * E v := hEnear v hb
      _ ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v := by
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
      have hAbd : |A| ≤ C * E v := by
        rw [hA, abs_mul]
        have hχle : |radialCutoff a b v| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
        calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
            ≤ 1 * (C * E v) :=
              mul_le_mul hχle (hEnear v hb) (abs_nonneg _) (by norm_num)
          _ = C * E v := by ring
      have hBbd : |B'| ≤ (Kcof * Kc2) * E v := by
        rw [hB', abs_mul]
        calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
            ≤ (Kcof * E v) * Kc2 :=
              mul_le_mul (hHann v ha2 hb) (hLapChi v ha2 hb) (abs_nonneg _)
                (mul_nonneg hKcof hWnn)
          _ = (Kcof * Kc2) * E v := by ring
      have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ Kg * Kc1 * (Kder * E v) := by
        intro i j
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hgibd v i j ha2 hb) (hDchi v i ha2 hb) (abs_nonneg _) hKg)
          (hDHann v j ha2 hb) (abs_nonneg _) (mul_nonneg hKg hKc1)
      have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * E v)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * E v)))
          = (n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * E v)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v := by
        rw [hCc]
        calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
            = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
              mul_le_mul_of_nonneg_left hSabs (by norm_num)
          _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * E v))) :=
              mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v := by ring
      calc |A - B' - Cc|
          ≤ C * E v + (Kcof * Kc2) * E v
              + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v :=
            htri.trans (add_le_add (add_le_add hAbd hBbd) hCcbd)
        _ = (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * E v := by ring
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

/-! ### (ANN) — the annulus derivative bound at the width-1 quadratic envelope. -/

/-- **★ (ANN) — `parametrixCofactor_deriv_annulus_quadEnv_tauUniform`.**  The annulus `∂ⱼ(G·cof)`
    bound at the WIDTH-1 QUADRATIC envelope: on `a² ≤ r² ≤ b²` (`0 < a`),
        `|∂ⱼ(G_τ·cof)(w)| ≤ Kd·(((r²_w/τ)² + r²_w/τ + 1)·G_τ(w))`,   `Kd` `τ`-FREE.
    Route: Leibniz `∂ⱼ(G·cof) = (−wⱼ/2τ)·G·cof + G·∂ⱼcof`; on the annulus `1/τ ≤ (r²/τ)/a²`, so the
    `(1/τ)·G` factor deposits into the POLYNOMIAL (`X ≤ X²+X+1`) instead of a wider Gaussian —
    `Kd = b·Kcof/(2a²) + Kdcof`.  The width-1 analogue of the banked
    `parametrixCofactor_deriv_annulus_narrow_tauUniform`.  NOT `a₁ = R/6`. -/
theorem parametrixCofactor_deriv_annulus_quadEnv_tauUniform
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => gaussDdim τ y * cofactor y) j w|
        ≤ Kd * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1) * gaussDdim τ w) := by
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
  refine ⟨b * Kcof / (2 * a ^ 2) + Kdcof, by positivity, ?_⟩
  intro τ hτ w j h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  set X : ℝ := rncRadialSq w / τ with hXdef
  have hX0 : 0 ≤ X := div_nonneg (rncRadialSq_nonneg w) hτ.le
  set En : ℝ := (X ^ 2 + X + 1) * gaussDdim τ w with hEndef
  have hEn0 : 0 ≤ En := by
    have : 0 ≤ X ^ 2 + X + 1 := by nlinarith [sq_nonneg X]
    exact mul_nonneg this hG0
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
  -- `(1/τ)·G ≤ (1/a²)·X·G ≤ (1/a²)·En` — the annulus deposits `1/τ` into the POLYNOMIAL.
  have hinvT : (1 / τ) * gaussDdim τ w ≤ (1 / a ^ 2) * En := by
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    have h1τX : 1 / τ ≤ X / a ^ 2 := by
      rw [div_le_div_iff₀ hτ ha2]
      calc 1 * a ^ 2 = a ^ 2 := by ring
        _ ≤ rncRadialSq w := h1
        _ = X * τ := by rw [hXdef]; field_simp
    have hXen : X * gaussDdim τ w ≤ En := by
      rw [hEndef]
      apply mul_le_mul_of_nonneg_right _ hG0
      nlinarith [sq_nonneg X]
    calc (1 / τ) * gaussDdim τ w
        ≤ (X / a ^ 2) * gaussDdim τ w := mul_le_mul_of_nonneg_right h1τX hG0
      _ = (1 / a ^ 2) * (X * gaussDdim τ w) := by ring
      _ ≤ (1 / a ^ 2) * En := by
          exact mul_le_mul_of_nonneg_left hXen (by positivity)
  have hGle : gaussDdim τ w ≤ En := by
    rw [hEndef, hXdef]; exact gaussDdim_le_quadEnv hτ w
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
  have hT1abs : b / (2 * τ) * gaussDdim τ w * Kcof ≤ b * Kcof / (2 * a ^ 2) * En := by
    have hcoef : (0 : ℝ) ≤ b * Kcof / 2 := by positivity
    calc b / (2 * τ) * gaussDdim τ w * Kcof
        = (b * Kcof / 2) * ((1 / τ) * gaussDdim τ w) := by field_simp
      _ ≤ (b * Kcof / 2) * ((1 / a ^ 2) * En) := mul_le_mul_of_nonneg_left hinvT hcoef
      _ = b * Kcof / (2 * a ^ 2) * En := by field_simp
  have hT2abs : gaussDdim τ w * Kdcof ≤ Kdcof * En := by
    calc gaussDdim τ w * Kdcof = Kdcof * gaussDdim τ w := by ring
      _ ≤ Kdcof * En := mul_le_mul_of_nonneg_left hGle hKdcof0
  calc |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w + gaussDdim τ w * pd cofactor j w|
      ≤ |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w| + |gaussDdim τ w * pd cofactor j w| :=
        abs_add_le _ _
    _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof + gaussDdim τ w * Kdcof := add_le_add hT1 hT2
    _ ≤ b * Kcof / (2 * a ^ 2) * En + Kdcof * En := add_le_add hT1abs hT2abs
    _ = (b * Kcof / (2 * a ^ 2) + Kdcof) * En := by ring

/-! ### (CUT) — ★★ the capstone: the CUTOFF `N = 1` residual at the width-1 quadratic envelope. -/

/-- **★★ (CUT) — `cutoffResidualN1_uniformFlow_width1_quad_affine`.**  THE WIDTH-1 QUADRATIC AFFINE
    CUTOFF `N = 1` RESIDUAL — the in-chart supply of the J4-677 `hgate` glue.  The exact analogue of the
    banked `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` with the width-3/2 collapse UNDONE:
        `∃ 0 < a < b < ρc, ∃ B₀ B₁ ≥ 0, ∀ τ>0, ∀ q ∈ K, ∀ v,
            |χ_{a,b}(v)·∂_τ P₁(v) − Δ_{g̃_q}(χ_{a,b}·P₁)(v)|
              ≤ (B₀ + B₁·τ)·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v)`.
    Near packet: (W1N).  Annulus value: the banked τ-uniform cofactor bounds (already width-1) widened
    `G ≤ E`.  Annulus derivative: (ANN).  Glue: (ENG) per `τ` at the envelope `E_τ`.  Same firewalled
    coefficient inputs (`hCoeffU0` `O(r²)` at `u`, `hCoeffLin1` `O(r)` at `u′`) as the banked chain.
    NOT `a₁ = R/6`. -/
theorem cutoffResidualN1_uniformFlow_width1_quad_affine (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v)
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B₀ B₁ : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
        |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
          ≤ (B₀ + B₁ * τ)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  classical
  obtain ⟨ρ_u, hρ_u0, Bᵣ0, Bᵣ1, hBᵣ0, hBᵣ1, hResU1⟩ :=
    uniformResidualN1_quadPoly_width1_affine g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  set bN : ℝ := ρ_u / 2 with hbN_def
  have hbN0 : 0 < bN := by rw [hbN_def]; linarith
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min (min bN (rmin / 2)) (ρc / 2) with hb_def
  have hb0 : 0 < b := lt_min (lt_min hbN0 (by linarith)) (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_lt_ρc : b < ρc := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_le_bN : b ≤ bN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hb_lt_rmin : b < rmin :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kcof0, hKcof00, hHann0U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) (hw 0).continuous
  obtain ⟨Kcof1, hKcof10, hHann1U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 1) (hw 1).continuous
  obtain ⟨Kder0, hKder00, hDHann0U⟩ :=
    parametrixCofactor_deriv_annulus_quadEnv_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      (hw 0).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) (hw 0) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) (hw 0) j).continuous)
  obtain ⟨Kder1, hKder10, hDHann1U⟩ :=
    parametrixCofactor_deriv_annulus_quadEnv_tauUniform a b ha0 hb0 (foldedCoeff Θ u 1)
      (hw 1).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 1) (hw 1) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 1) (hw 1) j).continuous)
  set B₀ : ℝ := Bᵣ0 + Kcof0 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder0 with hB0_def
  set B₁ : ℝ := Bᵣ1 + Kcof1 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder1 with hB1_def
  have hB0nn : 0 ≤ B₀ := by rw [hB0_def]; positivity
  have hB1nn : 0 ≤ B₁ := by rw [hB1_def]; positivity
  refine ⟨a, b, B₀, B₁, ha0, hab, hb_lt_ρc, hB0nn, hB1nn, ?_⟩
  intro τ hτ q hq v
  set En : Point n → ℝ :=
    fun w => ((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1) * gaussDdim τ w with hEndef
  have hEn0 : ∀ w, 0 ≤ En w := by
    intro w
    have hX0 : 0 ≤ rncRadialSq w / τ := div_nonneg (rncRadialSq_nonneg w) hτ.le
    have : 0 ≤ (rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1 := by
      nlinarith [sq_nonneg (rncRadialSq w / τ)]
    exact mul_nonneg this (gaussDdim_nonneg τ w)
  have hH1eq : (heatParametrix 1 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y
          + τ * (gaussDdim τ y * foldedCoeff Θ u 1 y) := by
    funext y
    rw [heatParametrix_one_split Θ u τ y]
    have e0 : heatParametrix 0 Θ u τ y = gaussDdim τ y * foldedCoeff Θ u 0 y := by
      rw [heatParametrix_folded]; simp
    have e1 : heatParametrix 0 Θ (fun j => u (j + 1)) τ y
        = gaussDdim τ y * foldedCoeff Θ u 1 y := by
      rw [heatParametrix_folded]; simp [foldedCoeff_shift]
    rw [e0, e1]
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 1 Θ u τ) w :=
    fun w => (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
  have hb_le_ρu2 : b ≤ ρ_u / 2 := hb_le_bN
  -- the NEAR bound from (W1N), converted to the `r² ≤ b²` ball shape.
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
        ≤ (Bᵣ0 + Bᵣ1 * τ) * En w := by
    intro w hw2
    have hnw : ‖w‖ < ρ_u := by
      have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
      have hb2 : rncRadialSq w ≤ (ρ_u / 2) ^ 2 := by
        refine le_trans hw2 ?_
        have := mul_le_mul hb_le_ρu2 hb_le_ρu2 hb_nonneg (by linarith)
        simpa [pow_two] using this
      have h2 : rncRadial w ≤ ρ_u / 2 := by
        rw [rncRadial]
        calc Real.sqrt (rncRadialSq w)
            ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hb2
          _ = ρ_u / 2 := by rw [Real.sqrt_sq (by linarith)]
      linarith
    have hs := hResU1 τ hτ q hq w hnw
    simpa only [parametrixResidualN] using hs
  -- the annulus VALUE bound (width-1 already; widened `G ≤ En`).
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 1 Θ u τ w| ≤ (Kcof0 + τ * Kcof1) * En w := by
    intro w h1 h2
    have hsplit : heatParametrix 1 Θ u τ w
        = gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w) := by
      rw [hH1eq]
    rw [hsplit]
    have hb0v := hHann0U τ hτ w h1 h2
    have hb1v := hHann1U τ hτ w h1 h2
    have hKsum : (0 : ℝ) ≤ Kcof0 + τ * Kcof1 := by positivity
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)|
        ≤ |gaussDdim τ w * foldedCoeff Θ u 0 w| + |τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)| :=
          abs_add_le _ _
      _ = |gaussDdim τ w * foldedCoeff Θ u 0 w| + τ * |gaussDdim τ w * foldedCoeff Θ u 1 w| := by
          rw [abs_mul τ (gaussDdim τ w * foldedCoeff Θ u 1 w), abs_of_pos hτ]
      _ ≤ Kcof0 * gaussDdim τ w + τ * (Kcof1 * gaussDdim τ w) :=
          add_le_add hb0v (mul_le_mul_of_nonneg_left hb1v hτ.le)
      _ = (Kcof0 + τ * Kcof1) * gaussDdim τ w := by ring
      _ ≤ (Kcof0 + τ * Kcof1) * En w := by
          exact mul_le_mul_of_nonneg_left (gaussDdim_le_quadEnv hτ w) hKsum
  -- the annulus DERIVATIVE bound from (ANN).
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 1 Θ u τ) j w| ≤ (Kder0 + τ * Kder1) * En w := by
    intro w j h1 h2
    have hpdA : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 0)) j w
    have hpdB : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 1)) j w
    have hpdτB : PdiffAt (fun y => τ * (gaussDdim τ y * foldedCoeff Θ u 1 y)) j w :=
      PdiffAt_of_contDiff _ (contDiff_const.mul ((gaussDdim_contDiff τ).mul (hw 1))) j w
    have hpdsplit : pd (heatParametrix 1 Θ u τ) j w
        = pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
          + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w := by
      rw [hH1eq, pd_add _ _ j w hpdA hpdτB,
        pd_const_mul τ (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w hpdB]
    rw [hpdsplit]
    have hd0 := hDHann0U τ hτ w j h1 h2
    have hd1 := hDHann1U τ hτ w j h1 h2
    calc |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
            + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w|
        ≤ |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + |τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := abs_add_le _ _
      _ = |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + τ * |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := by
          rw [abs_mul τ (pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w), abs_of_pos hτ]
      _ ≤ Kder0 * En w + τ * (Kder1 * En w) :=
          add_le_add hd0 (mul_le_mul_of_nonneg_left hd1 hτ.le)
      _ = (Kder0 + τ * Kder1) * En w := by ring
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  have hCnn : (0 : ℝ) ≤ Bᵣ0 + Bᵣ1 * τ := by positivity
  have hKcofnn : (0 : ℝ) ≤ Kcof0 + τ * Kcof1 := by positivity
  have hKdernn : (0 : ℝ) ≤ Kder0 + τ * Kder1 := by positivity
  have hres := (cutoffResidual_envelope_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 1 Θ u τ) (fun x => deriv (fun s => heatParametrix 1 Θ u s x) τ)
    a b ha0 hab hH2 hgisymm_q
    En hEn0
    (Bᵣ0 + Bᵣ1 * τ) hCnn hEnear_q
    (Kcof0 + τ * Kcof1) hKcofnn hHann
    (Kder0 + τ * Kder1) hKdernn hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v
  calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
      ≤ ((Bᵣ0 + Bᵣ1 * τ) + (Kcof0 + τ * Kcof1) * Kc2
            + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * (Kder0 + τ * Kder1)) * En v := hres
    _ = (B₀ + B₁ * τ) * En v := by rw [hB0_def, hB1_def]; ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.sqrt_le_one_add_w1
#print axioms QIQTH.HeatResidualBound.gaussDdim_le_quadEnv
#print axioms QIQTH.HeatResidualBound.uniformResidualLinear_quadPoly_bound_tau_width1
#print axioms QIQTH.HeatResidualBound.uniformResidualN1_quadPoly_width1_affine
#print axioms QIQTH.HeatResidualBound.cutoffResidual_envelope_engine
#print axioms QIQTH.HeatResidualBound.parametrixCofactor_deriv_annulus_quadEnv_tauUniform
#print axioms QIQTH.HeatResidualBound.cutoffResidualN1_uniformFlow_width1_quad_affine
