/-
  LegUniformization — J4-378: THE FLOW-FRAME UNIFORMIZATION of the plateau (ball) affine leg's
  analytic core.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  UNIFORMIZATION / GLUE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  The banked
  plateau leg `QIQTH.PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau` (J4-374) emits its
  affine coefficient pair `(P₀, P₁)` as a PER-POINT existential (a `∃ P₀ P₁` INSIDE the `∀ q v τ`), fed
  by per-point coefficient carries (`Md`, `Cc0`, `W0`, `L0`, `Cc1`, `W1`, `L1`).  The 3-region capstone
  `QIQTH.AffineGateCapstone.affineGateBound_of_legs` (J4-377), by contrast, demands a SINGLE `(P₀, P₁)`
  pair valid uniformly over `q ∈ K`, over all `v` in the region, and over all `τ > 0`.  This file
  performs the plateau uniformization: it obtains all the banked compact-`K` uniform coefficient
  suppliers ONCE (before the `∀ q v τ`), verifies that the banked raw-residual affine bound's
  `(P₀, P₁)` formulas
      `P₀ = (L0 + Cc0 + ¼n²·Md·W0) + W1 + Cc1`,     `P₁ = Cc1 + ¼n²·Md·W1 + L1`
  (from `QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1`) are ALGEBRAIC in the
  uniform constants only — NOT secretly `(q, v, τ)`-dependent — and folds the pre-absorption width `1`
  through the near-isometry chart transfer to the ambient width `4/3`, yielding a SINGLE uniform pair.

  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable
  hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing file edited, nothing
  committed.  `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-wiring stack AND on the
  surviving LABELLED inputs (here: the two uniform coefficient bounds `hCoeffU0`/`hCoeffLin1`, which are
  the banked satisfiable outputs of `CoeffBoundsN1.hCoeffU0_vanVleck` / `CoeffU1Fix.uniformCoeffLinear_bound`,
  and the geometric data piles).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SUPPLIER MAP (U2, plateau leg).  Each per-point carry of the banked ball leg is discharged by a
  banked compact-`K` uniform supplier (all `∃ρ ∃const, ∀ q∈K ∀v ‖v‖<ρ, …`, hence a SINGLE constant over
  `K`):
    - `Md`  (inverse-metric deviation)   ← `UniformFlowJetZero.uniformFlowPullbackMetricInv_dev_uniform`
    - `L0`  (Laplacian of `w₀`)          ← `UniformResidualBound.uniformFlowLaplaceBeltrami_w0_near_uniform` @ `u`
    - `L1`  (Laplacian of `w₁`)          ← `UniformResidualBound.uniformFlowLaplaceBeltrami_w0_near_uniform` @ `u'`
    - `W0`/`W1` (amplitude sups)         ← sup-on-compact of `foldedCoeff` (`q`-independent)
    - `Cc0` (`O(r²)` coeff at `u`)       ← hypothesis (banked `hCoeffU0_vanVleck`, satisfiable)
    - `Cc1` (`O(r)`  coeff at `u'`)      ← hypothesis (banked `uniformCoeffLinear_bound`, satisfiable)
  the near-isometry width transfer being `Transfer43Quad.chartTransfer43_quad_from_nearIsometry`.

  ## DELIVERABLE.
  •  `plat_residual_uniform_width43` — ★ the UNIFORM plateau residual envelope: a single `(ρ, P₀, P₁)`
     with `0 < ρ`, `0 ≤ P₀`, `0 ≤ P₁` such that for ALL `τ > 0`, ALL `q ∈ K`, ALL `v` with `‖v‖ < ρ`,
     the pullback-metric `N = 1` parametrix residual is bounded by the affine width-`4/3` envelope on the
     ambient displacement `z := uniformFlowExp q v − q`.  This is the uniformized analytic core of the
     plateau leg (everything up to the pointwise-uniform transport / gate glue).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AffineRawResidual
import QIQTH.Transfer43Quad
import QIQTH.UniformFlowJetZero
import QIQTH.UniformResidualBound
import QIQTH.OnGateGlue
import QIQTH.UniformChartRadius
import QIQTH.RadiusOrdering
import QIQTH.GlobalWitnessHunif
import QIQTH.SmoothCutoff
import QIQTH.VanVleckCancellation

open Set Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.RNCDecay
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.LegUniformization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ J4-378 — `plat_residual_uniform_width43`.**  THE UNIFORM PLATEAU RESIDUAL ENVELOPE.  A single
    coefficient pair `(P₀, P₁)` and radius `ρ > 0` such that, uniformly over `q ∈ K` and over `v` with
    `‖v‖ < ρ` and all `τ > 0`, the pullback-metric `N = 1` parametrix residual is bounded by the affine
    width-`4/3` quadratic envelope on the ambient displacement `z := uniformFlowExp g gi hC hK q v − q`:
        `|parametrixResidualN 1 g̃_q g̃i_q Θ u τ v|
            ≤ (P₀ + P₁·τ)·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.

    ROUTE (uniformizing `PullbackAffineBallLeg.pullbackAffine_onBall`, whose per-point `∃ P₀ P₁` hides the
    algebraic formula):  obtain the banked compact-`K` uniform suppliers ONCE — `Md` from
    `uniformFlowPullbackMetricInv_dev_uniform`, `L0`/`L1` from `uniformFlowLaplaceBeltrami_w0_near_uniform`
    at the base / shifted profile, `W0`/`W1` by sup-on-compact of the (`q`-independent) folded
    coefficients — then, at each point, assemble the EXPLICIT width-`1` raw affine bound from the banked
    per-term slices (`rawResidualN0_graded_quadPoly_width1`, the amplitude carry,
    `tauResidualN0_Or_graded_quadPoly_width1`) whose `(P₀, P₁)` are
    `((L0+Cc0+¼n²MdW0)+W1+Cc1, Cc1+¼n²MdW1+L1)` — ALGEBRAIC in the uniform constants only — and fold
    `1 → 5/4 → 4/3` through the near-isometry transfer `chartTransfer43_quad_from_nearIsometry`, folding
    the width normalizer `√(5/4)ⁿ·(25/16)·√((4/3)/(5/4))ⁿ` into both coefficients.

    The carries `hCoeffU0` (`O(r²)` at `u`) and `hCoeffLin1` (`O(r)` at `u'`) are the banked satisfiable
    uniform outputs of `hCoeffU0_vanVleck` / `uniformCoeffLinear_bound`; the geometric data
    (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`) and folded smoothness `hw` are genuine.  NONE
    equals the conclusion.  NOT `a₁ = R/6`. -/
theorem plat_residual_uniform_width43 (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ ρ P₀ P₁ : ℝ, 0 < ρ ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ (P₀ + P₁ * τ)
            * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                  + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  classical
  -- (U2) the banked compact-`K` uniform suppliers, obtained ONCE.
  obtain ⟨r_d, hr_d0, Md, hMd0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨r_L0, hr_L00, L0, hL00, hlap0U⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u (hw 0)
  obtain ⟨r_L1, hr_L10, L1, hL10, hlap1U⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ (fun j => u (j + 1)) (hw 1)
  obtain ⟨r_T, hr_T0, htransU⟩ :=
    QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry g gi hC hK
  set ρ : ℝ := min r_d (min r_L0 (min r_L1 (min r_T ρ_c))) with hρdef
  have hρ0 : 0 < ρ := lt_min hr_d0 (lt_min hr_L00 (lt_min hr_L10 (lt_min hr_T0 hρ_c)))
  -- the amplitude sups (metric-independent — sup of the folded coefficient on the closed ball).
  obtain ⟨W0, hW00, hW0bd⟩ : ∃ W0 : ℝ, 0 ≤ W0 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ, |foldedCoeff Θ u 0 v| ≤ W0 := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ).exists_bound_of_continuousOn
        (hw 0).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨W1, hW10, hW1bd⟩ : ∃ W1 : ℝ, 0 ≤ W1 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ, |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  -- the width-`1 → 4/3` normalizer (constant; folds into both coefficients).
  set N : ℝ := Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  -- the EXPLICIT width-`1` raw affine coefficients (algebraic in the uniform constants only).
  set P0₁ : ℝ := (L0 + C_c0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0) + W1 + C_c1 with hP0₁def
  set P1₁ : ℝ := C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1 with hP1₁def
  have hP0₁0 : 0 ≤ P0₁ := by rw [hP0₁def]; positivity
  have hP1₁0 : 0 ≤ P1₁ := by rw [hP1₁def]; positivity
  refine ⟨ρ, P0₁ * N, P1₁ * N, hρ0, mul_nonneg hP0₁0 hN0, mul_nonneg hP1₁0 hN0, ?_⟩
  intro τ hτ q hq v hv
  -- radius extractions.
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL0 : ‖v‖ < r_L0 := lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_left _ _))
  have hvL1 : ‖v‖ < r_L1 :=
    lt_of_lt_of_le hv ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hvT : ‖v‖ < r_T :=
    lt_of_lt_of_le hv
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hvc : ‖v‖ < ρ_c :=
    lt_of_lt_of_le hv
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  -- pointwise carries at `(q, v)` from the uniform suppliers.
  have hdev : ∀ i j : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v i j
      - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v := fun i j => hdevU q hq v hvd i j
  have hlap0 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L0 := hlap0U q hq v hvL0
  have hlap1 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1 :=
    hlap1U q hq v hvL1
  have hcoeff0 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v := hCoeffU0 q hq v hvc
  have hcoeff1 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v := hCoeffLin1 q hq v hvc
  have hw0bd : |foldedCoeff Θ u 0 v| ≤ W0 := hW0bd v hvball
  have hw1bd : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 := hW1bd v hvball
  have hcd0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := (hw 0).contDiffAt.of_le le_top
  have hcd1 : ContDiffAt ℝ 2 (foldedCoeff Θ (fun j => u (j + 1)) 0) v :=
    (hw 1).contDiffAt.of_le le_top
  -- abbreviations for the pullback pair.
  set gM : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hgMdef
  set giM : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hgiMdef
  -- (A) the base-profile `N = 0` residual via the banked width-`1` graded quadratic slice.
  have hA := QIQTH.AffineRawResidual.rawResidualN0_graded_quadPoly_width1 gM giM Θ u hτ v hcd0
    C_c0 Md W0 L0 hC_c0 hMd0 hW00 hL00 hcoeff0 hdev hw0bd hlap0
  -- (B) the shifted-profile amplitude `H₀[u'] = G_τ·w₁`.
  have hmideq : heatParametrix 0 Θ (fun j => u (j + 1)) τ v
      = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
    rw [heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
  have hq1poly : (1 : ℝ) ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 := by
    nlinarith [sq_nonneg (rncRadialSq v / τ), div_nonneg (rncRadialSq_nonneg v) hτ.le]
  have hB : |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
      ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [hmideq, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W1 := mul_le_mul_of_nonneg_left hw1bd (gaussDdim_nonneg τ v)
      _ = W1 * (1 * gaussDdim τ v) := by ring
      _ ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
          apply mul_le_mul_of_nonneg_left _ hW10
          exact mul_le_mul_of_nonneg_right hq1poly (gaussDdim_nonneg τ v)
  -- (C) the `τ·R₀[u']` branch via the banked `O(r)` shifted-profile slice.
  have hCbr : |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v|
      ≤ (C_c1 + (C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [abs_mul, abs_of_pos hτ]
    exact QIQTH.AffineRawResidual.tauResidualN0_Or_graded_quadPoly_width1 gM giM Θ
      (fun j => u (j + 1)) hτ v hcd1 C_c1 Md W1 L1 hC_c1 hMd0 hW10 hL10 hcoeff1 hdev hw1bd hlap1
  -- the EXPLICIT width-`1` raw affine bound (mirrors `rawResidualN1_affine_graded_quadPoly_width1`).
  have hwidth1 : |parametrixResidualN 1 gM giM Θ u τ v|
      ≤ (P0₁ + P1₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [parametrixResidual_one_split gM giM Θ u τ hτ v hw]
    calc |parametrixResidualN 0 gM giM Θ u τ v
            + heatParametrix 0 Θ (fun j => u (j + 1)) τ v
            + τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v|
        ≤ |parametrixResidualN 0 gM giM Θ u τ v
            + heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
            + |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v| :=
          abs_add_le _ _
      _ ≤ (|parametrixResidualN 0 gM giM Θ u τ v|
            + |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|)
            + |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((L0 + C_c0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0)
                * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v)
              + W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v))
            + (C_c1 + (C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
                * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) :=
          add_le_add (add_le_add hA hB) hCbr
      _ = (P0₁ + P1₁ * τ)
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
          rw [hP0₁def, hP1₁def]; ring
  -- the `1 → 5/4 → 4/3` fold (mirrors `PullbackAffineBallLeg.pullbackAffine_onBall`).
  have htr := htransU q hq v hvT τ hτ
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  have hfold : gaussDdim τ v ≤ Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) v := by
    have h := QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 5 / 4)
      (by norm_num) (by norm_num) hτ (v := v) (w := v)
      (by have := rncRadialSq_nonneg v; linarith)
    simpa using h
  have hXv0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hQv0 : 0 ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hXv0) zero_le_one
  have hS54_0 : 0 ≤ Real.sqrt (5 / 4) ^ n := by positivity
  have hfac0 : 0 ≤ P0₁ + P1₁ * τ := add_nonneg hP0₁0 (mul_nonneg hP1₁0 hτ.le)
  have henv : ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v
      ≤ N * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
    rw [hNdef]
    calc ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v
        ≤ ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1)
            * (Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) v) :=
          mul_le_mul_of_nonneg_left hfold hQv0
      _ = Real.sqrt (5 / 4) ^ n
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (5 / 4 * τ) v) := by ring
      _ ≤ Real.sqrt (5 / 4) ^ n
            * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
                * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z)) :=
          mul_le_mul_of_nonneg_left htr hS54_0
      _ = Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)
            * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring
  calc |parametrixResidualN 1 gM giM Θ u τ v|
      ≤ (P0₁ + P1₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hwidth1
    _ ≤ (P0₁ + P1₁ * τ)
          * (N * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z)) :=
        mul_le_mul_of_nonneg_left henv hfac0
    _ = (P0₁ * N + P1₁ * N * τ)
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

/-- **★★ J4-378 — `gatedHeatOp_plateau_uniform`.**  THE UNIFORMIZED PLATEAU LEG (`hplat_uniform`).
    The single-`(P₀, P₁)` version of the banked ball leg
    `PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau`, in the EXACT binder shape the
    3-region capstone `AffineGateCapstone.affineGateBound_of_legs` consumes for its `hplat` hypothesis
    (specialized to the concrete chart `W = uniformInverseChart g gi hC hK`): a SINGLE cutoff radius pair
    `(a, b)` and coefficient pair `(P₀, P₁)`, valid uniformly over `q ∈ K`, over the whole plateau region
    `rncRadialSq v < a²`, and over all `τ > 0`, bounding the GATED witness's `heatOp` at the exp point by
    the affine width-`4/3` envelope on `z := uniformFlowExp g gi hC hK q v − q`.

    ROUTE: obtain the uniform residual envelope `plat_residual_uniform_width43` ONCE (giving `ρ, P₀, P₁`);
    obtain the banked uniform chart-germ (`uniformInverseChart_huniformChart`) and naturality
    (`laplaceBeltrami_uniformFlow_naturality_forall_f`) radii; choose `b := m/2`, `a := m/4` below
    `m := min ρ (min δ₀ rN)`, so the plateau constraint `rncRadialSq v < a²` forces
    `‖v‖ ≤ rncRadial v < a < b < m`, discharging every radius.  For each point, discharge the glue carries
    `hpt` (chart left-inverse germ) and `hlap` (Laplacian naturality + germ congruence) exactly as the
    banked `gatedWitnessN1_hEboundW_le_lin`, rewrite the gated `heatOp` to the pullback residual via the
    banked plateau glue `OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau`, and close with the
    uniform residual envelope.  The `(P₀, P₁)` is threaded UNCHANGED from the residual core — genuinely a
    single pair over `K`.  The carries `hCoeffU0`/`hCoeffLin1` are the banked satisfiable uniform outputs;
    the geometric data and folded smoothness are genuine; NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem gatedHeatOp_plateau_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (S : Point n → Set (Point n))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ a b P₀ P₁ : ℝ, 0 < a ∧ a < b ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n, rncRadialSq v < a ^ 2 →
        S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (P₀ + P₁ * τ)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨ρ, P₀, P₁, hρ0, hP00, hP10, hres⟩ :=
    plat_residual_uniform_width43 g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set m : ℝ := min ρ (min δ₀ rN) with hmdef
  have hm0 : 0 < m := lt_min hρ0 (lt_min hδ₀ hrNpos)
  set b : ℝ := m / 2 with hbdef
  set a : ℝ := m / 4 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hbm : b < m := by rw [hbdef]; linarith
  have ham : a < m := lt_trans hab hbm
  refine ⟨a, b, P₀, P₁, ha0, hab, hP00, hP10, ?_⟩
  intro τ hτ q hq v hplateau hS
  -- the plateau constraint forces `‖v‖ < a`, hence below every supplier radius.
  have hrv : rncRadial v < a := by
    have hsq : Real.sqrt (rncRadialSq v) < Real.sqrt (a ^ 2) :=
      Real.sqrt_lt_sqrt (rncRadialSq_nonneg v) hplateau
    rw [Real.sqrt_sq ha0.le] at hsq
    exact hsq
  have hnv : ‖v‖ < a := lt_of_le_of_lt (norm_le_rncRadial v) hrv
  have hvρ : ‖v‖ < ρ := lt_of_lt_of_le (lt_trans hnv ham) (min_le_left _ _)
  have hvδ₀ : ‖v‖ < δ₀ :=
    lt_of_lt_of_le (lt_trans hnv ham) ((min_le_right _ _).trans (min_le_left _ _))
  have hvrN : ‖v‖ < rN :=
    lt_of_lt_of_le (lt_trans hnv ham) ((min_le_right _ _).trans (min_le_right _ _))
  -- discharge the glue carries `hpt`, `hlap` (mirrors `gatedWitnessN1_hEboundW_le_lin`).
  obtain ⟨hchartGerm, _hchartOC⟩ := hchart q hq
  obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
  have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by simpa using hgerm.eq_of_nhds
  have hf : ContDiffAt ℝ 2
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      (uniformFlowExp g gi hC hK q v) := by
    have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
        (W q (uniformFlowExp g gi hC hK q v)) := by
      apply ContDiffAt.mul
      · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
    exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
  have hprofilegerm :
      (fun z => globalCutoffParametrixWitnessN 1 Θ u a b W τ
          (uniformFlowExp g gi hC hK q z) q)
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
  have hg1 : ∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v) :=
    fun a' b' => (hg a' b').contDiffAt.of_le le_top
  have hU : IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) :=
    hgnd (uniformFlowExp g gi hC hK q v)
  have hGGi : ∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
      * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0 :=
    fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc
  have hGiG : ∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
      * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0 :=
    metricInv_left_of_right
      (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
      (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
      (hgnd (uniformFlowExp g gi hC hK q v))
      (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitnessN 1 Θ u a b W τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
    have hn := hnat
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      q hq v hvrN hg1 hf hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  -- rewrite the gated heatOp to the pullback residual, then close with the uniform envelope.
  rw [QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau g gi hC hK S Θ u ha0 hab
      q v hq hS hpt hlap hplateau]
  exact hres τ hτ q hq v hvρ

end QIQTH.LegUniformization

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.LegUniformization.plat_residual_uniform_width43
#print axioms QIQTH.LegUniformization.gatedHeatOp_plateau_uniform
