/-
  PullbackAffineBallLeg — J4-374: the PULLBACK-metric affine ball leg (Sol brick map, step 2c′).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / TRANSPORT-WIRING brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It is
  the PULLBACK-metric analogue of the banked ORIGINAL-metric ball-leg envelope
  `QIQTH.Transfer43Quad.ambientAffine_onBall` (J4-372).  The J4-373 glue verdict
  (`QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau`) collapses the gated witness's
  `heatOp` on the cutoff plateau to the PULLBACK-metric parametrix residual
  `parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv …) Θ u τ v`
  — NOT the ORIGINAL-metric residual that `ambientAffine_onBall` bounds.  This file supplies the
  envelope for the PULLBACK residual so the two compose.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on
  the whole convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FRAME-SURVEY VERDICT (dont-undercredit).

  •  `QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1` is stated for a **GENERIC**
     metric pair `(g, gi)`: it takes `(g gi : Point n → Fin n → Fin n → ℝ)` and every coefficient carry
     (`hdev`, `hcoeff0`, `hw0bd`, `hlap0`, `hcoeff1`, `hw1bd`, `hlap1`) as a ∀-bound HYPOTHESIS about
     THAT pair.  So instantiating it at the pullback pair
     `(uniformFlowPullbackMetric g gi hC hK q, uniformFlowPullbackMetricInv g gi hC hK q)` is DIRECT —
     no generic-slice clone was needed.

  •  The four banked flow-frame uniforms discharge the pullback-frame carries EXACTLY (all satisfiable
     for the concrete van-Vleck witness — kept as hypotheses here, discharged downstream):
       - `hcoeff0` (`O(r²)` coefficient)   ← `CoeffBoundsN1.hCoeffU0_vanVleck`
       - `hcoeff1` (`O(r)` shifted coeff)  ← `CoeffU1Fix.uniformCoeffLinear_bound`
       - `hlap0` / `hlap1` (Laplacian)     ← `UniformResidualBound.uniformFlowLaplaceBeltrami_w0_near_uniform`
       - `hdev` (inverse-metric deviation) ← `UniformFlowJetZero.uniformFlowPullbackMetricInv_dev_uniform`
     each of whose CONCLUSION already lives in the pullback frame `(uniformFlowPullbackMetric …,
     uniformFlowPullbackMetricInv …)`.  (`hw0bd`/`hw1bd` amplitude and `hw` smoothness are
     metric-independent — sup on compact / `foldedCoeff` regularity.)

  •  The transfer legs (`chartTransfer43_quad_from_nearIsometry`, `gaussDdim_le_gaussDdim_chart`) are
     metric-INDEPENDENT: they only involve `v`, the ORIGINAL flow-exp displacement
     `z := uniformFlowExp g gi hC hK q v − q`, and the Gaussian widths.  So they REUSE VERBATIM — the
     ambient displacement `z` is the ORIGINAL-metric flow-exp in BOTH the ambient and pullback legs.

  ## DELIVERABLES.
  •  (P1) `pullbackAffine_width1` — the raw affine graded width-`1` estimate for the PULLBACK-metric
     `N = 1` residual, by direct instantiation of the generic width-`1` estimate at the pullback pair.
  •  (P2) `pullbackAffine_onBall` — ★ the ball-leg envelope: mirrors `ambientAffine_onBall`'s
     `1 → 5/4` fold ∘ width-4/3 QUAD transfer on the PULLBACK residual, bounding it by the affine
     width-4/3 envelope on the ambient displacement `z`.
  •  (P3) `gatedHeatOp_pullbackAffine_onBallPlateau` — the composed BALL LEG of `AffineGateBound`:
     compose (P2) with the J4-373 plateau glue to bound the gated witness's `heatOp` on the
     ball ∩ plateau ∩ gate-interior by the affine width-4/3 envelope.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Transfer43Quad
import QIQTH.OnGateGlue

open Set Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.PullbackAffineBallLeg

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (P1) — the pullback-metric raw affine width-`1` estimate.
    ############################################################################### -/

/-- **★ (P1) — `pullbackAffine_width1`.**  THE PULLBACK-METRIC RAW AFFINE GRADED ESTIMATE at the
    pre-absorption width `1`.  DIRECT instantiation of the GENERIC
    `QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1` at the pullback pair
    `(uniformFlowPullbackMetric g gi hC hK q, uniformFlowPullbackMetricInv g gi hC hK q)` — the generic
    lemma takes the metric pair and every coefficient carry as ∀-bound hypotheses, so no generic-slice
    clone is needed.  The `O(r²)` carries (`hcoeff0`/`hw0bd`/`hlap0`) and the `O(r)` shifted-profile
    carries (`hcoeff1`/`hw1bd`/`hlap1`) plus the deviation `hdev` are exactly the conclusions of the
    banked flow-frame uniforms (`hCoeffU0_vanVleck`, `uniformCoeffLinear_bound`,
    `uniformFlowLaplaceBeltrami_w0_near_uniform`, `uniformFlowPullbackMetricInv_dev_uniform`) — all
    satisfiable; none equals the conclusion.  NOT `a₁ = R/6`. -/
theorem pullbackAffine_width1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (Md : ℝ) (hMd : 0 ≤ Md)
    (hdev : ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ Md * rncRadialSq v)
    (Cc0 W0 L0 : ℝ) (hCc0 : 0 ≤ Cc0) (hW0 : 0 ≤ W0) (hL0 : 0 ≤ L0)
    (hcoeff0 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ Cc0 * rncRadialSq v)
    (hw0bd : |foldedCoeff Θ u 0 v| ≤ W0)
    (hlap0 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L0)
    (Cc1 W1 L1 : ℝ) (hCc1 : 0 ≤ Cc1) (hW1 : 0 ≤ W1) (hL1 : 0 ≤ L1)
    (hcoeff1 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v)
    (hw1bd : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1)
    (hlap1 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1) :
    ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ (P₀ + P₁ * τ)
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) :=
  QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    Θ u hτ v hw Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
    Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1

/-! ###############################################################################
    ### (P2) — the pullback-metric ball-leg envelope.  ★
    ############################################################################### -/

/-- **★★ (P2) — `pullbackAffine_onBall`.**  THE PULLBACK-METRIC BALL LEG.  The exact analogue of
    `QIQTH.Transfer43Quad.ambientAffine_onBall`, but the bounded residual is in the PULLBACK metric
    `g̃_q = uniformFlowPullbackMetric g gi hC hK q`.  On the near-isometry ball `‖v‖ < r₁`, with
    `z := uniformFlowExp g gi hC hK q v − q` the ORIGINAL-metric flow-exp displacement,
        `∃ P₀ P₁ ≥ 0, |parametrixResidualN 1 g̃_q g̃i_q Θ u τ v|
            ≤ (P₀ + P₁·τ)·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Route (VERBATIM to `ambientAffine_onBall`, transfer legs metric-independent): the pullback width-1
    chart bound (P1) produces `gaussDdim τ v`; a single `1 → 5/4` fold
    (`gaussDdim_le_gaussDdim_chart (c=1, d=5/4)`, `√(5/4)ⁿ`) lands the chart Gaussian at width `5/4`,
    the LHS of the QUAD transfer `chartTransfer43_quad_from_nearIsometry`; the transfer then carries the
    geometric envelope to the ambient displacement `z` at width `4/3`.  The
    `√(5/4)ⁿ·(25/16)·√((4/3)/(5/4))ⁿ` normalizer folds into BOTH affine coefficients.

    HONESTY.  Every coefficient hypothesis is the SAME satisfiable pointwise pullback-frame carry as
    (P1) (all instances of the banked flow-frame uniforms — see the header frame survey); none equals
    the conclusion.  NOT `a₁ = R/6`. -/
theorem pullbackAffine_onBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ → ∀ τ : ℝ, 0 < τ →
      ∀ Md : ℝ, 0 ≤ Md →
        (∀ i j : Fin n,
          |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
            ≤ Md * rncRadialSq v) →
      ∀ Cc0 W0 L0 : ℝ, 0 ≤ Cc0 → 0 ≤ W0 → 0 ≤ L0 →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ Cc0 * rncRadialSq v →
        |foldedCoeff Θ u 0 v| ≤ W0 →
        |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L0 →
      ∀ Cc1 W1 L1 : ℝ, 0 ≤ Cc1 → 0 ≤ W1 → 0 ≤ L1 →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v →
        |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 →
        |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ (fun j => u (j + 1)) 0) v|
              ≤ L1 →
      ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (P₀ + P₁ * τ)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨r₁, hr₁pos, htrans⟩ :=
    QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry g gi hC hK
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv τ hτ Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
    Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the pullback-frame affine width-1 QUAD estimate (P1).
  obtain ⟨P₀, P₁, hP₀, hP₁, hbound⟩ :=
    pullbackAffine_width1 g gi hC hK q Θ u hτ v hw Md hMd hdev
      Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
      Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the QUAD transfer at `(q, v, τ)` (metric-independent — reused verbatim).
  have htr := htrans q hq v hv τ hτ
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  -- the `1 → 5/4` chart-Gaussian fold (metric-independent).
  have hfold : gaussDdim τ v ≤ Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) v := by
    have h := QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 5 / 4)
      (by norm_num) (by norm_num) hτ (v := v) (w := v)
      (by have := rncRadialSq_nonneg v; linarith)
    simpa using h
  -- nonnegativity facts.
  have hXv0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hQv0 : 0 ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hXv0) zero_le_one
  have hS54_0 : 0 ≤ Real.sqrt (5 / 4) ^ n := by positivity
  have hC0 : 0 ≤ Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n) := by positivity
  have hfac0 : 0 ≤ P₀ + P₁ * τ := add_nonneg hP₀ (mul_nonneg hP₁ hτ.le)
  -- the geometric-envelope chain: chart width-1 envelope ≤ constant × ambient width-4/3 envelope.
  have henv : ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v
      ≤ Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
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
  -- fold the normalizer into both affine coefficients.
  refine ⟨P₀ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)),
    P₁ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)),
    mul_nonneg hP₀ hC0, mul_nonneg hP₁ hC0, ?_⟩
  calc |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
      ≤ (P₀ + P₁ * τ) * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hbound
    _ ≤ (P₀ + P₁ * τ)
          * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)
              * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z)) :=
        mul_le_mul_of_nonneg_left henv hfac0
    _ = (P₀ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n))
          + P₁ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)) * τ)
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

/-! ###############################################################################
    ### (P3) — the composed BALL LEG of `AffineGateBound`.
    ############################################################################### -/

/-- **★★ (P3) — `gatedHeatOp_pullbackAffine_onBallPlateau`.**  THE BALL LEG OF `AffineGateBound`
    (composed).  On the ball ∩ plateau ∩ gate-interior, the GATED witness's `heatOp` at the exp point is
    bounded by the affine width-4/3 envelope on the ambient displacement `z := uniformFlowExp g gi hC hK
    q v − q`:
        `|heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 …)) τ (exp q v) q|
            ≤ (P₀ + P₁·τ)·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Route: the J4-373 plateau glue `QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau`
    (transport (2a) ∘ cutoff collapse) rewrites the gated `heatOp` to the PULLBACK-metric residual
    `parametrixResidualN 1 g̃_q g̃i_q Θ u τ v`; the pullback ball-leg envelope (P2) then bounds it.  The
    glue carries (`hpt` chart-inverse, `hlap` naturality, `hS` gate-interior, `hq`, `hv` plateau) and
    the envelope carries (`Md`/`hdev`, `Cc0…L0`, `Cc1…L1`) are the SAME satisfiable inputs the banked
    lemmas take — all discharged downstream from `OnGateGlue.uniformInverseChart_leftInverse_of_lt`,
    `OnGateGlue.laplaceBeltrami_globalCutoffWitness_naturality`, and the flow-frame uniforms; none
    equals the conclusion.  NOT `a₁ = R/6`. -/
theorem gatedHeatOp_pullbackAffine_onBallPlateau (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ → ∀ τ : ℝ, 0 < τ →
      ∀ {a b : ℝ}, 0 < a → a < b → rncRadialSq v < a ^ 2 →
        S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
        uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v →
        laplaceBeltrami g gi
            (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ p q)
            (uniformFlowExp g gi hC hK q v)
          = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v →
      ∀ Md : ℝ, 0 ≤ Md →
        (∀ i j : Fin n,
          |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
            ≤ Md * rncRadialSq v) →
      ∀ Cc0 W0 L0 : ℝ, 0 ≤ Cc0 → 0 ≤ W0 → 0 ≤ L0 →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ Cc0 * rncRadialSq v →
        |foldedCoeff Θ u 0 v| ≤ W0 →
        |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L0 →
      ∀ Cc1 W1 L1 : ℝ, 0 ≤ Cc1 → 0 ≤ W1 → 0 ≤ L1 →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v →
        |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 →
        |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ (fun j => u (j + 1)) 0) v|
              ≤ L1 →
      ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (P₀ + P₁ * τ)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨r₁, hr₁pos, hball⟩ := pullbackAffine_onBall g gi hC hK Θ u hw
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv τ hτ a b ha hab hplateau hS hpt hlap
    Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
    Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the pullback ball-leg envelope (P2) at `(q, v, τ)`.
  obtain ⟨P₀, P₁, hP₀, hP₁, hbound⟩ :=
    hball q hq v hv τ hτ Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
      Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the J4-373 plateau glue: the gated `heatOp` = the pullback-metric residual.
  have hglue := QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau
    g gi hC hK S Θ u ha hab q v hq hS hpt hlap hplateau
  exact ⟨P₀, P₁, hP₀, hP₁, by rw [hglue]; exact hbound⟩

end QIQTH.PullbackAffineBallLeg

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.PullbackAffineBallLeg.pullbackAffine_width1
#print axioms QIQTH.PullbackAffineBallLeg.pullbackAffine_onBall
#print axioms QIQTH.PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau
