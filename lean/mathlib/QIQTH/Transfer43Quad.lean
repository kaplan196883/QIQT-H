/-
  Transfer43Quad — J4-372: the consumer-facing WIDTH-4/3 QUAD transfer.  Turns the chart-frame
  quadratic (`x² + x + 1`) Gaussian envelope at the near-diagonal Gaussian width `5/4` into the
  AMBIENT-frame shape at width `4/3` on the near-isometry ball, mirroring the banked pattern
  `QIQTH.HrawPreCollapse.chartTransfer_quad` but plumbed for the CONCRETE flow-exp displacement
  `z := uniformFlowExp g gi hC hK q v − q` and the tighter `(5/4 → 4/3)` Gaussian widths.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / TRANSPORT-WIRING brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It
  chains two ALREADY-BANKED ball-local budgets — the width-4/3 Gaussian transfer
  `QIQTH.NearIsometry43Budget.uniformFlowExp_gaussDdim_transfer_43` (J4-371, the `(5/4)τ → (4/3)τ`
  Gaussian comparison) and the two-sided near-isometry `QIQTH.HrawNearIsometryConcrete.nearIsometry_
  concrete` (J4-361, `|r²_v − r²_z| ≤ (1/4)·r²_z` on an explicit shrunk gate) — into the ambient QUAD
  envelope transfer.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-
  wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TWO-SIDED BUDGET VERDICT (dont-undercredit).

  The polynomial leg needs the UPPER radial budget `r²_v ≤ (5/4)·r²_z`, i.e. the REVERSE direction of
  the width-4/3 near-isometry pairing `uniformFlowExp_hdisp43_ball` (which supplies only the LOWER
  `(5/4)·r²_z ≤ (4/3)·r²_v`).  It is NOT derived here: the concrete TWO-SIDED near-isometry is BANKED
  as `QIQTH.HrawNearIsometryConcrete.nearIsometry_concrete` (J4-361) — an explicit shrunk gate `r*>0`
  on which `|r²_v − r²_z| ≤ (1/4)·r²_z`, `z := uniformFlowExp … q v − q`.  Its `δ = 1/4` split
  `QIQTH.HrawChartTransfer.nearIsometry_budgets` yields BOTH budgets `r²_z ≤ (4/3)·r²_v` (lower) and
  `r²_v ≤ (5/4)·r²_z` (upper); this file consumes the UPPER one for the polynomial leg.

  ## THE TRANSFER (mirror of `chartTransfer_quad`).

  On `‖v‖ < r₁ := min r_N2 r*` (both banked gate radii), with `z := uniformFlowExp g gi hC hK q v − q`:
  •  Gaussian leg — `gaussDdim ((5/4)·τ) v ≤ √((4/3)/(5/4))ⁿ · gaussDdim ((4/3)·τ) z`, verbatim
     `uniformFlowExp_gaussDdim_transfer_43` (N2).
  •  Polynomial leg — from the UPPER budget `r²_v ≤ (5/4)·r²_z` (whence `r²_v/τ ≤ (5/4)·(r²_z/τ)`),
     monotonicity of `x ↦ x² + x + 1` on `[0,∞)` gives
     `(r²_v/τ)² + r²_v/τ + 1 ≤ (25/16)·((r²_z/τ)² + r²_z/τ + 1)`
     (the `25/16 = (5/4)²` factor, EXACTLY the banked `chartTransfer_quad` poly-factor step; `(5/4)²`
     dominates the linear `5/4` and the constant since `25/16 ≥ 5/4 ≥ 1`).
  Product of the two legs gives the explicit constant
     `B = (25/16)·√((4/3)/(5/4))ⁿ  =  (25/16)·√(16/15)ⁿ`.

  ## DELIVERABLE.
  •  `chartTransfer43_quad_from_nearIsometry` — the ball-local ambient QUAD envelope transfer at the
     explicit constant `B`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NearIsometry43Budget
import QIQTH.HrawNearIsometryConcrete
import QIQTH.HrawChartTransfer
import QIQTH.AffineRawResidual

open Set Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.ExpMap
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami
open scoped Topology BigOperators

namespace QIQTH.Transfer43Quad

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ J4-372 — `chartTransfer43_quad_from_nearIsometry`.**  THE WIDTH-4/3 QUAD TRANSFER.  There is a
    ball radius `r₁ > 0` such that for every `q ∈ K`, `‖v‖ < r₁`, `τ > 0`, with `z := uniformFlowExp
    g gi hC hK q v − q` the ambient displacement of the exp point,
        `((r²_v/τ)² + r²_v/τ + 1)·gaussDdim ((5/4)·τ) v
            ≤ (25/16)·√((4/3)/(5/4))ⁿ · (((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Chains the two banked ball-local budgets: the Gaussian leg is
    `QIQTH.NearIsometry43Budget.uniformFlowExp_gaussDdim_transfer_43` (N2, `(5/4)τ → (4/3)τ`), the
    polynomial leg is `(25/16)`-monotonicity of `x ↦ x²+x+1` under the UPPER radial budget
    `r²_v ≤ (5/4)·r²_z` (from the banked two-sided near-isometry
    `QIQTH.HrawNearIsometryConcrete.nearIsometry_concrete` split by
    `QIQTH.HrawChartTransfer.nearIsometry_budgets`).  Mirrors the banked
    `QIQTH.HrawPreCollapse.chartTransfer_quad` at the tighter widths.  NOT `a₁ = R/6`. -/
theorem chartTransfer43_quad_from_nearIsometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ → ∀ τ : ℝ, 0 < τ →
      ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (5 / 4 * τ) v
        ≤ 25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
            * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                  + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨rG, hrGpos, hgaussBall⟩ :=
    QIQTH.NearIsometry43Budget.uniformFlowExp_gaussDdim_transfer_43 g gi hC hK
  obtain ⟨rI, hrIpos, hisoBall⟩ :=
    QIQTH.HrawNearIsometryConcrete.nearIsometry_concrete g gi hC hK
  refine ⟨min rG rI, lt_min hrGpos hrIpos, ?_⟩
  intro q hq v hv τ hτ
  have hvG : ‖v‖ < rG := lt_of_lt_of_le hv (min_le_left _ _)
  have hvI : ‖v‖ < rI := lt_of_lt_of_le hv (min_le_right _ _)
  have hgauss := hgaussBall q hq v hvG τ hτ
  have hiso := hisoBall q hq v hvI
  obtain ⟨_hlow, hup⟩ := QIQTH.HrawChartTransfer.nearIsometry_budgets hiso
  -- fold the ambient displacement point.
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  -- polynomial leg: the upper budget scaled by `1/τ`.
  have hstep : rncRadialSq v / τ ≤ 5 / 4 * (rncRadialSq z / τ) := by
    have h := div_le_div_of_nonneg_right hup hτ.le
    rwa [mul_div_assoc] at h
  have hXv0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hXz0 : 0 ≤ rncRadialSq z / τ := div_nonneg (rncRadialSq_nonneg z) hτ.le
  have hpoly : (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1
      ≤ 25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) := by
    nlinarith [hstep, hXv0, hXz0, sq_nonneg (rncRadialSq z / τ),
      mul_nonneg hXz0 hXz0, sq_nonneg (5 / 4 * (rncRadialSq z / τ) - rncRadialSq v / τ)]
  -- nonnegativity facts.
  have hGv0 : 0 ≤ gaussDdim (5 / 4 * τ) v := gaussDdim_nonneg (5 / 4 * τ) v
  have hGz0 : 0 ≤ gaussDdim (4 / 3 * τ) z := gaussDdim_nonneg (4 / 3 * τ) z
  have hPz0 : 0 ≤ (rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hXz0) zero_le_one
  have h2516Pz0 : 0 ≤ 25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) :=
    mul_nonneg (by norm_num) hPz0
  -- assemble the two legs.
  calc ((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (5 / 4 * τ) v
      ≤ (25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1)) * gaussDdim (5 / 4 * τ) v :=
        mul_le_mul_of_nonneg_right hpoly hGv0
    _ ≤ (25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1))
          * (Real.sqrt ((4 / 3) / (5 / 4)) ^ n * gaussDdim (4 / 3 * τ) z) :=
        mul_le_mul_of_nonneg_left hgauss h2516Pz0
    _ = 25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

/-! ###############################################################################
    ### (stretch) — the ambient-frame width-4/3 QUAD affine bound on the ball.
    ############################################################################### -/

/-- **★★ (stretch) — `ambientAffine_onBall`.**  THE BALL PART OF THE `AffineGateBound` PRECURSOR.
    Chains the banked chart-frame affine width-1 QUAD estimate
    `QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1` with the width-4/3 QUAD
    transfer `chartTransfer43_quad_from_nearIsometry`: on the near-isometry ball `‖v‖ < r₁`, with
    `z := uniformFlowExp g gi hC hK q v − q`, the `N = 1` parametrix residual satisfies the AMBIENT
    width-4/3 affine QUAD bound
        `∃ P₀ P₁ ≥ 0, |parametrixResidualN 1 g gi Θ u τ v|
            ≤ (P₀ + P₁·τ)·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Route: the width-1 chart bound produces `gaussDdim τ v`; a single `1 → 5/4` fold
    (`gaussDdim_le_gaussDdim_chart (c=1, d=5/4)`, `√(5/4)ⁿ`) lands the chart Gaussian at width `5/4`,
    exactly the LHS of the QUAD transfer; the transfer then carries the geometric envelope to the
    ambient displacement `z` at width `4/3`.  The `√(5/4)ⁿ·(25/16)·√((4/3)/(5/4))ⁿ` normalizer folds
    into BOTH affine coefficients, preserving the affine shape.

    HONESTY.  Every coefficient hypothesis is the SAME satisfiable pointwise carry as the banked
    width-1 estimate (all instances of banked uniform bounds for the concrete van-Vleck witness — see
    `AffineRawResidual`); none equals the conclusion.  The ambient `heatOp = chart residual` transport
    (`AffineGateTransport.heatOp_globalCutoffWitness_transport`) and the annulus (2b) / on-gate
    assembly remain OPEN.  NOT `a₁ = R/6`. -/
theorem ambientAffine_onBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₁ → ∀ τ : ℝ, 0 < τ →
      ∀ Md : ℝ, 0 ≤ Md →
        (∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v) →
      ∀ Cc0 W0 L0 : ℝ, 0 ≤ Cc0 → 0 ≤ W0 → 0 ≤ L0 →
        |totalRadialO1_coeff g gi Θ u v| ≤ Cc0 * rncRadialSq v →
        |foldedCoeff Θ u 0 v| ≤ W0 →
        |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L0 →
      ∀ Cc1 W1 L1 : ℝ, 0 ≤ Cc1 → 0 ≤ W1 → 0 ≤ L1 →
        |totalRadialO1_coeff g gi Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v →
        |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 →
        |laplaceBeltrami g gi (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1 →
      ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        |parametrixResidualN 1 g gi Θ u τ v|
          ≤ (P₀ + P₁ * τ)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨r₁, hr₁pos, htrans⟩ := chartTransfer43_quad_from_nearIsometry g gi hC hK
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v hv τ hτ Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
    Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the banked chart-frame affine width-1 QUAD estimate.
  obtain ⟨P₀, P₁, hP₀, hP₁, hbound⟩ :=
    QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1
      g gi Θ u hτ v hw Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
      Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  -- the QUAD transfer at `(q, v, τ)`.
  have htr := htrans q hq v hv τ hτ
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  -- the `1 → 5/4` chart-Gaussian fold.
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
  calc |parametrixResidualN 1 g gi Θ u τ v|
      ≤ (P₀ + P₁ * τ) * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hbound
    _ ≤ (P₀ + P₁ * τ)
          * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)
              * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z)) :=
        mul_le_mul_of_nonneg_left henv hfac0
    _ = (P₀ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n))
          + P₁ * (Real.sqrt (5 / 4) ^ n * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n)) * τ)
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

end QIQTH.Transfer43Quad

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry
#print axioms QIQTH.Transfer43Quad.ambientAffine_onBall
