/-
  AffineGateTransport — J4-370: the AffineGateBound closure, steps (1)+(2) of 3 (Sol brick map).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / TRANSPORT-WIRING brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It
  takes the banked RAW AFFINE `N = 1` graded quadratic residual estimate at width `1`
  (`AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1`) and folds it to width `4/3` (brick
  (1)), and it PROMOTES the on-gate transport identity buried inside the compiled capstone
  `HeatResidualBound.gatedWitnessN1_hEboundW_le_lin` (its pre-line-871 slice) to a standalone lemma
  (brick (2a)).  Both bricks feed the still-OPEN consumer predicate
  `HgateAffineRepair.AffineGateBound` — but the ambient-frame `v → (p−q)` transfer (brick (3)) and the
  width-`≤ 4/3` cutoff-annulus assembly (brick (2b/2c)) remain OPEN.  NO `sorry` (header prose
  excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or
  trivially yielding) the conclusion, NO existing file edited, nothing committed.  `a₁ = R/6` stays
  CONDITIONAL on the whole convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WIDTH BOOKKEEPING (Sol #15).  The target `AffineGateBound` carries width `4/3`, and `4/3 < 3/2`
  — a `3/2`-width bound (the banked `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` /
  `gatedWitnessN1_hEboundW_le_lin`) can NEVER be narrowed to `4/3` by polynomial factors.  The honest
  route therefore rebuilds from the PRE-ABSORPTION width-`1` graded residual (`rawResidualN1_affine_*
  _width1`, which keeps the `(x²+x+1)` polynomial EXPLICIT rather than absorbing it into a `3/2`
  constant) and folds `1 → 4/3` via the normalized comparison `gaussDdim_le_gaussDdim_chart (c=1,
  d=4/3)`.

  ## DELIVERABLES.
  •  (1) `rawResidualN1_affine_graded_quadPoly_width43` — the trivial `1 → 4/3` affine fold of the raw
     affine `N = 1` graded quadratic estimate.  Same `∃ P₀ P₁ ≥ 0` affine shape, at width `4/3`.
  •  (2a) `heatOp_globalCutoffWitness_transport` — the ON-GATE TRANSPORT IDENTITY (verbatim from the
     `htransport` block of `gatedWitnessN1_hEboundW_le_lin`, lines 853-868): for the (un-gated)
     `globalCutoffParametrixWitnessN 1` witness at the ambient point `uniformFlowExp q v`, `heatOp`
     equals the chart-frame cutoff residual, GIVEN the two honest germ facts
     (`hpt`: chart inverse, `hlap`: laplaceBeltrami naturality) that the compiled capstone discharges.

  ## HONESTY / SATISFIABILITY.  Brick (1)'s hypotheses are the SAME pointwise coefficient carries as the
  banked width-`1` estimate (all satisfiable for the concrete van-Vleck witness — see
  `AffineRawResidual`).  Brick (2a)'s two hypotheses `hpt` / `hlap` are SATISFIABLE (both are discharged
  INSIDE `gatedWitnessN1_hEboundW_le_lin` — `hpt` at line 831-832 via the chart germ `hgerm.eq_of_nhds`,
  `hlap` at lines 840-852 via `laplaceBeltrami_uniformFlow_naturality_forall_f` +
  `laplaceBeltrami_congr_nhds`), non-vacuous, and NEITHER equals the conclusion (`hlap` is only the
  laplaceBeltrami term; the conclusion is the full `heatOp = deriv − laplaceBeltrami` identity).  NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AffineRawResidual
import QIQTH.CoeffU1Fix

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.AffineGateTransport

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) — the trivial `1 → 4/3` affine fold.
    ############################################################################### -/

/-- **★ (1) — `rawResidualN1_affine_graded_quadPoly_width43`.**  THE `1 → 4/3` AFFINE FOLD.  Applies the
    normalized width comparison `gaussDdim τ v ≤ √(4/3)ⁿ·gaussDdim ((4/3)·τ) v`
    (`gaussDdim_le_gaussDdim_chart`, `c = 1 < d = 4/3`, `w = v` — the SAME step the banked `N = 0`
    `rawResidualN0_graded_quadPoly_width43` uses) to the banked raw affine `N = 1` graded quadratic
    estimate at width `1`.  The affine factor `(P₀ + P₁·τ)` passes through by `mul_le_mul` on the nonneg
    quadratic polynomial, and the normalizing `√(4/3)ⁿ` is folded into BOTH affine coefficients
    (`P₀' = √(4/3)ⁿ·P₀`, `P₁' = √(4/3)ⁿ·P₁`), preserving the affine shape:
        `∃ P₀ P₁ ≥ 0, |parametrixResidualN 1 g gi Θ u τ v|
           ≤ (P₀ + P₁·τ)·((x²+x+1)·gaussDdim ((4/3)·τ) v)`,   `x = rncRadialSq v/τ`.
    This is the inner shape of `HgateAffineRepair.AffineGateBound` at the target width `4/3` (chart
    frame; the ambient `v → (p−q)` transfer is brick (3)).  NOT `a₁ = R/6`. -/
theorem rawResidualN1_affine_graded_quadPoly_width43
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (v : Point n)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (Md : ℝ) (hMd : 0 ≤ Md)
    (hdev : ∀ i j : Fin n, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v)
    (Cc0 W0 L0 : ℝ) (hCc0 : 0 ≤ Cc0) (hW0 : 0 ≤ W0) (hL0 : 0 ≤ L0)
    (hcoeff0 : |totalRadialO1_coeff g gi Θ u v| ≤ Cc0 * rncRadialSq v)
    (hw0bd : |foldedCoeff Θ u 0 v| ≤ W0)
    (hlap0 : |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L0)
    (Cc1 W1 L1 : ℝ) (hCc1 : 0 ≤ Cc1) (hW1 : 0 ≤ W1) (hL1 : 0 ≤ L1)
    (hcoeff1 : |totalRadialO1_coeff g gi Θ (fun j => u (j + 1)) v| ≤ Cc1 * rncRadial v)
    (hw1bd : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1)
    (hlap1 : |laplaceBeltrami g gi (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1) :
    ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      |parametrixResidualN 1 g gi Θ u τ v|
        ≤ (P₀ + P₁ * τ)
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (4 / 3 * τ) v) := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hbound⟩ :=
    QIQTH.AffineRawResidual.rawResidualN1_affine_graded_quadPoly_width1
      g gi Θ u hτ v hw Md hMd hdev Cc0 W0 L0 hCc0 hW0 hL0 hcoeff0 hw0bd hlap0
      Cc1 W1 L1 hCc1 hW1 hL1 hcoeff1 hw1bd hlap1
  refine ⟨Real.sqrt (4 / 3) ^ n * P₀, Real.sqrt (4 / 3) ^ n * P₁,
    mul_nonneg (by positivity) hP₀, mul_nonneg (by positivity) hP₁, ?_⟩
  have hxr : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hpoly0 : 0 ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hxr) zero_le_one
  have hfac0 : 0 ≤ P₀ + P₁ * τ := add_nonneg hP₀ (mul_nonneg hP₁ hτ.le)
  have hwidth : gaussDdim τ v ≤ Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) v := by
    have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 4 / 3)
      (by norm_num) (by norm_num) hτ (v := v) (w := v)
      (by have := rncRadialSq_nonneg v; linarith)
    simpa using h
  calc |parametrixResidualN 1 g gi Θ u τ v|
      ≤ (P₀ + P₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hbound
    _ ≤ (P₀ + P₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1)
              * (Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) v)) := by
        apply mul_le_mul_of_nonneg_left _ hfac0
        exact mul_le_mul_of_nonneg_left hwidth hpoly0
    _ = (Real.sqrt (4 / 3) ^ n * P₀ + Real.sqrt (4 / 3) ^ n * P₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (4 / 3 * τ) v) := by
        ring

/-! ###############################################################################
    ### (2a) — the on-gate transport identity (verbatim promotion).
    ############################################################################### -/

/-- **★★ (2a) — `heatOp_globalCutoffWitness_transport`.**  THE ON-GATE TRANSPORT IDENTITY (VERBATIM
    from the `htransport` block of `HeatResidualBound.gatedWitnessN1_hEboundW_le_lin`, lines 853-868).
    For the (un-gated) `globalCutoffParametrixWitnessN 1 Θ u a b W` witness evaluated at the AMBIENT
    point `uniformFlowExp g gi hC hK q v` (chart source `v`, base `q`), the heat operator `heatOp`
    EQUALS the chart-frame cutoff residual
        `radialCutoff a b v · ∂_τ(heatParametrix 1 Θ u · v)
           − Δ_{g̃_q}(radialCutoff a b · heatParametrix 1 Θ u τ ·) v`,
    GIVEN the two germ facts the compiled capstone discharges:
    •  `hpt`   : `W q (uniformFlowExp q v) = v`  — the chart-inverse property (discharged via
       `hgerm.eq_of_nhds`);
    •  `hlap`  : the laplaceBeltrami NATURALITY identity (discharged via
       `laplaceBeltrami_uniformFlow_naturality_forall_f` + `laplaceBeltrami_congr_nhds`).
    Route: `simp only [heatOp]` splits into the `∂_τ` and `Δ` terms; the `∂_τ` term is pointwise the
    `radialCutoff a b v`-scaled parametrix time-derivative (`hpt` + `deriv_const_mul_field`); the `Δ`
    term is `hlap`.  Both hypotheses are SATISFIABLE, non-vacuous, and NEITHER equals the conclusion.
    NOT `a₁ = R/6`. -/
theorem heatOp_globalCutoffWitness_transport
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (W : Point n → Point n → Point n) {τ : ℝ} (q v : Point n)
    (hpt : W q (uniformFlowExp g gi hC hK q v) = v)
    (hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitnessN 1 Θ u a b W τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v) :
    heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b W) τ
        (uniformFlowExp g gi hC hK q v) q
      = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
        - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
  simp only [heatOp]
  have hterm1fun :
      (fun s => globalCutoffParametrixWitnessN 1 Θ u a b W s
          (uniformFlowExp g gi hC hK q v) q)
        = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
    funext s
    simp only [globalCutoffParametrixWitnessN, hpt]
  rw [hterm1fun, deriv_const_mul_field, hlap]

end QIQTH.AffineGateTransport

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AffineGateTransport.rawResidualN1_affine_graded_quadPoly_width43
#print axioms QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport
