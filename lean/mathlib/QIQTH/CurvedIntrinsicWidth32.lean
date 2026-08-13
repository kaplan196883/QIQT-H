/-
  CurvedIntrinsicWidth32 — J4-672 (brick 1 of the curved width-3/2 near-diagonal domination campaign).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WIDTH-PARAMETRICITY SCOPING (the finding this brick lands).

  The banked curved provider `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` (J4-536) delivers only a
  WIDTH-2 ambient Gaussian defect bound
      `|heatOp g^K gi^K (vanVleckGatedWitness …) τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`
  (= `gaussDdim (2τ) (p−q)`), and width-2 does NOT imply the width-3/2 `hEdom` the labelled capstone
  consumes (near the diagonal the narrower 3/2-Gaussian is LARGER, so neither dominates the other).

  ★ KEY: the width-2 in that package is NOT intrinsic — it is a CHART-TRANSFER ARTIFACT.  The deepest
  producer in the chain, `HeatResidualBound.cutoffResidualN1_uniformFlow_narrow_mixed_below_lin`
  (CoeffU1Fix.lean:562), proves the per-`q` PULLBACK-FRAME defect bound at WIDTH 3/2:
      `|χ·∂_τ P − Δ_{g_q}(χ·P) | (v) ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`
  (its conclusion literally reads `gaussDdim (3 / 2 * τ) v`).  The ambient width 2 arises only when
  `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_of_good_CONST` transfers this intrinsic bound
  through the near-isometry chart with the displacement expansion factor `rncRadialSq (φ_q v − q) ≤
  (3/2)·rncRadialSq v` (with prefactor `Sc = √(2/(3/2))ⁿ = √(4/3)ⁿ`): intrinsic-3/2 × displacement-4/3
  = ambient-2.  Because the displacement factor → 1 as the gate radius → 0 (near-isometry), the AMBIENT
  width is tunable DOWN toward the intrinsic floor 3/2 by shrinking the radius; it cannot go BELOW 3/2
  through the pure-Gaussian route (a strictly-narrower target such as the width-4/3 `hgate` needs the
  QUADRATIC parametrix prefactor `((r²/τ)²+r²/τ+1)`, which absorbs an exponential the pure Gaussian
  cannot — width-4/3-quadratic is strictly stronger than width-3/2-pure).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE (brick 1).

    • `curvedRNC_intrinsic_width32_defect` — ★★ the CURVED intrinsic (pullback-frame) width-3/2 per-`q`
      defect domination, for the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`,
      `Ric(0) = (n−1)κδ ≠ 0`), on the seed `K = {0}`.  This is `cutoffResidualN1_uniformFlow_narrow_
      mixed_below_lin` RE-RUN at `g = curvedRNCMetric κ`, with the two amplitude-coefficient bounds
      discharged EXACTLY as in the flat/curved width-2 package (`hCoeffU0_vanVleck` +
      `uniformCoeffLinear_bound`) and the geometry/gauge/nondegeneracy members supplied by the banked
      curved bundle (`curvedRNCMetric_contDiff`/`_symm`/`_hinvF`/`_zero`/`_pd_zero`, `det g^K > 0`).
      It EXPOSES the width-3/2 intrinsic floor for the curved witness — the mathematically load-bearing
      first step of the width-3/2 campaign — with NO new geometry.
    • `curvedRNC_intrinsic_width32_defect_curved_satisfiable` — the SATISFIABILITY GATE re-export
      (`Ric(0) ≠ 0` at `κ ≠ 0`, `n ≥ 2`): the width-3/2 intrinsic bound is inhabited by a GENUINELY
      curved metric, NOT the flat `δ`.  Non-vacuous.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and it is **NOT** the ambient constGate width-3/2
  `hEdom` the capstone consumes.  It lands ONLY the INTRINSIC (pullback-frame) width-3/2 defect bound
  and the scoping verdict that the ambient width-2 is a transfer artifact whose displacement factor is
  tunable toward the intrinsic floor 3/2.  Turning this into the ambient constGate width-3/2 still
  requires a WIDTH-PARAMETRIC variant of `gatedWitnessN1_hEboundW_le_of_good_CONST` (currently pinned to
  the ambient width 2 / displacement 3/2) fed a shrunk-radius near-isometry displacement `rncRadialSq
  (φ_q v − q) ≤ (1+δ)·rncRadialSq v` — the precise remaining blocker (see the report).  No `sorry`, no
  new axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.GaussGaugeToHgauge
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ConstRadiusGateExport
open QIQTH.GaussianWidthTolerant QIQTH.A1R6CoreAtGate QIQTH.LaplaceBeltrami
open scoped BigOperators

namespace QIQTH.CurvedIntrinsicWidth32

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ J4-672 (brick 1) — `curvedRNC_intrinsic_width32_defect`.**  THE CURVED INTRINSIC (pullback-frame)
    WIDTH-3/2 per-`q` heat-parametrix DEFECT domination, for the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ < 0`), on the seed `K = {0}` (the RNC centre).  Given ONLY the mainline
    Christoffel smoothness `hChr`, the amplitude-smoothness carry `hw`, and any positive outer radius
    `ρc`, there are gate parameters `0 < a < b < ρc` and constants `B₀, B₁ ≥ 0` such that, for the
    order-1 van-Vleck parametrix `P = heatParametrix 1 (vanVleck g^K) (transportCoeff …)`, the cutoff
    defect against the uniform-flow pullback metric obeys the WIDTH-3/2 Gaussian bound
        `|χ·∂_τ P − Δ_{g_q}(χ·P)| (v) ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`   (∀ τ>0, ∀ q ∈ {0}, ∀ v).

    This is `HeatResidualBound.cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` RE-RUN at the curved
    metric: the two amplitude-coefficient bounds are discharged by `hCoeffU0_vanVleck` +
    `uniformCoeffLinear_bound` (the O(r²) and O(r) coefficient bounds), and the geometry/gauge/
    nondegeneracy inputs are the banked curved members (`curvedRNCMetric_contDiff`, `_symm`, `_hinvF`,
    `_zero`, `_pd_zero`, and `det g^K > 0` for `hgnd`).  It EXPOSES the width-3/2 intrinsic floor: the
    width-2 of the banked ambient package `curvedRNC_heatOp_dom_pkg` is a chart-transfer artifact, not an
    intrinsic ceiling.  ⚠ NOT `a₁ = R/6`; NOT the ambient constGate width-3/2 `hEdom`. -/
theorem curvedRNC_intrinsic_width32_defect
    (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B₀ B₁ : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ v : Point n,
        |radialCutoff a b v
              * deriv (fun s => heatParametrix 1 (vanVleck (curvedRNCMetric κ))
                  (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
                    (curvedRNCMetric κ) (curvedRNCInv κ))) s v) τ
            - laplaceBeltrami
                (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) q)
                (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) q)
                (fun y => radialCutoff a b y
                  * heatParametrix 1 (vanVleck (curvedRNCMetric κ))
                      (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
                        (curvedRNCMetric κ) (curvedRNCInv κ))) τ y) v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by
  classical
  -- ── the geometry / gauge members for `g^K` (all banked, exactly as in `curvedRNC_heatOp_dom_pkg`).
  have hg : ∀ (a b : Fin n), ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgsymm : ∀ (y : Point n) a b, curvedRNCMetric κ y a b = curvedRNCMetric κ y b a :=
    fun y a b => curvedRNCMetric_symm κ y a b
  have hinvF : ∀ (y : Point n) a b,
      (∑ σ, curvedRNCMetric κ y a σ * curvedRNCInv κ y σ b) = if a = b then (1 : ℝ) else 0 :=
    fun y a b => curvedRNCMetric_hinvF κ hκ.le y a b
  have hg0 : ∀ i j, curvedRNCMetric κ (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => curvedRNCMetric_zero κ i j
  have hdg0 : ∀ a b e, pd (fun y => curvedRNCMetric κ y a b) e (0 : Point n) = 0 :=
    fun a b e => curvedRNCMetric_pd_zero κ a b e
  -- ── nondegeneracy `hgnd` from `det g^K > 0` (`κ ≤ 0`).
  have hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => curvedRNCMetric κ y a b)) := by
    intro y
    rw [isUnit_matToCLM_iff (fun a b => curvedRNCMetric κ y a b), Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (curvedRNCMetric_det_pos κ hκ.le y).ne'
  -- ── the singleton-seed frame condition (`g^K = δ` at the RNC centre `0`).
  have hframeK : ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ i j,
      curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0) := by
    intro q hq i j
    rw [Set.mem_singleton_iff.mp hq]; exact hg0 i j
  -- ── the two amplitude-coefficient bounds (as in the width-2 package).
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ))
      (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric κ))
      (fun j => transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
        (curvedRNCMetric κ) (curvedRNCInv κ)) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  -- ── the width-3/2 intrinsic defect bound, RE-RUN at the curved metric.
  exact cutoffResidualN1_uniformFlow_narrow_mixed_below_lin (curvedRNCMetric κ) (curvedRNCInv κ)
    hg hChr (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    hgnd hgsymm hinvF hframeK
    (vanVleck (curvedRNCMetric κ))
    (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
      (curvedRNCMetric κ) (curvedRNCInv κ)))
    hw ρ_c C0 C1 hρc0 hC0 hC1
    (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
    (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
    ρc hρc

/-- **★ J4-672 (satisfiability gate) — CURVED, NOT SECRETLY FLAT.**  The witness `g^K` underlying the
    intrinsic width-3/2 defect domination is genuinely curved: for `κ ≠ 0` and `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) is nonzero.  So the width-3/2 intrinsic bound is inhabited by a
    genuinely curved metric (`κ < 0` ⊂ `κ ≠ 0`), NOT the flat `δ`.  Non-vacuous.  NOT `a₁ = R/6`. -/
theorem curvedRNC_intrinsic_width32_defect_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedIntrinsicWidth32

section AxiomChecks
open QIQTH.CurvedIntrinsicWidth32
#print axioms curvedRNC_intrinsic_width32_defect
#print axioms curvedRNC_intrinsic_width32_defect_curved_satisfiable
end AxiomChecks
