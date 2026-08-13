/-
  WhiteChartC5 — J4-664: ★ THE CHART WELD (J5-6).  Discharges the chart-C⁵ residue `hch5`
  — the SOLE remaining hypothesis of the k=1 curved t²-budget `white_K1BudgetW_final` — from
  the just-landed unconditional `ExpMap.expMap_contDiffOn_five`, and instantiates the K1
  capstone UNCONDITIONALLY.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ WHAT LANDS.
  (1) `uniformFlowExp_contDiffAt_five` (namespace `QIQTH.ExpMap`) — the C⁵ FORWARD MAP at
      reachable points, the faithful one-Fréchet-order-up mirror of the banked
      `ChartThirdJet.uniformFlowExp_contDiffAt_four`: the `exp∈C⁵` tower
      `expMap_contDiffOn_five` gives `ContDiffAt ℝ 5 (expMap g gi hC z) v` on the injectivity
      ball; the overlap bridge `expMap_eq_uniformFlowExp_on_overlap` gives
      `uniformFlowExp z =ᶠ[𝓝 v] expMap z`; transfer via `ContDiffAt.congr_of_eventuallyEq`.
  (2) `white_chartC5_discharged` — the residue `hch5` PRODUCED at the curved whitened chart:
      the exact Prop binder of `white_K1BudgetW_final`, instantiated from (1) at
      `(curvedRNCMetric κ, curvedRNCInv κ, curvedRNC_hChr κ hκ, hKc, q)`.
  (3) ★ `white_K1BudgetW_unconditional` — the k=1 curved t²-budget with the `hch5` binder
      GONE (only the generic `w ≥ 2` and `H`-side comparison data remain).
  (4) ★ `white_K1BudgetW_unconditional_curvedWitness` — the UNCONDITIONAL, ANTECEDENT-FREE
      k=1 budget at the GENUINELY CURVED witness (`n = 2`, `κ = −1`, fat `K = closedBall 0 2`,
      off-centre row `q = (1,1)`), with the concrete Gaussian `H`-witness discharged too.

  ⚠ HONEST SCOPE (binding).
    • This lands the k=1 curved t²-budget UNCONDITIONALLY — NOT the full `a₁ = R/6`.  The
      curved side still owes: the Duhamel-split integrability carry, the fat-`K` carrier piles,
      the capstone co-instantiation at the corrected witness, and the prior analytic piles.
      The diagonal `R/6` remains a labelled CARRIER value (`whiteU1(0) = R/6`), NOT derived.
    • The weld is a one-brick mirror: `expMap_contDiffOn_five` is ball-local, the overlap
      bridge is exactly the C⁴ bridge, so NO boundary/uniformity gap arises.
  No axioms, no `sorry`, no `:= True`.
-/
import QIQTH.WhiteF1Reg
import QIQTH.ExpMapContDiffFive

open Filter Topology

namespace QIQTH.ExpMap

open QIQTH.Curvature

variable {n : ℕ}

/-- **★ `uniformFlowExp_contDiffAt_five` — the C⁵ FORWARD MAP at reachable points.**  The flow
    exponential `φ_z := uniformFlowExp g gi hC hK z` is `ContDiffAt ℝ 5` at every reachable field
    point `v` with `‖v‖ < expRho g gi hC z` and `‖v‖ < uniformFlowRadius g gi hC hK`.  The faithful
    one-Fréchet-order-up mirror of the banked `ChartThirdJet.uniformFlowExp_contDiffAt_four`:
    the `exp∈C⁵` tower `expMap_contDiffOn_five` gives `ContDiffAt ℝ 5 (expMap g gi hC z) v` (open
    injectivity ball ∈ `𝓝 v`); the overlap bridge `expMap_eq_uniformFlowExp_on_overlap` gives
    `uniformFlowExp z =ᶠ[𝓝 v] expMap z`; transfer via `ContDiffAt.congr_of_eventuallyEq`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_contDiffAt_five (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) (v : Point n)
    (hvexp : ‖v‖ < expRho g gi hC z) (hvuf : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 5 (uniformFlowExp g gi hC hK z) v := by
  -- `expMap z` is `C⁵` at `v` (open injectivity ball is a neighbourhood of `v`).
  have hexp5 : ContDiffAt ℝ 5 (expMap g gi hC z) v :=
    (expMap_contDiffOn_five g gi hC z).contDiffAt
      (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hvexp))
  -- `uniformFlowExp z =ᶠ[𝓝 v] expMap z` on the overlap ball.
  have hmin : ‖v‖ < min (expRho g gi hC z) (uniformFlowRadius g gi hC hK) := lt_min hvexp hvuf
  have hnhds : Metric.ball (0 : Point n) (min (expRho g gi hC z) (uniformFlowRadius g gi hC hK))
      ∈ 𝓝 v :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hmin)
  have heq : uniformFlowExp g gi hC hK z =ᶠ[𝓝 v] expMap g gi hC z := by
    filter_upwards [hnhds] with w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (expMap_eq_uniformFlowExp_on_overlap g gi hC hK z hz w hw).symm
  exact hexp5.congr_of_eventuallyEq heq

end QIQTH.ExpMap

namespace QIQTH.WhiteChartC5

open QIQTH.Curvature QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef QIQTH.CurvedA1CenterAmp
open QIQTH.CurvedRNCGaugeBundle QIQTH.FlatHeatEquation QIQTH.WhiteCapstoneWire
open QIQTH.WhiteWitness QIQTH.WhiteF1 QIQTH.WhiteF1Reg

variable {n : ℕ}

/-- **★ `white_chartC5_discharged` — the chart-C⁵ residue `hch5` PRODUCED.**  The exact Prop
    binder of `white_K1BudgetW_final`: for every reachable `v` (below the injectivity radius
    `expRho` and the K-uniform-flow radius), the whitened uniform-flow chart is `ContDiffAt ℝ 5`.
    Direct instantiation of the C⁵ forward map `ExpMap.uniformFlowExp_contDiffAt_five` at the
    curved base data `(curvedRNCMetric κ, curvedRNCInv κ, curvedRNC_hChr κ hκ, hKc, q)`, with the
    row-membership `hq : q ∈ Kset` supplying the base-point hypothesis.  NOT `a₁ = R/6`. -/
theorem white_chartC5_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v :=
  fun v hvexp hvuf =>
    uniformFlowExp_contDiffAt_five (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q hq v hvexp hvuf

/-- **★★★ `white_K1BudgetW_unconditional` — the k=1 curved t²-budget, `hch5` DISCHARGED.**  The
    corrected h0h1-free K1 budget `white_K1BudgetW_final` with its SOLE residue — the chart-C⁵
    (Jet-5) rung — supplied internally by `white_chartC5_discharged` (⟸ the unconditional
    `expMap_contDiffOn_five`).  The only remaining binders are the generic budget-shape data
    (`w ≥ 2` and the `H`-side comparison bound), NOT regularity residues.  ⚠ NOT `a₁ = R/6`:
    the curved side still owes the Duhamel carry + fat-`K` carriers + capstone co-instantiation;
    `R/6` stays a labelled carrier. -/
theorem white_K1BudgetW_unconditional (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : ℝ) (hw2 : 2 ≤ w) :
    ∃ rF > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rF →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1' κ hκ hKc q r₀) :=
  white_K1BudgetW_final κ hκ hKc q hq w hw2 (white_chartC5_discharged κ hκ hKc q hq)

/-- **★★★ `white_K1BudgetW_unconditional_curvedWitness` — the ANTECEDENT-FREE k=1 budget at the
    GENUINELY CURVED witness.**  `n = 2`, `κ = −1`, fat `K = closedBall 0 2`, off-centre row
    `q = (1,1)` (‖q‖ = 1 ≠ 0, so NOT the degenerate `K = {0}` cp466 trap — the antecedents are
    genuinely inhabited).  Both the chart-C⁵ residue (via `white_chartC5_discharged`) and the
    concrete Gaussian `H`-witness (via `white_K1BudgetW_final_concreteH`) are discharged, leaving
    ZERO hypotheses.  The k=1 curved t²-budget is now UNCONDITIONAL at a curved witness.
    ⚠ NOT `a₁ = R/6` (the diagonal `R/6` remains a labelled carrier). -/
theorem white_K1BudgetW_unconditional_curvedWitness :
    ∃ rF > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rF →
      K1TransportBudgetW 8 (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ))
        (whiteDefect1' (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2)
          (fun _ => 1) r₀) := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  exact white_K1BudgetW_final_concreteH (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
    (white_chartC5_discharged (-1) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq)

end QIQTH.WhiteChartC5

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.ExpMap.uniformFlowExp_contDiffAt_five
#print axioms QIQTH.WhiteChartC5.white_chartC5_discharged
#print axioms QIQTH.WhiteChartC5.white_K1BudgetW_unconditional
#print axioms QIQTH.WhiteChartC5.white_K1BudgetW_unconditional_curvedWitness
