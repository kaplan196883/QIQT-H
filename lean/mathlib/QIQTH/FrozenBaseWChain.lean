/-
  FrozenBaseWChain — J4-293: the FROZEN-BASE-`w` continuity chain (Gap-A's near region).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET (Gap-A, near region).  The Levi-continuity chain needs, for a.e. base `w`, the joint
  `(time,first-spatial)`-continuity of the concrete gated van-Vleck witness heat operator
      `E τ z w := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ z w`
  at the FIXED second (base) argument `w`.  The banked chain (J4-285/287/288:
  `ChartJetFactsDischarge.heatOpGatedWitness_jointContinuousOn_chartFree`) proves this for the base slice
  `w = 0` ONLY.

  THE SOL#7 ROUTE (this file).  FREEZE the base `w`.  The inverse chart at base `w`,
  `W w := uniformInverseChart g gi hC hK w`, is then a FIXED function of the field variable `z`; re-run
  the whole base-0 chain AT base `w`, co-centered at the chart CENTER (which is the point `w` itself,
  since `W w w = 0`).  No joint-in-`w` regularity is ever needed.  The J4-292 zero-collar machinery
  (`ZeroCollarLocalZero.heatOpGatedWitness_eq_zero_of_far`, which is ALREADY base-generic) supplies the
  off-support half.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE BASE-0-ANCHORING CENSUS (the load-bearing recon — what is base-parametric vs base-0-specific).

    • `uniformInverseChart_huniformChart`  — provides its germ+`C²` spec `∀ q ∈ K` (base-parametric).
    • `uniformFlowExp_zero q hq : φ_q 0 = q`  — proved `∀ base q ∈ K` (base-parametric).  ⟹ the CENTRE
      of `W w` is the POINT `w` (`W w w = 0`); the `C²` ball is `ball w ρc`, NOT `ball 0 ρc`.
    • `ChartJetBounds.chartField_contDiffAt_center` : `ContDiffAt ℝ 2 (W 0) 0`  — STATED at base 0, but
      its PROOF is literally base-parametric (it invokes the two ∀-base facts above at `q = 0`).  ⟹ F1
      below re-proves it `∀ w ∈ K` as `ContDiffAt ℝ 2 (W w) w`.
    • `AmplitudePackage.vanVleckGatedWitness_gate_apply`  — takes `{p q} (hq : q∈K) (hp : p∈S q)`: fully
      base-parametric.
    • `GlobalHunifAssembly.gatedKernel_heatOp_eq_of_mem_nhds`  — takes generic `q`, `hq : q∈K`,
      `hS : S q ∈ 𝓝 p`: fully base-parametric (⟹ the base-`w` gate transfer is a one-liner).
    • `ChartComposedHeatOp.chartComposed_pd_eq` / `_pd_pd_eq`  — the first/second chain-rule POINTWISE
      forms: GENERIC in `W₀ : Point n → Point n` (base-agnostic); reused verbatim here.
    • `ChartComposedHeatOp.chartComposed_pd_jointContinuousOn` … `chartComposedHeatOp_jointContinuousOn`
      (D1c–D5) and `ChartJetFactsDischarge.hWc*_of_contDiffOn_ball` (J2–J4) — GENERIC in `W₀`, but their
      DOMAIN is hardwired to `closedBall 0 R` (`chartLift`, `lift_snd` centred at `0`).  This is the ONLY
      base-0-specificity in the composition/discharge layer; it is re-proven co-centred at an ARBITRARY
      centre `c` below (§F3), reusing the domain-generic banked parametrix continuities
      (`heatParametrix_*_jointContinuousOn`, all on `{0<τ}`) and the banked pointwise chain rules.
    • The parametrix data `Θ* = vanVleck g`, `u* = transportCoeff (transportOp (vanVleck g) g gi)` are
      GLOBAL functions, base-independent — only the CHART is base-dependent.
    • `ZeroCollarLocalZero` (B1)`gatedWitness_eventuallyEq_zero_of_far` / (B2)`heatOpGatedWitness_eq_zero_of_far`
      / (C) — fully base-generic (generic `q`, generic `W`); reused verbatim.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (all axiom-free; NO `sorry` outside this header prose; NO `:= True`; none the conclusion).

    F1 — the centre facts at base `w` (the KEY census item, honestly generalized):
       • `chartField_contDiffAt_center_at` : `∀ w ∈ K, ContDiffAt ℝ 2 (W w) w`.
       • `chartField_contDiffOn_ball_at`    : `∃ ρc>0, ContDiffOn ℝ 2 (W w) (ball w ρc)`.

    F3 — the chart-composed continuity chain, RE-CENTRED at an arbitrary centre `c` (domain
         `Icc t₁ t₂ ×ˢ closedBall c R`), `W₀`-generic:
       • `chartComposed_pd_jointContinuousOn_at`, `chartComposed_pd_pd_jointContinuousOn_at`,
         `chartComposed_dtau_jointContinuousOn_at`, `chartComposed_laplaceBeltrami_jointContinuousOn_at`,
       • `chartComposedHeatOp_jointContinuousOn_at`  — `hBcont` on `closedBall c R` (the base-`w` `hBcont`
         is the `c = w`, `W₀ = W w` instance).

    F2 — the base-`w` on-gate reduction (mirror of GatedWitnessHeatOpBridge L2a/L2b/COMPOSED/L3 at base `w`,
         domain `closedBall w R`):
       • `heatOpWitness_eq_heatOp_cutoffChart_at`, `heatOp_cutoffChart_eq_chartParametrix_at`,
         `heatOpWitness_eq_chartParametrix_of_gate_cut_at`,
         `heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at`.

    F4 — the frozen-base-`w` capstones (co-centred at `w`):
       • `heatOpWitness_fixedBase_active_continuousOn`    — `E(·,·,w)` continuous on `closedBall w R`
         (active region), `hBcont` discharged via F3-at-`w`;
       • `heatOpWitness_fixedBase_active_chartFree`       — the same with the three chart facts INTERNAL
         (discharged from F1's `ball w ρc` `C²` region);
       • `heatOpWitness_fixedBase_continuousOn`           — the FULL near+off paste: `E(·,·,w)` continuous
         on `closedBall w R` (`R<ρc`) from the carried active-region continuity `hEA` + the honest collar
         carry `hoff` (off the active set, strictly far ⟹ off-support ZERO via J4-292).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry`, no `:= True`, no conclusion-as-hypothesis.  Every carried hypothesis
     is genuine and satisfiable (the chart facts from `W w`'s `C²` region on `ball w ρc`; the coefficient
     regularity from the van-Vleck/transport smoothness banks; `hEA` from the F3+F2 active capstone;
     `hoff` the collar geometry).  The frozen-base capstone is co-centred at `w` (`closedBall w R`); the
     reconciliation to a single origin-centred `closedBall 0 R` for a.e. `w` (a chart-ball COVER of the
     active compact) is the residual named in the report — NOT discharged here.  This file only RELOCATES
     the boundary-chain regularity onto the frozen base `w`; the curvature value is untouched.
     **NOT `a₁ = R/6`.**
-/
import Mathlib
import QIQTH.ChartComposedHeatOp
import QIQTH.ChartJetFactsDischarge
import QIQTH.ZeroCollarLocalZero
import QIQTH.ChartJetBounds

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.HeatParametrixOrder
open QIQTH.ParametrixPartsContinuity QIQTH.ParametrixSpatialPartials
open QIQTH.GatedWitnessHeatOpBridge
open QIQTH.ChartComposedHeatOp
open QIQTH.ChartJetFactsDischarge
open QIQTH.ZeroCollarLocalZero
open QIQTH.RadialDistance QIQTH.RNCDecay
open scoped Topology ContDiff

namespace QIQTH.FrozenBaseWChain

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (F1) — the centre facts at base `w` (the KEY census item).
    ############################################################################### -/

/-- **★ (F1) `chartField_contDiffAt_center_at`.**  The base-`w` field-slot inverse chart
    `W w = uniformInverseChart g gi hC hK w` is `C²` at its FIELD CENTRE — the point `w` itself
    (`W w w = 0`).  This is `ChartJetBounds.chartField_contDiffAt_center` re-proved `∀ w ∈ K`: the two
    ingredients — `uniformInverseChart_huniformChart` (spec `∀ q ∈ K`) and `uniformFlowExp_zero`
    (`φ_w 0 = w`, `∀ base w ∈ K`) — are BOTH base-parametric, so the base-0 proof is literally
    parametric in the base.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt_center_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {w : Point n} (hwK : w ∈ K) :
    ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w) w := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec w hwK
  obtain ⟨_, hC2⟩ := hgermC2 0 (by rw [norm_zero]; exact hδ₀)
  rwa [QIQTH.ExpMap.uniformFlowExp_zero g gi hC hK w hwK] at hC2

/-- **★ (F1, ball form) `chartField_contDiffOn_ball_at`.**  From the base-`w` centre `C²` (F1) extract an
    OPEN ball `ball w ρc` (`ρc>0`) on which `W w` is `ContDiffOn ℝ 2`.  `ContDiffAt.contDiffOn` +
    `Metric.mem_nhds_iff`.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffOn_ball_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {w : Point n} (hwK : w ∈ K) :
    ∃ ρc : ℝ, 0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) := by
  obtain ⟨u, hu_nhds, hu_cd⟩ :=
    (chartField_contDiffAt_center_at g gi hC hK hwK).contDiffOn
      (le_refl (2 : WithTop ℕ∞)) (by simp)
  obtain ⟨ρc, hρc, hball⟩ := Metric.mem_nhds_iff.mp hu_nhds
  exact ⟨ρc, hρc, hu_cd.mono hball⟩

/-! ###############################################################################
    ## (F3) — the chart-composed continuity chain, RE-CENTRED at an arbitrary centre `c`.
    ##  `W₀`-generic; the ONLY base-0-specificity in the banked chain (`closedBall 0` domain) removed.
    ############################################################################### -/

/-- **Centre-`c` chart continuity.**  Per-component `ContDiffAt ℝ 2` on `closedBall c R` gives
    `ContinuousOn W₀` there. -/
theorem chart_continuousOn_of_c2_at (W₀ : Point n → Point n) (c : Point n) (R : ℝ)
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z) :
    ContinuousOn W₀ (Metric.closedBall c R) :=
  fun z hz =>
    (differentiableAt_pi.mpr
      (fun a => (hWc2 z hz a).differentiableAt (by norm_num))).continuousAt.continuousWithinAt

/-- **Centre-`c` chart-lift continuity.**  `(τ,z) ↦ (τ, W₀ z)` is continuous on `Icc t₁ t₂ ×ˢ closedBall
    c R` from `ContinuousOn W₀` on the ball. -/
theorem chartLift_continuousOn_at (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ)
    (hWcont : ContinuousOn W₀ (Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n => ((p.1, W₀ p.2) : ℝ × Point n))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
  (continuous_fst.continuousOn).prodMk
    (hWcont.comp continuous_snd.continuousOn (fun _ hp => hp.2))

/-- **Centre-`c` chart-lift `MapsTo`.**  Sends the positive-time compact into `{0<τ}` (`0<t₁`);
    independent of the centre. -/
theorem chartLift_mapsTo_at (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) :
    Set.MapsTo (fun p : ℝ × Point n => ((p.1, W₀ p.2) : ℝ × Point n))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) {q : ℝ × Point n | 0 < q.1} :=
  fun _ hp => lt_of_lt_of_le ht₁ hp.1.1

/-- **★ (F3, D1c-at) `chartComposed_pd_jointContinuousOn_at`.**  Joint continuity of the chart-composed
    first partial on `Icc t₁ t₂ ×ˢ closedBall c R`.  Verbatim the banked D1c with the domain re-centred
    to `c`; reuses the banked POINTWISE chain rule `chartComposed_pd_eq` and the domain-generic banked
    `heatParametrix_pd_jointContinuousOn`.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_jointContinuousOn_at (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (i : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hWcont := chart_continuousOn_of_c2_at W₀ c R hWc2
  have hΦcont := chartLift_continuousOn_at W₀ c t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo_at W₀ c t₁ t₂ R ht₁
  have hbankPd : ∀ a, ContinuousOn
      (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) a (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
    intro a
    simpa [Function.comp] using
      (heatParametrix_pd_jointContinuousOn N Θ u a hw).comp hΦcont hΦmaps
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ a, pd (heatParametrix N Θ u p.1) a (W₀ p.2) * pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
    continuousOn_finsetSum _ (fun a _ => (hbankPd a).mul (hWc1cont a i))
  refine hClosed.congr (fun p hp => ?_)
  have hWz : DifferentiableAt ℝ W₀ p.2 :=
    differentiableAt_pi.mpr (fun a => (hWc2 p.2 hp.2 a).differentiableAt (by norm_num))
  exact chartComposed_pd_eq N Θ u W₀ hw p.1 i p.2 hWz

/-- **★ (F3, D2c-at) `chartComposed_pd_pd_jointContinuousOn_at`.**  Joint continuity of the chart-composed
    second partial on `Icc t₁ t₂ ×ˢ closedBall c R`.  Verbatim banked D2c, domain re-centred to `c`;
    reuses `chartComposed_pd_pd_eq`.  NOT `a₁ = R/6`. -/
theorem chartComposed_pd_pd_jointContinuousOn_at (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (i j : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hWcont := chart_continuousOn_of_c2_at W₀ c R hWc2
  have hΦcont := chartLift_continuousOn_at W₀ c t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo_at W₀ c t₁ t₂ R ht₁
  have hbankPd : ∀ a, ContinuousOn
      (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) a (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
    intro a
    simpa [Function.comp] using
      (heatParametrix_pd_jointContinuousOn N Θ u a hw).comp hΦcont hΦmaps
  have hbankPdPd : ∀ a b, ContinuousOn
      (fun p : ℝ × Point n => pd (fun w => pd (heatParametrix N Θ u p.1) a w) b (W₀ p.2))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
    intro a b
    simpa [Function.comp] using
      (heatParametrix_pd_pd_jointContinuousOn N Θ u b a hw).comp hΦcont hΦmaps
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        (∑ a, (∑ b, pd (fun w => pd (heatParametrix N Θ u p.1) a w) b (W₀ p.2)
                  * pd (fun y => W₀ y b) i p.2) * pd (fun y => W₀ y a) j p.2)
          + ∑ a, pd (heatParametrix N Θ u p.1) a (W₀ p.2)
                * pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
    refine (continuousOn_finsetSum _ (fun a _ => ?_)).add
      (continuousOn_finsetSum _ (fun a _ => (hbankPd a).mul (hWc2cont a i j)))
    exact (continuousOn_finsetSum _ (fun b _ => (hbankPdPd a b).mul (hWc1cont b i))).mul
      (hWc1cont a j)
  refine hClosed.congr (fun p hp => ?_)
  have hWc2z : ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) p.2 := fun a => hWc2 p.2 hp.2 a
  exact chartComposed_pd_pd_eq N Θ u W₀ hw p.1 i j p.2 hWc2z

/-- **★ (F3, D3-at) `chartComposed_dtau_jointContinuousOn_at`.**  The `∂_τ`-term joint continuity,
    domain re-centred to `c`.  The chart is `τ`-independent ⟹ the banked
    `heatParametrix_deriv_jointContinuousOn` composed with the chart lift.  NOT `a₁ = R/6`. -/
theorem chartComposed_dtau_jointContinuousOn_at (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z) :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hWcont := chart_continuousOn_of_c2_at W₀ c R hWc2
  have hΦcont := chartLift_continuousOn_at W₀ c t₁ t₂ R hWcont
  have hΦmaps := chartLift_mapsTo_at W₀ c t₁ t₂ R ht₁
  simpa [Function.comp] using
    (heatParametrix_deriv_jointContinuousOn N Θ u hΘc hΘne huc).comp hΦcont hΦmaps

/-- **★ (F3, D4-at) `chartComposed_laplaceBeltrami_jointContinuousOn_at`.**  The `Δ`-term joint continuity,
    domain re-centred to `c`.  Unfold `laplaceBeltrami`; assemble from `hgi`/`hChr` and the re-centred
    composed partials (D1c-at / D2c-at).  NOT `a₁ = R/6`. -/
theorem chartComposed_laplaceBeltrami_jointContinuousOn_at (N : ℕ)
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hEq : (fun p : ℝ × Point n =>
        laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi p.2 i j *
            (pd (fun y => pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) j y) i p.2
              - ∑ k, christoffel g gi k i j p.2
                  * pd (fun x => heatParametrix N Θ u p.1 (W₀ x)) k p.2) := by
    funext p; rw [laplaceBeltrami]
  rw [hEq]
  apply continuousOn_finsetSum; intro i _
  apply continuousOn_finsetSum; intro j _
  refine (hgi i j).mul
    ((chartComposed_pd_pd_jointContinuousOn_at N Θ u W₀ c t₁ t₂ R ht₁ i j hw hWc2 hWc1cont hWc2cont).sub
      ?_)
  apply continuousOn_finsetSum; intro k _
  exact (hChr k i j).mul
    (chartComposed_pd_jointContinuousOn_at N Θ u W₀ c t₁ t₂ R ht₁ k hw hWc2 hWc1cont)

/-- **★★ (F3, D5-at) `chartComposedHeatOp_jointContinuousOn_at` — `hBcont` re-centred at `c`.**  Joint
    continuity of the chart-composed order-`N` parametrix heat operator on `Icc t₁ t₂ ×ˢ closedBall c R`.
    `heatOp = ∂_τ − Δ_g` (the base slot `q` is IGNORED by the kernel `fun s x _ => …`), so this is the
    DIFFERENCE of (D3-at) and (D4-at).  The `c = w`, `W₀ = W w` instance is the base-`w` `hBcont`.
    NOT `a₁ = R/6`. -/
theorem chartComposedHeatOp_jointContinuousOn_at (N : ℕ)
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (W₀ : Point n → Point n) (c : Point n) (q : Point n) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hWc2 : ∀ z ∈ Metric.closedBall c R, ∀ a, ContDiffAt ℝ 2 (fun y => W₀ y a) z)
    (hWc1cont : ∀ a i, ContinuousOn (fun p : ℝ × Point n => pd (fun y => W₀ y a) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R))
    (hWc2cont : ∀ a i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W₀ z a) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 q)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  have hEq : (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix N Θ u s (W₀ x)) p.1 p.2 q)
      = fun p : ℝ × Point n =>
          deriv (fun s => heatParametrix N Θ u s (W₀ p.2)) p.1
            - laplaceBeltrami g gi (fun x => heatParametrix N Θ u p.1 (W₀ x)) p.2 := by
    funext p; rw [heatOp]
  rw [hEq]
  exact (chartComposed_dtau_jointContinuousOn_at N Θ u W₀ c t₁ t₂ R ht₁ hΘc hΘne huc hWc2).sub
    (chartComposed_laplaceBeltrami_jointContinuousOn_at N g gi Θ u W₀ c t₁ t₂ R ht₁ hw hgi hChr
      hWc2 hWc1cont hWc2cont)

/-! ###############################################################################
    ## (F2) — the base-`w` on-gate reduction (mirror of GatedWitnessHeatOpBridge at base `w`).
    ############################################################################### -/

/-- **★ (F2, L2a-at) `heatOpWitness_eq_heatOp_cutoffChart_at`.**  On `Icc t₁ t₂ ×ˢ closedBall w R` with
    the ball inside the OPEN gate `S w` (and `w ∈ K`), the base-`w` gated witness's heat operator equals
    the ungated cutoff-chart parametrix's — the base-`w` gate transfer via the base-GENERIC
    `gatedKernel_heatOp_eq_of_mem_nhds` and the definitional `vanVleckGatedWitness = gatedKernel K S H`.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_eq_heatOp_cutoffChart_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) {w : Point n} (hwK : w ∈ K) (hSopen : IsOpen (S w))
    (hsub : Metric.closedBall w R ⊆ S w) :
    ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R,
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w
        = heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK)) p.1 p.2 w := by
  intro p hp
  have hS : S w ∈ nhds p.2 := hSopen.mem_nhds (hsub hp.2)
  have h := QIQTH.HeatResidualBound.gatedKernel_heatOp_eq_of_mem_nhds g gi K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b
      (uniformInverseChart g gi hC hK)) p.1 p.2 w hwK hS
  simpa only [vanVleckGatedWitness] using h

/-- **★ (F2, L2b-at) `heatOp_cutoffChart_eq_chartParametrix_at`.**  Where the base-`w` radial cutoff is
    identically `1` near `z` (`hcut1`), the `heatOp` of the cutoff-chart parametrix agrees with the
    `heatOp` of the PURE chart-composed parametrix at `(τ,z,w)`.  `heatOp` is germ-local
    (`heatOp_congr_nhds`); time germ ∀ `t` (cutoff `τ`-independent), space germ on `hcut1`.
    NOT `a₁ = R/6`. -/
theorem heatOp_cutoffChart_eq_chartParametrix_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) {w : Point n}
    {z : Point n}
    (hcut1 : (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK w p'))
      =ᶠ[nhds z] (fun _ => (1 : ℝ))) :
    heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK)) τ z w
      = heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK w x)) τ z w := by
  refine heatOp_congr_nhds g gi _ _ τ z w ?_ ?_
  · have h1 : radialCutoff a b (uniformInverseChart g gi hC hK w z) = 1 := hcut1.self_of_nhds
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [globalCutoffParametrixWitnessN, h1, one_mul]
  · filter_upwards [hcut1] with p' hp'
    have hp'1 : radialCutoff a b (uniformInverseChart g gi hC hK w p') = 1 := hp'
    simp only [globalCutoffParametrixWitnessN, hp'1, one_mul]

/-- **★★ (F2, COMPOSED-at) `heatOpWitness_eq_chartParametrix_of_gate_cut_at`.**  L2a-at ∘ L2b-at: on the
    gate compact (`w∈K`, `S w` open, `closedBall w R ⊆ S w`) and under the near-diagonal cutoff germ
    `hcut1`, the base-`w` gated-witness heat operator equals the heat operator of the CHART-COMPOSED
    order-1 parametrix at `(p.1, p.2, w)`.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_eq_chartParametrix_of_gate_cut_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) {w : Point n} (hwK : w ∈ K) (hSopen : IsOpen (S w))
    (hsub : Metric.closedBall w R ⊆ S w)
    (p : ℝ × Point n) (hp : p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)
    (hcut1 : (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK w p'))
      =ᶠ[nhds p.2] (fun _ => (1 : ℝ))) :
    heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w
      = heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK w x)) p.1 p.2 w := by
  rw [heatOpWitness_eq_heatOp_cutoffChart_at g gi hC hK S a b t₁ t₂ R hwK hSopen hsub p hp]
  exact heatOp_cutoffChart_eq_chartParametrix_at g gi hC hK a b p.1 hcut1

/-- **★★ (F2, L3-at) `heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at`.**  Joint continuity of
    the base-`w` gated-witness heat operator `E(·,·,w)` on `Icc t₁ t₂ ×ˢ closedBall w R`, transferred by
    `ContinuousOn.congr` (through COMPOSED-at) from the CHART-COMPOSED parametrix heat operator `hBcont`
    (base slot `w`) and the near-diagonal cutoff germ `hcut`.  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) {w : Point n} (hwK : w ∈ K) (hSopen : IsOpen (S w))
    (hsub : Metric.closedBall w R ⊆ S w)
    (hcut : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R,
      (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK w p'))
        =ᶠ[nhds p.2] (fun _ => (1 : ℝ)))
    (hBcont : ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK w x)) p.1 p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) := by
  refine hBcont.congr (fun p hp => ?_)
  exact heatOpWitness_eq_chartParametrix_of_gate_cut_at g gi hC hK S a b t₁ t₂ R
    hwK hSopen hsub p hp (hcut p hp)

/-! ###############################################################################
    ## (F4-support) — the co-centred `(τ,z)`-lift + chart-fact discharge on `ball w ρc`.
    ##  (The `closedBall 0`→`closedBall c` re-centring of the J2–J4 engines; `pd_(pd_)continuousOn_open`
    ##  themselves already take an ARBITRARY open set, so only the lift + subset are re-centred.)
    ############################################################################### -/

/-- **Co-centred `(τ,z)`-lift of a `z`-only `ContinuousOn`.** -/
theorem lift_snd_at {φ : Point n → ℝ} {c : Point n} {R : ℝ}
    (h : ContinuousOn φ (Metric.closedBall c R)) (t₁ t₂ : ℝ) :
    ContinuousOn (fun p : ℝ × Point n => φ p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) :=
  h.comp (continuous_snd.continuousOn) (fun _ hp => hp.2)

/-- **(J2-at) `hWc2_of_contDiffOn_ball_at`.**  Per-component `ContDiffAt ℝ 2` at every `z ∈ closedBall c
    R` with `R < ρc`, from `ContDiffOn ℝ 2 W (ball c ρc)`. -/
theorem hWc2_of_contDiffOn_ball_at (W : Point n → Point n) (c : Point n) (ρc R : ℝ) (hR : R < ρc)
    (hW : ContDiffOn ℝ 2 W (Metric.ball c ρc)) :
    ∀ z ∈ Metric.closedBall c R, ∀ d, ContDiffAt ℝ 2 (fun y => W y d) z := by
  intro z hz d
  have hzball : z ∈ Metric.ball c ρc := Metric.closedBall_subset_ball hR hz
  have hWatz : ContDiffAt ℝ 2 W z := hW.contDiffAt (Metric.isOpen_ball.mem_nhds hzball)
  exact (contDiff_apply ℝ ℝ d).contDiffAt.comp z hWatz

/-- **(J3-at) `hWc1cont_of_contDiffOn_ball_at`.**  The first coordinate-jet is jointly `ContinuousOn (Icc
    t₁ t₂ ×ˢ closedBall c R)` for `R < ρc`, via `pd_continuousOn_open` on `ball c ρc`, restricted+lifted. -/
theorem hWc1cont_of_contDiffOn_ball_at (W : Point n → Point n) (c : Point n) (ρc R t₁ t₂ : ℝ)
    (hR : R < ρc) (hW : ContDiffOn ℝ 2 W (Metric.ball c ρc)) :
    ∀ d i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => W y d) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  intro d i
  have hcomp : ContDiffOn ℝ 2 (fun y => W y d) (Metric.ball c ρc) :=
    (contDiff_apply ℝ ℝ d).comp_contDiffOn hW
  have hz : ContinuousOn (fun w => pd (fun y => W y d) i w) (Metric.ball c ρc) :=
    pd_continuousOn_open (fun y => W y d) i Metric.isOpen_ball hcomp
  exact lift_snd_at (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-- **(J4-at) `hWc2cont_of_contDiffOn_ball_at`.**  The mixed second coordinate-jet is jointly
    `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall c R)` for `R < ρc`, via `pd_pd_continuousOn_open` on `ball c
    ρc`, restricted+lifted. -/
theorem hWc2cont_of_contDiffOn_ball_at (W : Point n → Point n) (c : Point n) (ρc R t₁ t₂ : ℝ)
    (hR : R < ρc) (hW : ContDiffOn ℝ 2 W (Metric.ball c ρc)) :
    ∀ d i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W z d) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall c R) := by
  intro d i j
  have hcomp : ContDiffOn ℝ 2 (fun y => W y d) (Metric.ball c ρc) :=
    (contDiff_apply ℝ ℝ d).comp_contDiffOn hW
  have hz : ContinuousOn (fun w => pd (fun y => pd (fun z => W z d) j y) i w) (Metric.ball c ρc) :=
    pd_pd_continuousOn_open (fun z => W z d) i j Metric.isOpen_ball hcomp
  exact lift_snd_at (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-! ###############################################################################
    ## (F4) — the frozen-base-`w` capstones (co-centred at `w`).
    ############################################################################### -/

/-- **★★ (F4, active) `heatOpWitness_fixedBase_active_continuousOn`.**  The base-`w` gated-witness heat
    operator `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall w R)` (the ACTIVE region), obtained by
    plugging the CONCRETE F3 `hBcont` at base `w` (`chartComposedHeatOp_jointContinuousOn_at` at `N=1`,
    `Θ* = vanVleck g`, `u* = transportCoeff …`, `W₀ = uniformInverseChart g gi hC hK w`, centre `c = w`,
    base slot `q = w`) into the F2 L3-at reduction.  Every carry is genuine and satisfiable
    (coefficient/geometry regularity, the chart facts, the gate data, the cutoff germ).  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_active_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) {w : Point n} (hwK : w ∈ K) (hSopen : IsOpen (S w))
    (hsub : Metric.closedBall w R ⊆ S w)
    (hcut : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R,
      (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK w p'))
        =ᶠ[nhds p.2] (fun _ => (1 : ℝ)))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hWc2 : ∀ z ∈ Metric.closedBall w R, ∀ c,
      ContDiffAt ℝ 2 (fun y => uniformInverseChart g gi hC hK w y c) z)
    (hWc1cont : ∀ c i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hC hK w y c) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R))
    (hWc2cont : ∀ c i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => uniformInverseChart g gi hC hK w z c) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) :=
  heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at g gi hC hK S a b t₁ t₂ R
    hwK hSopen hsub hcut
    (chartComposedHeatOp_jointContinuousOn_at 1 g gi (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) (uniformInverseChart g gi hC hK w)
      w w t₁ t₂ R ht₁ hw hΘc hΘne huc hgi hChr hWc2 hWc1cont hWc2cont)

/-- **★★ (F4, chart-free active) `heatOpWitness_fixedBase_active_chartFree`.**  The active-region
    continuity with the THREE chart facts made INTERNAL: there is a radius `ρc>0` (the `C²` region of
    `W w = uniformInverseChart g gi hC hK w` around its centre `w`, from F1) such that for EVERY `R` with
    `0 < R < ρc`, given the honest remaining carries — gate data / cutoff germ / coefficient regularity /
    geometry continuities — `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall w R)`.  The chart facts
    are DISCHARGED (J2–J4 engines) from F1's `ContDiffOn ℝ 2 (W w) (ball w ρc)`.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_active_chartFree (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) {w : Point n} (hwK : w ∈ K)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ ρc : ℝ, 0 < ρc ∧ ∀ R : ℝ, 0 < R → R < ρc →
      IsOpen (S w) →
      Metric.closedBall w R ⊆ S w →
      (∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R,
        (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK w p'))
          =ᶠ[nhds p.2] (fun _ => (1 : ℝ))) →
      (∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) →
      (∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R)) →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) := by
  obtain ⟨ρc, hρc, hball⟩ := chartField_contDiffOn_ball_at g gi hC hK hwK
  refine ⟨ρc, hρc, fun R hRpos hR hSopen hsub hcut hgi hChr => ?_⟩
  exact heatOpWitness_fixedBase_active_continuousOn g gi hC hK S a b t₁ t₂ R ht₁ hwK hSopen hsub
    hcut hw hΘc hΘne huc hgi hChr
    (hWc2_of_contDiffOn_ball_at _ w ρc R hR hball)
    (hWc1cont_of_contDiffOn_ball_at _ w ρc R t₁ t₂ hR hball)
    (hWc2cont_of_contDiffOn_ball_at _ w ρc R t₁ t₂ hR hball)

/-! ###############################################################################
    ## (F4, full) — the frozen-base-`w` near+off paste (co-centred at `w`).
    ############################################################################### -/

/-- **★★★ (F4) `heatOpWitness_fixedBase_continuousOn` — THE FROZEN-BASE-`w` NEAR+OFF CAPSTONE.**  For the
    base-`w` gated van-Vleck witness heat operator `E p := heatOp g gi (vanVleckGatedWitness …) p.1 p.2 w`,
    given:

    * `hRρc : R < ρc` and `hWwcont` — `W w = uniformInverseChart g gi hC hK w` is `ContinuousOn (ball w
      ρc)` (its `C²` region around the centre `w`, from F1 `chartField_contDiffOn_ball_at`);
    * an OPEN active set `A` with `hEA : ContinuousAt E` on `A` — the banked base-`w` active-region
      continuity (`heatOpWitness_fixedBase_active_chartFree` gives `ContinuousOn` on `closedBall w R`;
      `A` is any open set inside its interior covering the support);
    * `hoff` — the HONEST collar carry: every slab point OFF `A` is strictly far,
      `b² < rncRadialSq (W w ·)` (the cutoff support ⊆ `A`),

    the slice `E(·,·,w)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall w R)`.  The local-zero half is
    DISCHARGED here (via J4-292 B1/B2 at base `q = w`, which is base-generic); the active-region
    continuity is the carried banked capstone.  Co-centred at `w`; the reconciliation to origin-centred
    `closedBall 0 R` for a.e. `w` (a chart-ball COVER) is the named residual.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_fixedBase_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t₁ t₂ R ρc : ℝ) {w : Point n} (hRρc : R < ρc)
    (hWwcont : ContinuousOn (uniformInverseChart g gi hC hK w) (Metric.ball w ρc))
    (A : Set (ℝ × Point n))
    (hEA : ∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w) p)
    (hoff : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R, p ∉ A →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall w R) := by
  refine continuousOn_of_active_open_zero_off _ _ A hEA ?_
  intro p hp hpA
  have hfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w p.2) := hoff p hp hpA
  have hz : p.2 ∈ Metric.ball w ρc := Metric.closedBall_subset_ball hRρc hp.2
  have hballnhds : Metric.ball w ρc ∈ nhds p.2 := Metric.isOpen_ball.mem_nhds hz
  have hNnhds : (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v}
      ∈ nhds p.2 :=
    (hWwcont.continuousAt hballnhds).preimage_mem_nhds
      ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hfar)
  have hN'nhds :
      (uniformInverseChart g gi hC hK w) ⁻¹' {v : Point n | b ^ 2 < rncRadialSq v}
          ∩ Metric.ball w ρc ∈ nhds p.2 :=
    Filter.inter_mem hNnhds hballnhds
  have hprodnhds : Set.univ ×ˢ ((uniformInverseChart g gi hC hK w) ⁻¹'
      {v : Point n | b ^ 2 < rncRadialSq v} ∩ Metric.ball w ρc) ∈ nhds p := by
    have h := prod_mem_nhds (Filter.univ_mem : (Set.univ : Set ℝ) ∈ nhds p.1) hN'nhds
    rwa [Prod.mk.eta] at h
  filter_upwards [hprodnhds] with x hx
  have hx2 : x.2 ∈ (uniformInverseChart g gi hC hK w) ⁻¹'
      {v : Point n | b ^ 2 < rncRadialSq v} ∩ Metric.ball w ρc := hx.2
  have hxfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w x.2) := hx2.1
  have hxball : x.2 ∈ Metric.ball w ρc := hx2.2
  have hWc_x : ContinuousAt (uniformInverseChart g gi hC hK w) x.2 :=
    hWwcont.continuousAt (Metric.isOpen_ball.mem_nhds hxball)
  show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) x.1 x.2 w = 0
  simp only [vanVleckGatedWitness]
  exact heatOpGatedWitness_eq_zero_of_far g gi ha hab 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) K S (uniformInverseChart g gi hC hK)
    x.1 w hWc_x hxfar

#check @chartField_contDiffAt_center_at
#check @chartField_contDiffOn_ball_at
#check @chartComposedHeatOp_jointContinuousOn_at
#check @heatOpWitness_eq_chartParametrix_of_gate_cut_at
#check @heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at
#check @heatOpWitness_fixedBase_active_continuousOn
#check @heatOpWitness_fixedBase_active_chartFree
#check @heatOpWitness_fixedBase_continuousOn

end QIQTH.FrozenBaseWChain

/-! ## Axiom checks — every theorem `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FrozenBaseWChain
#print axioms chartField_contDiffAt_center_at
#print axioms chartField_contDiffOn_ball_at
#print axioms chartComposed_pd_jointContinuousOn_at
#print axioms chartComposed_pd_pd_jointContinuousOn_at
#print axioms chartComposed_dtau_jointContinuousOn_at
#print axioms chartComposed_laplaceBeltrami_jointContinuousOn_at
#print axioms chartComposedHeatOp_jointContinuousOn_at
#print axioms heatOpWitness_eq_heatOp_cutoffChart_at
#print axioms heatOp_cutoffChart_eq_chartParametrix_at
#print axioms heatOpWitness_eq_chartParametrix_of_gate_cut_at
#print axioms heatOpGatedWitness_jointContinuousOn_of_chartParametrix_at
#print axioms heatOpWitness_fixedBase_active_continuousOn
#print axioms heatOpWitness_fixedBase_active_chartFree
#print axioms heatOpWitness_fixedBase_continuousOn
end AxiomChecks
