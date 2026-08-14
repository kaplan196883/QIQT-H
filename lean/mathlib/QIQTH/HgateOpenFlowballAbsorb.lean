/-
  HgateOpenFlowballAbsorb — J4-745 (TASK A): THE FLOWBALL TRIPLE-ABSORPTION — `hgate` **AND** the
  width-2 package `hpkgBound` **AND** the origin gate-openness `hopenS0`, all absorbed into a
  v2-descended capstone from PURE GEOMETRY, at ONE shared flow-ball gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (J4-745 · TASK A) HOW THE RADIUS-OPACITY WALL IS DISSOLVED FOR `hopenS0`.

  `HgatePkgFlowballAbsorb.a1_R6_from_data_v4c` (J4-744) absorbed `hgate` + `hpkgBound` + `hmemS0` at the
  flow-ball gate but STILL CARRIED the origin gate-openness `hopenS0 : ∀ c, 0∈K → IsOpen (constGate … c 0)`
  as a ∀-over-radii binder.  It could not be discharged from `hgate`'s produced triple, because the
  producer `CurvedHgateGlue.hgate_width43_quad_affine_flowball` EXPORTS ONLY `∃ a b c P₀ P₁, hgate` — the
  produced `c` is opaque, so the constraint `c < δ₀` (the chart-radius bound the openness proof needs) is
  NOT visible on the outside.  Supplying openness from an INDEPENDENT supplier (e.g. the δ₀-bounded
  `flowBall_gateRadius_floor`) hits the J4-741/743 RADIUS-OPACITY wall: two independent existential radii
  cannot be aligned.

  ⭐ THE DISSOLUTION.  The openness is ALREADY PROVEN INSIDE the producer's own proof (verbatim
  `(hchartOC c hc0 hc_δ₀).1`, at the producer's OWN `c`), but the base producer never exported it.  So we
  build a producer VARIANT `hgate_flowball_width43_open` that runs the identical construction and adds ONE
  extra deliverable to the ∃-package — `∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)`
  — read off the SAME chart spec `uniformInverseChart_huniformChart` at the SAME `c`.  (This is exactly the
  export pattern `CurvedUnifiedGateBounds.hgate_and_gateSq_flowball` uses to add a `GateSqControl`.)  Now
  `hopenS0` is DERIVED at `hgate`'s own gate: no second opaque existential, no radius alignment.

  `a1_R6_from_data_v4d` therefore absorbs `hgate` + `hpkgBound` + `hmemS0` (as v4c) AND `hopenS0` — a
  strict improvement over v4c, from geometry alone, at ONE gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (J4-745 · TASK B) the measurability `hKSmeas` — DISSOLVED THE SAME WAY.

  The joint gate-graph `MeasurableSet` is NOT a consequence of pointwise gate-openness (openness of
  `constGate … z` for a FIXED `z` says nothing about JOINT measurability over varying `z`).  Its banked
  supplier `ConcreteGateInstantiation.hKSmeas_concrete` proves it via the JOINTLY-CONTINUOUS injective
  forward-flow graph map `Θ(q,v) = (q, φ_q v)` + Lusin–Souslin — jointly continuous only inside the flow
  radius, so it needs `c < δm := min (germ radius) (uniformFlowRadius)`.  That is again the radius-opacity
  wall.  DISSOLUTION: the producer variant folds `δm` INTO the gate-radius min, so its produced `c < δm`
  BY CONSTRUCTION, and exports the joint `MeasurableSet` at the produced `c` — no second opaque radius.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Absorbing
  `hopenS0` + `hKSmeas` removes exactly those carriers from the v2 surface at the flow-ball gate; it
  closes NOTHING deeper.  What remains CONDITIONAL (UNCHANGED in content):
    • the CONVERGENCE-TRIO content inside the `A1R6GateSlots` Duhamel census — NEVER claimed closed;
    • the `hcarTau`/`hcarField`/`hcarField2` jet-supplier existentials — carried ∀-over-gates;
    • the base-metric identification `hgPull` and the F4 pullback residues (group (D′)).
  No `sorry`, no `admit`, no `:= True`, no new axiom (`std-3` only), no vacuous / unsatisfiable
  hypothesis (the flow-ball producer's `hframeK` holds on `K = {0}` by `curvedRNCMetric_zero`), no
  existing file edited.  `a₁ = R/6` stays CONDITIONAL.
-/
import Mathlib
import QIQTH.HgatePkgFlowballAbsorb
import QIQTH.CurvedHgateGlue
import QIQTH.ConcreteGateInstantiation

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix
open QIQTH.A1R6FromData QIQTH.HGaussAbsorb QIQTH.CurvedHgateGlue
open QIQTH.HeatParametrixOrder QIQTH.GaussianPolyBound QIQTH.RNCDecay
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HgateOpenFlowballAbsorb

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### (J4-745 · A) `hgate_flowball_width43_open` — the base producer PLUS gate-openness export.
    ############################################################################### -/

/-- **★★ (G++) — `hgate_flowball_width43_open`.**  Verbatim
    `CurvedHgateGlue.hgate_width43_quad_affine_flowball` (the metric-agnostic on-gate width-4/3
    quadratic-affine `hgate` producer) with TWO extra deliverables at the SAME produced flow-ball gate `c`:
      • (TASK A) the gate-openness certificate `∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' ball 0 c)`
        — read off the SAME chart spec `uniformInverseChart_huniformChart` (`(hchartOC c hc0 hc_δ₀).1`);
      • (TASK B) the joint gate-graph `MeasurableSet {w | w.2.2∈K ∧ w.2.1 ∈ φ_(w.2.2) '' ball 0 c}` —
        supplied by `ConcreteGateInstantiation.hKSmeas_concrete`, whose radius `δm` is FOLDED INTO the
        gate-radius min so the produced `c < δm` by construction.
    These are the two exports that let `hopenS0` AND `hKSmeas` be discharged at `hgate`'s OWN gate,
    dissolving the J4-741/743 radius-opacity wall for both.  NOT `a₁ = R/6`. -/
theorem hgate_flowball_width43_open (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∃ a b c P₀ P₁ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      (∀ q : Point n, q ∈ K →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c)) ∧
      (MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c}) ∧
      (∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure ((fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) q) →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) := by
  classical
  -- ── the two coefficient suppliers (as in the banked width-2 package).
  obtain ⟨ρ0, hρ0, C0, hC0', hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1', hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  have hρc0 : 0 < min ρ0 ρ1 := lt_min hρ0 hρ1
  -- ── the chart/naturality/near-isometry radii.
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrN, hnat⟩ := laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨rI, hrI, hiso⟩ := QIQTH.HrawNearIsometryConcrete.nearIsometry_concrete g gi hC hK
  -- ── the joint-measurability supplier's radius, FOLDED INTO the gate-radius min (TASK B).
  obtain ⟨δm, hδm, hmeasspec⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  set ρc : ℝ := min (min (min rN δ₀) rI) δm with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min (lt_min hrN hδ₀) hrI) hδm
  have hρc_rN : ρc ≤ rN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρc_δ₀ : ρc ≤ δ₀ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρc_rI : ρc ≤ rI := (min_le_left _ _).trans (min_le_right _ _)
  have hρc_δm : ρc ≤ δm := min_le_right _ _
  -- ── the file-1 width-1 quadratic affine cutoff `N = 1` residual.
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB₀, hB₁, hCUT⟩ :=
    cutoffResidualN1_uniformFlow_width1_quad_affine g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      (min ρ0 ρ1) C0 C1 hρc0 hC0' hC1'
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
      ρc hρc
  -- ── the gate radius `c = (b + ρc)/2`.
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_rI : c < rI := lt_of_lt_of_le hcρc hρc_rI
  have hc_δm : c < δm := lt_of_lt_of_le hcρc hρc_δm
  have hP₀' : (0 : ℝ) ≤ B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n :=
    mul_nonneg (mul_nonneg hB₀ (by norm_num)) (by positivity)
  have hP₁' : (0 : ℝ) ≤ B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n :=
    mul_nonneg (mul_nonneg hB₁ (by norm_num)) (by positivity)
  -- ── THE EXTRA EXPORT: gate-openness at the SAME produced `c`, off the SAME chart spec.
  have hopenAll : ∀ q : Point n, q ∈ K →
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c) := by
    intro q hq
    obtain ⟨_, hchartOC⟩ := hchart q hq
    exact (hchartOC c hc0 hc_δ₀).1
  -- ── THE EXTRA EXPORT (TASK B): the joint gate-graph MeasurableSet at the SAME produced `c`.
  have hmeasSet : MeasurableSet {w : ℝ × Point n × Point n |
      w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c} :=
    hmeasspec c hc0 hc_δm
  refine ⟨a, b, c, B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n,
    B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n, ha, hab, hbc, hP₀', hP₁', hopenAll, hmeasSet, ?_⟩
  intro τ hτ q hq p hp
  have hfac0 : (0 : ℝ) ≤ B₀ + B₁ * τ := add_nonneg hB₀ (mul_nonneg hB₁ hτ.le)
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  have hopen : IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) :=
    (hchartOC c hc0 hc_δ₀).1
  have hclos : closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c := (hchartOC c hc0 hc_δ₀).2
  simp only [vanVleckGatedWitness]
  by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c
  · -- ═══ IN-GATE LEG: G2a transfer + transport identity + CUT + chart transfer.
    rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K
      (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
      (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))
      τ p q hq (hopen.mem_nhds hpS)]
    obtain ⟨v, hvmem, hvp⟩ := hpS
    rw [mem_ball_zero_iff] at hvmem
    rw [← hvp]
    have hvN : ‖v‖ < rN := lt_trans hvmem hc_rN
    have hvδ₀ : ‖v‖ < δ₀ := lt_trans hvmem hc_δ₀
    have hvrI : ‖v‖ < rI := lt_trans hvmem hc_rI
    obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
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
    have hf : ContDiffAt ℝ 2
        (fun x => globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ x q)
        (uniformFlowExp g gi hC hK q v) := by
      have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y
          * heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) τ y)
          (uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)) := by
        apply ContDiffAt.mul
        · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
        · exact (heatParametrix_contDiff_space 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) τ hw).contDiffAt.of_le le_top
      exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
    have hpt : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
      simpa using hgerm.eq_of_nhds
    have hprofilegerm :
        (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK) τ (uniformFlowExp g gi hC hK q z) q)
          =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) τ y) := by
      filter_upwards [hgerm] with z hz
      have hz' : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z) = z := hz
      simp only [globalCutoffParametrixWitnessN, hz']
    have hlap : laplaceBeltrami g gi
          (fun x => globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK) τ x q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) τ y) v := by
      have hn' := hnat
        (fun x => globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ x q)
        q hq v hvN hg1 hf hU hGGi hGiG
      rw [← hn']
      exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
        (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
        _ _ v hprofilegerm
    have htransport :
        heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q
          = radialCutoff a b v * deriv (fun s => heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) τ y) v := by
      simp only [heatOp]
      have hterm1fun :
          (fun s => globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK) s
              (uniformFlowExp g gi hC hK q v) q)
            = (fun s => radialCutoff a b v * heatParametrix 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) s v) := by
        funext s
        simp only [globalCutoffParametrixWitnessN, hpt]
      rw [hterm1fun, deriv_const_mul_field, hlap]
    rw [htransport]
    -- the file-1 in-chart width-1 quadratic affine bound.
    have hchartbd := hCUT τ hτ q hq v
    -- the concrete two-sided (1/4) near-isometry.
    have hisoq := hiso q hq v hvrI
    -- the banked quadratic chart→ambient transfer (width 1 → width 4/3).
    have htrans := QIQTH.HrawPreCollapse.chartTransfer_quad_from_nearIsometry
      (n := n) hτ hfac0 hisoq hchartbd
    calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) τ y) v|
        ≤ (B₀ + B₁ * τ) * (25 / 16) * Real.sqrt (4 / 3) ^ n
            * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
              * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := htrans
      _ = (B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n
            + B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n * τ)
            * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
              * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by ring
  · -- ═══ FRONTIER LEG: the gate radius `c > b` kills the cutoff — the witness is locally zero.
    obtain ⟨w', hw'mem, hw'p⟩ := hclos hp
    rw [mem_closedBall_zero_iff] at hw'mem
    have hnormeq : ‖w'‖ = c := by
      rcases lt_or_eq_of_le hw'mem with hlt | heq
      · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
          p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) hpS
      · exact heq
    have hw'δ₀ : ‖w'‖ < δ₀ := by rw [hnormeq]; exact hc_δ₀
    obtain ⟨hgerm', hWc2'⟩ := hchartGerm w' hw'δ₀
    have hWp : uniformInverseChart g gi hC hK q p = w' := by
      rw [← hw'p]; simpa using hgerm'.eq_of_nhds
    have hb2 : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK q p) := by
      rw [hWp]
      have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := norm_sq_le_rncRadialSq w'
      have hb0' : 0 < b := lt_trans ha hab
      nlinarith [h1, hnormeq, hb0', hbc]
    have hcontp : ContinuousAt (uniformInverseChart g gi hC hK q) p := by
      rw [← hw'p]; exact hWc2'.continuousAt
    have hNnhds :
        (uniformInverseChart g gi hC hK q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w}
          ∈ nhds p :=
      hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
    have hzero : heatOp g gi (gatedKernel K
        (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
        (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK))) τ p q = 0 := by
      refine heatOp_eq_zero_of_locally_zero g gi _ τ p q ?_ ?_
      · exact Filter.Eventually.of_forall (fun t => gatedKernel_apply_of_notMem K
          (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
          _ t p q (Or.inr hpS))
      · filter_upwards [hNnhds] with p' hp'
        by_cases hp'S : p' ∈ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c
        · rw [gatedKernel_apply_of_mem K
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            _ τ hq hp'S]
          simp only [globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hp'), zero_mul]
        · exact gatedKernel_apply_of_notMem K
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            _ τ p' q (Or.inr hp'S)
    rw [hzero, abs_zero]
    have hX0 : 0 ≤ rncRadialSq (p - q) / τ := div_nonneg (rncRadialSq_nonneg _) hτ.le
    have hpoly0 : 0 ≤ (rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1 := by
      nlinarith [sq_nonneg (rncRadialSq (p - q) / τ)]
    exact mul_nonneg (add_nonneg hP₀' (mul_nonneg hP₁' hτ.le))
      (mul_nonneg hpoly0 (QIQTH.ResidueBound.gaussDdim_nonneg _ _))

/-! ###############################################################################
    ### (J4-745 · A) `a1_R6_from_data_v4d` — v4c with `hopenS0` ALSO ABSORBED.
    ############################################################################### -/

/-- **★★★★★ J4-745 — `a1_R6_from_data_v4d`.**  `HgatePkgFlowballAbsorb.a1_R6_from_data_v4c` RESTATED
    WITHOUT its `hopenS0` binder AND WITHOUT its `hKSmeas` binder — both discharged INTERNALLY at the
    flow-ball producer's OWN gate via the openness + joint-measurability exports of
    `hgate_flowball_width43_open`.  Absorbs `hgate` + `hpkgBound` + `hmemS0` (as v4c) AND `hopenS0` AND
    `hKSmeas`, from geometry alone, at ONE gate.

    ⚠ THE HONEST SUMMARY.  Maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT `a₁ = R/6`.  Absorbing
    `hopenS0` + `hKSmeas` removes exactly those carriers at the flow-ball gate; it closes nothing deeper.
    What remains CONDITIONAL: the `A1R6GateSlots` censuses (Duhamel/W1-free/L2 — the convergence-trio
    content), `hcarTau`/`hcarField`/`hcarField2`, the base-metric identification `hgPull` (group (D′)).
    ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v4d (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hcarTau : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ k : Fin n,
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t)
    (gb gib : Point n → Fin n → Fin n → ℝ)
    (hCb : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel gb gib a b c y))
    (hgPull : g = expPullbackMetric gb gib hCb 0)
    (hsymmb : ∀ y a b, gb y a b = gb y b a)
    (hinvb : ∀ y a b, (∑ σ, gb y a σ * gib y σ b) = if a = b then 1 else 0)
    (hgb : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gb y a b))
    (hgaugeb : ∀ a b, gb 0 a b = if a = b then 1 else 0) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
    (heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- ── consume the AUGMENTED flow-ball producer: gate radii + width-4/3 `hgate` + gate-openness + measSet.
  obtain ⟨a, b, c, P₀, P₁, ha, hab, hbc, hP₀, hP₁, hopenAll, hKSmeasSet, hgate⟩ :=
    hgate_flowball_width43_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  -- ── DERIVE `hEdom` (width-3/2 Gaussian) from the SAME `hgate` at the flow-ball gate.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    hEdom_vanVleck_of_hgate_affine g gi hChr hK (constGate g gi hChr hK c) a b P₀ P₁ hP₀ hP₁ hgate
  -- ── WIDTH-WIDEN `hEdom` (3/2 → 2) into the width-2 all-`t'` package bound `hpkgBound`.
  set S1 : ℝ := Real.sqrt (3 / 2) ^ n with hS1def
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hScdef
  have hS10 : (0 : ℝ) ≤ S1 := by rw [hS1def]; positivity
  have hSc0 : (0 : ℝ) ≤ Sc := by rw [hScdef]; positivity
  set C : ℝ := (E₀ + E₁) * S1 * Sc with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hCdef]; exact mul_nonneg (mul_nonneg (add_nonneg hE₀ hE₁) hS10) hSc0
  have hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro t' τ p q hτ hτt
    have hE := hEdom τ hτ p q
    have hwiden : gaussDdim (3 / 2 * τ) (p - q) ≤ Sc * gaussDdim (2 * τ) (p - q) := by
      have hchart := gaussDdim_le_gaussDdim_chart (n := n) (c := 3 / 2) (d := 2)
        (by norm_num) (by norm_num) hτ (v := p - q) (w := p - q)
        (by nlinarith [rncRadialSq_nonneg (p - q)])
      rw [hScdef]; exact hchart
    have hbk : baseKernelW (2 : ℝ) (0 : ℝ) τ p q = gaussDdim (2 * τ) (p - q) :=
      baseKernelW_zero_apply (2 : ℝ) τ p q
    have haff : E₀ + E₁ * τ ≤ (E₀ + E₁) * (1 + t') := by nlinarith [hE₁, hE₀, hτ, hτt, hτ.le]
    have hgnn : (0 : ℝ) ≤ gaussDdim (2 * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * S1 * gaussDdim (3 / 2 * τ) (p - q) := hE
        _ ≤ (E₀ + E₁ * τ) * S1 * (Sc * gaussDdim (2 * τ) (p - q)) := by
              apply mul_le_mul_of_nonneg_left hwiden
              exact mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hτ.le)) hS10
        _ = ((E₀ + E₁ * τ) * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by ring
        _ ≤ ((E₀ + E₁) * (1 + t') * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by
              apply mul_le_mul_of_nonneg_right _ hgnn
              apply mul_le_mul_of_nonneg_right haff
              exact mul_nonneg hS10 hSc0
        _ = (C * (1 + t')) * gaussDdim (2 * τ) (p - q) := by rw [hCdef]; ring
        _ = (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by rw [hbk]
  -- ── `hmemS0` discharged at the flow-ball gate: `φ_0 0 = 0`, `0 ∈ K`, `0 < c`.
  have hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0 := by
    intro _
    refine ⟨0, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_zero]; exact hc0
    · exact uniformFlowExp_zero g gi hChr hK 0 hK0
  -- ── `hopenS0` discharged at the SAME produced gate `c` (TASK A), off the producer's openness export.
  have hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0) := by
    intro h0
    exact hopenAll 0 h0
  -- ── assemble the ∃-quantified conclusion and re-export the CONDITIONAL two-jet from `v2`.
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  exact a1_R6_from_data_v2 hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    P₀ P₁ hP₀ hP₁ hgate
    hKSmeasSet (hcarTau a b c ha hab hbc) (hcarField a b c ha hab hbc) (hcarField2 a b c ha hab hbc)
    hgiMeas hchrMeas
    hpkgBound hmemS0 hopenS0
    (slots a b c ha hab hbc)
    gb gib hCb hgPull hsymmb hinvb hgb hgaugeb

end QIQTH.HgateOpenFlowballAbsorb

/-! ###############################################################################
    ### THE AUDIT — `#print axioms` for the augmented producer + the capstone (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.HgateOpenFlowballAbsorb
#print axioms hgate_flowball_width43_open
#print axioms a1_R6_from_data_v4d
end AxiomChecks
