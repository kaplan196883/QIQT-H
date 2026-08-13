/-
  CurvedUnifiedGateBounds — J4-680: THE WIDTH GATE-UNIFICATION BRICK.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-679 OBSTRUCTION THIS FILE REMOVES.

  The curved capstone's fed slots split across THREE suppliers that each ∃-produce their OWN gate
  parameters `(a,b,c)`, so their bounds are about DIFFERENT gated-witness objects `cW`:

    • `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` — the width-2 heatOp `hpkgBound` at ITS gate;
    • `CurvedHgateGlue.curvedRNC_hEdom_width32_from_geometry` — the width-3/2 `hEdom` at ITS gate;
    • `CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom` — the width-3/2 `hAdom`/`hWDom`
       at ITS gate.

  Because the gated witness `vanVleckGatedWitness … (constGate … c) a b` is PARAMETERIZED by the gate,
  bounds at different `(a,b,c)` are incomparable — the capstone needs them all at ONE gate.

  ## THE UNIFICATION (monotonicity verdict, J4-680).

  * `(a,b,c)` are all THRESHOLD-MONOTONE: the glue construction runs the width-1 quadratic cutoff at
    `ρc = min (min rN δ₀) rI` and sets `c = (b+ρc)/2 ∈ (b, ρc)`; ANY `c` in that interval works.  The
    width-2 pkg bound is NOT a separate radius fix at all — it is a **width-widening consequence** of
    the width-3/2 `hEdom` at the SAME gate:
        `gaussDdim ((3/2)τ) ≤ √(2/(3/2))ⁿ · gaussDdim (2τ) = √(4/3)ⁿ · baseKernelW 2 0 τ`
    (`WidthMarginEngine.gaussDdim_le_gaussDdim_chart` at `(c,d)=(3/2,2)`), plus the affine-to-all-`t'`
    rescale `(E₀+E₁τ) ≤ (E₀+E₁)(1+t')`.  So pkg and hEdom share the gate with NO extra analysis.
  * `hAdom`/`hWDom` also share that SAME gate: the glue construction already carries the CONCRETE
    two-sided (1/4) near-isometry `nearIsometry_concrete` on `‖v‖ < rI`, and `c < rI`.  That
    near-isometry `|r²(v) − r²(φv−q)| ≤ (1/4)·r²(φv−q)` gives EXACTLY the displacement budget
    `(3/2)·r²(φv−q) ≤ 2·r²(v)` that `gateSqControl_of_flowBall` demands — so a `GateSqControl`
    certificate is available at glue's NATIVE gate (no `r₁` from `uniformFlowExp_hdisp_ball` needed,
    no radius mismatch), and `exists_D1_constants_of_gateSqControl` produces `hAdom`/`hWDom` there.

  Hence: NOT a re-derivation of any analysis, just a re-instantiation that (i) augments the glue
  flowball construction to ALSO return its `GateSqControl`, and (ii) width-widens `hEdom → pkg`.

  ## DELIVERABLES.
    • `hgate_and_gateSq_flowball` — ★★ METRIC-AGNOSTIC: the glue on-gate width-4/3 quadratic affine
       `hgate` PLUS the `GateSqControl` certificate at the SAME flow-ball gate, from ONE bundle.
    • `curvedRNC_gate_bundle` — ★★★ the CURVED instantiation (`κ < 0`, seed `K = {0}`).
    • `curvedRNC_unified_gate_bounds` — ★★★ THE UNIFICATION: one `(a,b,c)`, with the width-2 pkg
       all-`t'` bound ∧ the width-3/2 `hEdom` ∧ the width-3/2 `hAdom` ∧ the frozen `hWDom`, all at
       that gate's `cW`.
    • `curvedRNC_unified_gate_bounds_curved_satisfiable` — the cp466 `Ric(0) ≠ 0` gate re-export.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It is GATE PLUMBING ONLY — it removes the
  J4-679 shared-gate obstruction so the pkg / hEdom / hAdom slots reference ONE witness.  The
  ~40-member W-census analytic pile, `hDuhamel`/`hDConv` (the differentiation-under-∫ / delta-family
  ARROWS), and the labelled inputs (incl. `R/6` as a labelled carrier) are UNTOUCHED and remain owed.
  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis (the curved seed `K = {0}` is where
  `hframeK` holds by `curvedRNCMetric_zero` — no cp466 collision), no existing file edited.  NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Width1QuadCutoff
import QIQTH.ConstRadiusGateExport
import QIQTH.HrawNearIsometryConcrete
import QIQTH.HrawPreCollapse
import QIQTH.HgateAffineRepair
import QIQTH.CurvedHgateGlue
import QIQTH.CurvedRNCBaseWitnessDomAdom
import QIQTH.ConcreteDominations
import QIQTH.WidthMarginEngine
import QIQTH.ParametrixHEboundWiring

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.WidthAdapters
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedUnifiedGateBounds

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (G+) — ★★ the METRIC-AGNOSTIC on-gate width-4/3 `hgate` PLUS the `GateSqControl`. -/

/-- **★★ (G+) — `hgate_and_gateSq_flowball`.**  THE GLUE, AUGMENTED.  Verbatim
    `CurvedHgateGlue.hgate_width43_quad_affine_flowball` (the on-gate width-4/3 quadratic affine
    `hgate` producer) with ONE extra deliverable: the `GateSqControl` certificate at the SAME flow-ball
    gate, produced from the concrete two-sided (1/4) near-isometry `nearIsometry_concrete` (already used
    for the `hgate` chart transfer) via `gateSqControl_of_flowBall`.  This is the single object that
    lets the width-2/width-3/2 `heatOp` bounds AND the width-3/2 witness `hAdom` bound live at ONE gate.
    NOT `a₁ = R/6`. -/
theorem hgate_and_gateSq_flowball (g gi : Point n → Fin n → Fin n → ℝ)
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
      (∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure ((fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) q) →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) ∧
      GateSqControl K (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
        (uniformInverseChart g gi hC hK) := by
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
  set ρc : ℝ := min (min rN δ₀) rI with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrN hδ₀) hrI
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_rI : ρc ≤ rI := min_le_right _ _
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
  have hP₀' : (0 : ℝ) ≤ B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n :=
    mul_nonneg (mul_nonneg hB₀ (by norm_num)) (by positivity)
  have hP₁' : (0 : ℝ) ≤ B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n :=
    mul_nonneg (mul_nonneg hB₁ (by norm_num)) (by positivity)
  -- ── the augmenting `GateSqControl`, from the concrete (1/4) near-isometry.
  have hgateSq : GateSqControl K
      (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
      (uniformInverseChart g gi hC hK) := by
    apply gateSqControl_of_flowBall K (uniformInverseChart g gi hC hK)
      (uniformFlowExp g gi hC hK) c rI (le_of_lt hc_rI)
    · -- `hinv`: the chart-inverse germ `W_q (φ_q v) = v` on `‖v‖ < c`.
      intro q hq v hv
      obtain ⟨hchartGerm, _⟩ := hchart q hq
      obtain ⟨hgerm, _⟩ := hchartGerm v (lt_trans hv hc_δ₀)
      simpa using hgerm.eq_of_nhds
    · -- `hdisp`: the two-sided (1/4) near-isometry yields the (3/2 ≤ 2) displacement budget.
      intro q hq v hv
      have h := hiso q hq v hv
      rw [abs_le] at h
      nlinarith [h.1, h.2, rncRadialSq_nonneg v,
        rncRadialSq_nonneg (uniformFlowExp g gi hC hK q v - q)]
  refine ⟨a, b, c, B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n,
    B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n, ha, hab, hbc, hP₀', hP₁', ?_, hgateSq⟩
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
    have hchartbd := hCUT τ hτ q hq v
    have hisoq := hiso q hq v hvrI
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
      (mul_nonneg hpoly0 (gaussDdim_nonneg _ _))

/-! ### (C+) — ★★★ the CURVED instantiation (`g = curvedRNCMetric κ`, `κ < 0`, seed `K = {0}`). -/

/-- **★★★ (C+) — `curvedRNC_gate_bundle`.**  THE CURVED on-gate width-4/3 `hgate` PLUS the
    `GateSqControl` certificate, PRODUCED at the seed `K = {0}`, given ONLY the standing carries
    `hChr` + `hw`.  Curved suppliers discharged exactly as in J4-672/677.  NOT `a₁ = R/6`. -/
theorem curvedRNC_gate_bundle
    (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ)) :
    ∃ a b c P₀ P₁ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      (∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ ({(0 : Point n)} : Set (Point n)) → ∀ p : Point n,
        p ∈ closure ((fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
              '' Metric.ball (0 : Point n) c) q) →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                  '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) ∧
      GateSqControl ({(0 : Point n)} : Set (Point n))
        (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
            '' Metric.ball (0 : Point n) c)
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) := by
  classical
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
    fun a b e => QIQTH.GaussGaugeToHgauge.curvedRNCMetric_pd_zero κ a b e
  have hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => curvedRNCMetric κ y a b)) := by
    intro y
    rw [isUnit_matToCLM_iff (fun a b => curvedRNCMetric κ y a b), Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (curvedRNCMetric_det_pos κ hκ.le y).ne'
  have hframeK : ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ i j,
      curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0) := by
    intro q hq i j
    rw [Set.mem_singleton_iff.mp hq]; exact hg0 i j
  exact hgate_and_gateSq_flowball (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    hgnd hgsymm hinvF hframeK hw hdg0 hg0

/-! ### (U) — ★★★ THE UNIFICATION: pkg ∧ hEdom ∧ hAdom ∧ hWDom at ONE gate. -/

/-- **★★★ (U) — `curvedRNC_unified_gate_bounds`.**  THE WIDTH GATE-UNIFICATION (J4-680).  For the
    genuinely-curved witness `g^κ = curvedRNCMetric κ` (`κ < 0`) on the seed `K = {0}`, given ONLY the
    standing carries `hChr` + `hw` and a window cap `τ0fr > 0`, there is ONE gate `(a,b,c)` and one
    constant `C ≥ 0`, `A₀,A₁,CW ≥ 0`, `lam > 0`, such that the SAME gated van-Vleck witness
    `cW = vanVleckGatedWitness g^κ gi^κ hChr {0} (flow-ball c) a b` satisfies ALL FOUR capstone binders:

    * `hpkgBound` (width-2 all-`t'` heatOp): `∀ t' τ p q, 0<τ → τ≤t' →
        |heatOp g^κ gi^κ cW τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`;
    * `hEdom` (width-3/2 heatOp): `∀ τ>0, ∀ p q,
        |heatOp g^κ gi^κ cW τ p q| ≤ (E₀+E₁τ)·√(3/2)ⁿ·gaussDdim ((3/2)τ) (p−q)`;
    * `hAdom` (width-3/2 witness): `∀ τ>0, ∀ p q,
        |cW τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim ((3/2)τ) (p−q)`;
    * `hWDom` (frozen `p=0` window): `∀ τ∈(0,τ0fr], ∀ z, |cW τ 0 z| ≤ CW·gaussDdim (lam·τ) z`.

    All at the ONE gate.  `pkg` is a width-widening of `hEdom` (`gaussDdim_le_gaussDdim_chart` at
    `(3/2,2)` + affine→all-`t'` rescale); `hEdom` is the affine route-β bridge of the on-gate width-4/3
    `hgate`; `hAdom`/`hWDom` come from the `GateSqControl` produced at the SAME gate.  NOT `a₁ = R/6`. -/
theorem curvedRNC_unified_gate_bounds
    (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (τ0fr : ℝ) (hτ0fr : 0 < τ0fr) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ C : ℝ, 0 ≤ C ∧
      ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
      ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∃ CW lam : ℝ, 0 ≤ CW ∧ 0 < lam ∧
      -- the ONE gated witness `cW`, spelled with the literal flow-ball gate.
      (∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                  '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) ∧
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                  '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                '' Metric.ball (0 : Point n) c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ τ0fr → ∀ z : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
            (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                '' Metric.ball (0 : Point n) c) a b τ (0 : Point n) z|
          ≤ CW * gaussDdim (lam * τ) z) := by
  classical
  -- ── the curved gate bundle: (a,b,c), the width-4/3 `hgate`, and the `GateSqControl`.
  obtain ⟨a, b, c, P₀, P₁, ha, hab, hbc, hP₀, hP₁, hgate, hgateSq⟩ :=
    curvedRNC_gate_bundle κ hκ hChr hw
  -- abbreviations.
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
        '' Metric.ball (0 : Point n) c with hS
  -- ── (E) hEdom: the affine route-β bridge `4/3 quad → 3/2 Gaussian`.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    QIQTH.HgateAffineRepair.hEdom_vanVleck_of_hgate_affine
      (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
      S a b P₀ P₁ hP₀ hP₁ hgate
  -- ── (A) hAdom: the D1 recenter-of-domination from the GateSqControl.
  obtain ⟨A₀, A₁, hA₀, hA₁, hdom⟩ :=
    exists_D1_constants_of_gateSqControl (vanVleck (curvedRNCMetric κ))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
        (curvedRNCMetric κ) (curvedRNCInv κ)))
      a b (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
      ({(0 : Point n)} : Set (Point n)) S ha hab hw hgateSq
  -- the pkg width-2 constant.
  set S1 : ℝ := Real.sqrt (3 / 2) ^ n with hS1
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc
  have hS10 : (0 : ℝ) ≤ S1 := by rw [hS1]; positivity
  have hSc0 : (0 : ℝ) ≤ Sc := by rw [hSc]; positivity
  set Cpkg : ℝ := (E₀ + E₁) * S1 * Sc with hCpkg
  have hCpkg0 : (0 : ℝ) ≤ Cpkg := by
    rw [hCpkg]; exact mul_nonneg (mul_nonneg (add_nonneg hE₀ hE₁) hS10) hSc0
  refine ⟨a, b, c, ha, hab, hbc, Cpkg, hCpkg0, E₀, E₁, hE₀, hE₁, A₀, A₁, hA₀, hA₁,
    (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n, 3 / 2,
    mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ0fr.le)) (pow_nonneg (Real.sqrt_nonneg _) n),
    by norm_num, ?_, ?_, ?_, ?_⟩
  · -- ── (pkg) width-2 all-`t'`: width-widen hEdom (3/2 → 2) + affine → (1+t') rescale.
    intro t' τ p q hτ hτt
    have hE := hEdom τ hτ p q
    -- width-widening `gaussDdim (3/2·τ) (p-q) ≤ Sc · gaussDdim (2·τ) (p-q)`.
    have hwiden : gaussDdim (3 / 2 * τ) (p - q) ≤ Sc * gaussDdim (2 * τ) (p - q) := by
      have hchart := gaussDdim_le_gaussDdim_chart (n := n) (c := 3 / 2) (d := 2)
        (by norm_num) (by norm_num) hτ (v := p - q) (w := p - q)
        (by nlinarith [rncRadialSq_nonneg (p - q)])
      rw [hSc]; exact hchart
    have hbk : baseKernelW (2 : ℝ) (0 : ℝ) τ p q = gaussDdim (2 * τ) (p - q) :=
      baseKernelW_zero_apply (2 : ℝ) τ p q
    -- affine outer factor: `(E₀+E₁τ) ≤ (E₀+E₁)(1+t')`.
    have haff : E₀ + E₁ * τ ≤ (E₀ + E₁) * (1 + t') := by nlinarith [hE₁, hE₀, hτ, hτt, hτ.le]
    have hgnn : (0 : ℝ) ≤ gaussDdim (2 * τ) (p - q) := gaussDdim_nonneg _ _
    have hg32 : (0 : ℝ) ≤ gaussDdim (3 / 2 * τ) (p - q) := gaussDdim_nonneg _ _
    calc |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * S1 * gaussDdim (3 / 2 * τ) (p - q) := hE
        _ ≤ (E₀ + E₁ * τ) * S1 * (Sc * gaussDdim (2 * τ) (p - q)) := by
              apply mul_le_mul_of_nonneg_left hwiden
              exact mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hτ.le)) hS10
        _ = ((E₀ + E₁ * τ) * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by ring
        _ ≤ ((E₀ + E₁) * (1 + t') * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by
              apply mul_le_mul_of_nonneg_right _ hgnn
              apply mul_le_mul_of_nonneg_right haff
              exact mul_nonneg hS10 hSc0
        _ = (Cpkg * (1 + t')) * gaussDdim (2 * τ) (p - q) := by rw [hCpkg]; ring
        _ = (Cpkg * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by rw [hbk]
  · -- ── (hEdom) verbatim.
    intro τ hτ p q; exact hEdom τ hτ p q
  · -- ── (hAdom) definitionally the D1 conclusion.
    intro τ hτ p q; exact hdom τ p q hτ
  · -- ── (hWDom) the frozen `p = 0` window slice of hAdom.
    intro τ hτ hτle z
    have hz := hdom τ (0 : Point n) z hτ
    rw [zero_sub, gaussDdim_neg] at hz
    have hstep : (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n
        ≤ (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) n)
      have := mul_le_mul_of_nonneg_left hτle hA₁
      linarith
    calc |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b τ
              (0 : Point n) z|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z := hz
        _ ≤ (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z :=
            mul_le_mul_of_nonneg_right hstep (gaussDdim_nonneg _ _)

/-- **★ (S) — CURVED, NOT SECRETLY FLAT (cp466 gate).**  The witness underlying the unified bounds is
    genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal metric-Hessian trace (`Ric(0)`) is nonzero.
    The seed is `K = {0}` where `hframeK` holds by `curvedRNCMetric_zero` — no cp466 collision.  NOT
    `a₁ = R/6`. -/
theorem curvedRNC_unified_gate_bounds_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedUnifiedGateBounds

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedUnifiedGateBounds.hgate_and_gateSq_flowball
#print axioms QIQTH.CurvedUnifiedGateBounds.curvedRNC_gate_bundle
#print axioms QIQTH.CurvedUnifiedGateBounds.curvedRNC_unified_gate_bounds
#print axioms QIQTH.CurvedUnifiedGateBounds.curvedRNC_unified_gate_bounds_curved_satisfiable
