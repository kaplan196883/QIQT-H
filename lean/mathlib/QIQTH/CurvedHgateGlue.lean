/-
  CurvedHgateGlue — J4-677 (file 2 of 2): THE GLUING BRICK — the width-1 quadratic in-chart cutoff
  residual (file 1) glued through the chart transfer into the ON-GATE width-4/3 QUADRATIC AFFINE
  `hgate`, instantiated at the genuinely-curved witness, and composed to the curved width-3/2 `hEdom`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CHAIN THIS FILE CLOSES (ledger 298a9bc0 → J4-677).

      (file 1, CUT)  in-chart width-1 quadratic affine cutoff `N=1` residual
        → [transport identity + G2a in-gate transfer, per gate point `p = φ_q v`]
      (T)   `|heatOp g gi H_G τ p q| = |χ·∂_τP₁ − Δ_{g̃_q}(χ·P₁)|(v) ≤ (B₀+B₁τ)·quadPoly(r²_v/τ)·G_τ(v)`
        → [`chartTransfer_quad_from_nearIsometry` (banked, J4-362) with the CONCRETE two-sided (1/4)
           near-isometry `nearIsometry_concrete` (banked, J4-361) — NOT the one-sided 3/2 displacement]
      (G)   `≤ (P₀+P₁τ)·quadPoly(r²_z/τ)·G_{4/3·τ}(z)`,  `z = p−q`   —  THE ON-GATE `hgate`, AFFINE
        → [`hEdom_vanVleck_of_hgate_affine` (banked, J4-368) — the `4/3 < 3/2` width absorption]
      (E)   the width-3/2 `hEdom` ∃-shape `(E₀+E₁τ)·√(3/2)ⁿ·G_{3/2·τ}(p−q)`, ∀ p q.

  The affine `(P₀+P₁τ)` (NOT a τ-free `P`) is the honest Sol-#15 shape: the `N = 1` witness's
  `τ·R₀[u′]` branch genuinely grows linearly in `τ`, and the τ-uniform gate constant is UNSATISFIABLE
  (HgateAffineRepair header).  The affine bridge is banked; no τ-horizon is needed.

  ## DELIVERABLES.
    • (G)  `hgate_width43_quad_affine_flowball` — ★★ METRIC-AGNOSTIC: the on-gate width-4/3 QUADRATIC
           AFFINE `hgate` for the concrete van-Vleck gated witness at the flow-ball gate
           `S = fun z => φ_z '' ball 0 c`, PRODUCED (not carried) from the geometric supplier bundle.
    • (C)  `curvedRNC_hgate_width43_quad_affine` — ★★★ the CURVED instantiation (`g = curvedRNCMetric κ`,
           `κ < 0`, seed `K = {0}`): the exact `hgate` input of `curvedRNC_hEdom_of_width43_quad` /
           `hEdom_vanVleck_of_hgate_affine`, from the banked curved suppliers.
    • (E)  `curvedRNC_hEdom_width32_from_geometry` — ★★★ the COMPOSITION: the curved width-3/2 `hEdom`
           ∃-shape (`(E₀+E₁τ)·√(3/2)ⁿ·G_{3/2τ}`, ∀ τ>0, ∀ p q) for the curved van-Vleck gated witness,
           CLOSED from geometry (inputs: only `hChr` + `hw`, the standing smoothness carries).
    • (S)  `curvedRNC_hgate_width43_curved_satisfiable` — the cp466 `Ric(0) ≠ 0` gate re-export.

  ## WHAT REMAINS CARRIED (precise).
    • `hChr` — smoothness of the curved Christoffels (same carry as J4-672/675 and the whole curved
      tower; a smoothness fact about the explicit `curvedRNCMetric`, not a physics input).
    • `hw`  — smoothness of the curved van-Vleck folded amplitudes (same standing carry).
    • The gate parameters `(a, b, c)` and the gate `S` are PRODUCER-CHOSEN (∃-quantified), matching the
      ∃-shape every banked consumer takes; no smallness condition survives as an antecedent.
    • NO τ-horizon: the bound is ∀ τ > 0 (the affine outer factor absorbs the τ-growth).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  the WIDTH CHAIN feeding the `hAdom`/`hEdom` slot; the arrows themselves (`hDelta`, the
  differentiation-under-∫ families for `hDConv`/`hDuhamel`) are NOT touched and remain owed.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis (the curved witness gate
  is `K = {0}`, where `hframeK` holds by `curvedRNCMetric_zero` — no cp466 collision), no hypothesis
  equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Width1QuadCutoff
import QIQTH.ConstRadiusGateExport
import QIQTH.HrawNearIsometryConcrete
import QIQTH.HrawPreCollapse
import QIQTH.HgateAffineRepair
import QIQTH.CurvedRNCHeatOpDomPkg

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedHgateGlue

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (G) — ★★ the METRIC-AGNOSTIC on-gate width-4/3 quadratic affine `hgate` producer. -/

/-- **★★ (G) — `hgate_width43_quad_affine_flowball`.**  THE GLUE.  From the geometric supplier bundle
    alone (the SAME hypotheses as the banked width-2 package `gatedWitnessN1_package_open_CONSTRADIUS`),
    there are cutoff radii `0 < a < b`, a flow-ball gate radius `c > b`, and affine constants
    `P₀, P₁ ≥ 0` such that the concrete van-Vleck gated witness at the gate
    `S = fun z => φ_z '' ball 0 c` obeys the ON-GATE width-4/3 QUADRATIC AFFINE bound
        `∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
              ≤ (P₀ + P₁·τ)·(((r²/τ)² + r²/τ + 1)·gaussDdim ((4/3)·τ) (p−q))`   (`r² = rncRadialSq (p−q)`)
    — the EXACT `hgate` binder of `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine`.

    ROUTE.  In-gate (`p = φ_q v ∈ S q`): the G2a heat-operator transfer + the transport identity turn
    `heatOp` into the in-chart cutoff `N = 1` residual at `v`; the file-1 capstone
    `cutoffResidualN1_uniformFlow_width1_quad_affine` bounds it at the WIDTH-1 QUADRATIC envelope; the
    banked `chartTransfer_quad_from_nearIsometry` with the CONCRETE (1/4) two-sided near-isometry
    `nearIsometry_concrete` transfers it to the ambient width-4/3 QUADRATIC shape (constants
    `Pᵢ = Bᵢ·(25/16)·√(4/3)ⁿ`).  Frontier (`p ∈ closure (S q) \ S q`): the gate radius `c > b` puts the
    chart image outside the cutoff support, so the witness is locally zero and `heatOp = 0 ≤ RHS`.
    NOT `a₁ = R/6`. -/
theorem hgate_width43_quad_affine_flowball (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure ((fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) q) →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)) := by
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
  refine ⟨a, b, c, B₀ * (25 / 16) * Real.sqrt (4 / 3) ^ n,
    B₁ * (25 / 16) * Real.sqrt (4 / 3) ^ n, ha, hab, hbc, hP₀', hP₁', ?_⟩
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
      (mul_nonneg hpoly0 (gaussDdim_nonneg _ _))

/-! ### (C) — ★★★ the CURVED instantiation (`g = curvedRNCMetric κ`, `κ < 0`, seed `K = {0}`). -/

/-- **★★★ (C) — `curvedRNC_hgate_width43_quad_affine`.**  THE CURVED ON-GATE WIDTH-4/3 QUADRATIC AFFINE
    `hgate`, PRODUCED.  For the genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`,
    `Ric(0) = (n−1)κδ ≠ 0`) on the seed `K = {0}`, given ONLY the standing smoothness carries `hChr` +
    `hw`, there are gate parameters `0 < a < b < c` and affine constants `P₀, P₁ ≥ 0` with the ON-GATE
    bound at the flow-ball gate — the EXACT input the route-β bridge
    (`hEdom_vanVleck_of_hgate_affine` / `curvedRNC_hEdom_of_width43_quad`) consumes.  The geometry /
    gauge / nondegeneracy members are the banked curved suppliers, discharged exactly as in J4-672.
    NOT `a₁ = R/6`. -/
theorem curvedRNC_hgate_width43_quad_affine
    (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ)) :
    ∃ a b c P₀ P₁ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ ({(0 : Point n)} : Set (Point n)) → ∀ p : Point n,
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
                  * gaussDdim (4 / 3 * τ) (p - q)) := by
  classical
  -- ── the geometry / gauge members for `g^K` (all banked, exactly as in J4-672).
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
  exact hgate_width43_quad_affine_flowball (curvedRNCMetric κ) (curvedRNCInv κ) hg hChr
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    hgnd hgsymm hinvF hframeK hw hdg0 hg0

/-! ### (E) — ★★★ the COMPOSITION: the curved width-3/2 `hEdom` from geometry. -/

/-- **★★★ (E) — `curvedRNC_hEdom_width32_from_geometry`.**  THE CURVED WIDTH-3/2 `hEdom`, CLOSED FROM
    GEOMETRY.  For `g^K = curvedRNCMetric κ` (`κ < 0`) on the seed `K = {0}`, given ONLY the standing
    smoothness carries `hChr` + `hw`, there are gate parameters `0 < a < b < c` such that the concrete
    curved van-Vleck gated witness at the flow-ball gate obeys the width-3/2 `hEdom` ∃-shape
        `∃ E₀ E₁ ≥ 0, ∀ τ>0, ∀ p q,
            |heatOp g^K gi^K H_G τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`
    — the EXACT hardcoded `hAdom`-supplier shape (the object `hDaLimLU_from_labelled_v2` step (vii)
    consumes, previously the surviving labelled width carry).  Composition: (C) + the banked affine
    route-β bridge `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine` (the `4/3 < 3/2` absorption).
    The width chain feeding `hEdom` is hereby CLOSED from geometry; `hChr`/`hw` are the only carries.
    ⚠ NOT `a₁ = R/6`; the `hDConv`/`hDuhamel` ARROWS (`hDelta`, diff-under-∫) remain owed. -/
theorem curvedRNC_hEdom_width32_from_geometry
    (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ)) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
              (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
                  '' Metric.ball (0 : Point n) c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  obtain ⟨a, b, c, P₀, P₁, ha, hab, hbc, hP₀, hP₁, hgate⟩ :=
    curvedRNC_hgate_width43_quad_affine κ hκ hChr hw
  exact ⟨a, b, c, ha, hab, hbc,
    QIQTH.HgateAffineRepair.hEdom_vanVleck_of_hgate_affine
      (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
      (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
          '' Metric.ball (0 : Point n) c) a b P₀ P₁ hP₀ hP₁ hgate⟩

/-! ### (S) — the cp466 satisfiability gate. -/

/-- **★ (S) — CURVED, NOT SECRETLY FLAT (cp466 gate).**  The witness underlying (C)/(E) is genuinely
    curved: for `κ ≠ 0` and `n ≥ 2` the diagonal metric-Hessian trace (`Ric(0)`) is nonzero — so the
    produced `hgate`/`hEdom` are instantiated at a genuinely curved metric (`κ = −1`, `n = 2` ⊂
    `κ < 0`, `n ≥ 2`), NOT the flat `δ`.  Antecedent inhabitance: the seed is `K = {0}` where the frame
    condition holds by `curvedRNCMetric_zero` (no J4-548-style `hframeK` collision); `hκ : κ < 0` is
    inhabited (`κ = −1`); `hChr`/`hw` are the standing smoothness carries of the whole curved tower
    (J4-672/675), not new assumptions.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hgate_width43_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedHgateGlue

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedHgateGlue.hgate_width43_quad_affine_flowball
#print axioms QIQTH.CurvedHgateGlue.curvedRNC_hgate_width43_quad_affine
#print axioms QIQTH.CurvedHgateGlue.curvedRNC_hEdom_width32_from_geometry
#print axioms QIQTH.CurvedHgateGlue.curvedRNC_hgate_width43_curved_satisfiable
