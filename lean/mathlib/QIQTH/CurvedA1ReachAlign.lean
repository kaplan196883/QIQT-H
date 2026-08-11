/-
  CurvedA1ReachAlign — J4-599 (part 2): THE REACH ALIGNMENT — the J4-598 arithmetic residual
  `c < δ₀` CLOSED, turning `curved_hBdom_of_reach` into a REAL `curved_hBdom_unconditional`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-597 (`CurvedA1HBdom`) discharged `hBdom` (the width-2 Levi Gaussian domination for
  `g^K = curvedRNCMetric κ`, `κ < 0`) modulo the M1 measurability carry `hEmeas`; J4-598
  (`CurvedA1HEmeas`) closed the measurability CONTENT via the banked S1 chain but only for gate
  radii `c < δ₀(a,b)` (the jet reach, ∃-bound AFTER `(a,b)` in every supplier), while the pkg
  produces its own `c = (b+ρc)/2` — the OPEN reach antecedent `c < δ₀`.

  ── ★★ THE ALIGNMENT (this brick).  Two ingredients:
    (i)  `ReachRequant.tripleHEmeas_flowball_requant` (part 1) — the honest ∃∀-swap: the jet reach
         `δ₀ > 0` is `(a,b)`-INDEPENDENT in substance (audited: every supplier radius bottoms out
         in `(a,b)`-free geometry lemmas), so it is now available BEFORE the gate parameters.
    (ii) `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` (here) — the banked constant-radius
         width-2 defect-bound producer replayed with a PRESCRIBED extra radius ceiling `ε`:
         `ρc := min (min (min rN δ₀_chart) r₁) ε`, so the produced gate radius `c = (b+ρc)/2`
         additionally satisfies `c < ε`.  Shrinking `ρc` strictly PRESERVES every step of the
         original proof (all uses are of the form `c < ρc ≤ availability radius`; gates only
         shrink) — verified by line-for-line replay.
  Choosing `ε := δ₀(jet)` aligns the two ∃-chains: the pkg's own `c` satisfies `c < δ₀`, the
  J4-598 antecedent DISCHARGES, and `hBdom` holds with NO reach antecedent and NO `hEmeas`
  antecedent — modulo only the mainline-standard carried geometric inputs `hChr`/`hw`/`hu`
  (Christoffel smoothness, folded-coefficient smoothness, transport-coefficient smoothness —
  all labelled, all true `C^∞` facts of the smooth `g^K`).

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` — ★★ the (ii) replay: the J4-316 CONST
      producer with the extra prescribed ceiling `ε > 0` and the extra conclusion `c < ε`.
    • `curvedRNC_heatOp_dom_pkg_prescribed` — ★★ the J4-536 curved pkg with the same extra `ε`.
    • `curved_hBdom_unconditional` — ★★★ THE GOAL: for `κ < 0`, `1 ≤ n`, `T > 0`, GIVEN only
      {`hChr`, `hw`, `hu`}: ∃ gate parameters `0 < a < b < c` and `C_L ≥ 0` with the EXACT width-2
      `hBdom` binder on `(0,T]` — NO reach antecedent, NO `hEmeas` antecedent.
    • `curved_hInnerCont_of_meas` — ★★ the ladder consumption: the capstone's `hInnerCont`
      reduced to the THREE remaining raw carries `{hAdom, hmeas, hcont}` only (the `hBdom` and
      `hEmeas` slots both internally discharged).
    • `curved_reachAlign_satisfiable` — ★ non-vacuity: `g^K` genuinely curved (`∃ w, 1 < det`).

  ── ADVERSARIAL NOTES.  The produced gate parameters remain GENUINE: `0 < a < b < c` with
  `c < min(chart-reach, jet-reach)` — a small but INHABITED gate (the J4-596 builder and the
  capstone consume `a b c` as free parameters; nothing downstream needs `c` large).  The
  domination and measurability are about the genuinely-curved witness (`κ < 0`,
  `Ric(0) = n(n−1)κ ≠ 0`); no inequality is weakened or reversed in the replay.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`, and a₁ = R/6 remains CONDITIONAL even with the reach
  aligned: `hInnerCont` still owes `{hAdom (global witness domination), hmeas, hcont}`, and the
  curved capstone still owes the census/domination piles, the rest of the convergence trio,
  `hmassone`'s pre-ρ carriers, and the `hjets` residual.  Everything here is TRUE for `g^K`
  (`κ < 0`), DERIVED from PROVED machinery (NOT axiomatized, NOT the `a₁` conclusion); the `R/6`
  value is unaffected.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous
  hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.GatedWitnessPackage
import QIQTH.CurvedA1HContDom
import QIQTH.CurvedA1HBdom
import QIQTH.CurvedA1GateS1
import QIQTH.CurvedA1HEmeas
import QIQTH.ReachRequant

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.GateOpennessExport QIQTH.S1TripleHEmeasGate QIQTH.ConstRadiusGateExport
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.GaussGaugeToHgauge
open QIQTH.CurvedRNCHeatOpDomPkg
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CurvedA1ReachAlign

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (A1) — the CONST producer with a PRESCRIBED radius ceiling `ε`. -/

/-- **★★ J4-599 (A1) — `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed`.**  Line-for-line replay
    of the banked `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST` with ONE change: the
    internal availability radius is `ρc := min (min (min rN δ₀) r₁) ε` for a PRESCRIBED `ε > 0`, so
    the exposed constant gate radius `c = (b+ρc)/2` additionally satisfies `c < ε`.  Every step of
    the original proof is preserved (the radius only shrinks; each use is `c < ρc ≤` an
    availability radius).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_lin_CONST_prescribed
    (g gi : Point n → Fin n → Fin n → ℝ)
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
        ≤ C_c1 * rncRadial v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧ c < ε ∧
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K (fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c)
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ GateSqControl K (fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c)
          (uniformInverseChart g gi hC hK)
      ∧ (∀ q ∈ K, q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      ∧ (∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)) := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc_def
  have hSc0 : 0 ≤ Sc := by positivity
  -- ★ THE ONE CHANGE: intersect the availability radius with the prescribed ceiling `ε`.
  set ρc : ℝ := min (min (min rN δ₀) r₁) ε with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min (lt_min hrNpos hδ₀) hr₁pos) hε
  have hρc_rN : ρc ≤ rN :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρc_δ₀ : ρc ≤ δ₀ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρc_r₁ : ρc ≤ r₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_ε : ρc ≤ ε := min_le_right _ _
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB0, hB1, hAbound⟩ :=
    cutoffResidualN1_uniformFlow_narrow_mixed_below_lin g gi hg hC hK hgnd hgsymm
      hinvF hframeK Θ u hw ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1 ρc hρc
  set B₀' : ℝ := B₀ * Sc with hB0'_def
  set B₁' : ℝ := B₁ * Sc with hB1'_def
  have hB0'0 : 0 ≤ B₀' := by rw [hB0'_def]; positivity
  have hB1'0 : 0 ≤ B₁' := by rw [hB1'_def]; positivity
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  have hcε : c < ε := lt_of_lt_of_le hcρc hρc_ε
  -- the 7-conjunct field bundle, discharged UNIFORMLY at the single constant `c` (verbatim replay).
  have hgoodC : ∀ q ∈ K,
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (B₀' + B₁' * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c ∧
      (∀ v : Point n, ‖v‖ < c →
        rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (3 / 2 : ℝ) * rncRadialSq v) ∧
      q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c := by
    intro q hq
    obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ v hv
      have hvN : ‖v‖ < rN := lt_trans hv hc_rN
      have hvδ₀ : ‖v‖ < δ₀ := lt_trans hv hc_δ₀
      have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
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
          (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
          (uniformFlowExp g gi hC hK q v) := by
        have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
            (W q (uniformFlowExp g gi hC hK q v)) := by
          apply ContDiffAt.mul
          · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
        exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
      have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by
        simpa using hgerm.eq_of_nhds
      have hprofilegerm :
          (fun z => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ
              (uniformFlowExp g gi hC hK q z) q)
            =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
        filter_upwards [hgerm] with z hz
        have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
        simp only [globalCutoffParametrixWitnessN, hz']
      have hlap : laplaceBeltrami g gi
            (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ p q)
            (uniformFlowExp g gi hC hK q v)
          = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
        have hn := hnat
          (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
          q hq v hvN hg1 hf hU hGGi hGiG
        rw [← hn]
        exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
          (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
          _ _ v hprofilegerm
      have htransport :
          heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
              (uniformFlowExp g gi hC hK q v) q
            = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
        simp only [heatOp]
        have hterm1fun :
            (fun s => globalCutoffParametrixWitnessN 1 Θ u a b (W) s
                (uniformFlowExp g gi hC hK q v) q)
              = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
          funext s
          simp only [globalCutoffParametrixWitnessN, hpt]
        rw [hterm1fun, deriv_const_mul_field, hlap]
      rw [htransport]
      have hnarrow := hAbound τ hτ q hq v
      have htransfer :
          gaussDdim (3 / 2 * τ) v
            ≤ Real.sqrt (2 / (3 / 2)) ^ n
                * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
        gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
          (hdisp q hq v hvr₁)
      have hBτ0 : (0 : ℝ) ≤ B₀ + B₁ * τ := by positivity
      calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
                - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                    (uniformFlowPullbackMetricInv g gi hC hK q)
                    (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := hnarrow
        _ ≤ (B₀ + B₁ * τ) * (Sc * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
            rw [hSc_def]; exact mul_le_mul_of_nonneg_left htransfer hBτ0
        _ = (B₀' + B₁' * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
            rw [hB0'_def, hB1'_def]; ring
    · intro v hv
      have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
      simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
    · intro v hv
      have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
      exact (hchartGerm v hvδ₀).2.continuousAt
    · exact (hchartOC c hc0 hc_δ₀).1
    · exact (hchartOC c hc0 hc_δ₀).2
    · intro v hv
      have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
      have hd := hdisp q hq v hvr₁
      linarith [hd, rncRadialSq_nonneg v]
    · exact ⟨0, by rw [mem_ball_zero_iff, norm_zero]; exact hc0, uniformFlowExp_zero g gi hC hK q hq⟩
  have hpkg := gatedWitnessN1_hEboundW_le_of_good_CONST g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0
    hB1'0 W c hbc hgoodC
  exact ⟨a, b, max B₀' B₁', c, ha, hab, le_trans hB0'0 (le_max_left _ _), hbc, hcε,
    hpkg.1, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2⟩

/-! ### (A2) — the curved heatOp domination pkg with the prescribed ceiling. -/

/-- **★★ J4-599 (A2) — `curvedRNC_heatOp_dom_pkg_prescribed`.**  The J4-536 curved heatOp
    defect-kernel width-2 Gaussian domination pkg (`curvedRNC_heatOp_dom_pkg`), replayed through the
    prescribed-ceiling producer (A1): the produced gate radius additionally satisfies `c < ε` for
    ANY prescribed `ε > 0`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_heatOp_dom_pkg_prescribed
    (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
          (curvedRNCMetric K) (curvedRNCInv K))) k : Point n → ℝ))
    (T : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧ c < ε ∧
      (∀ (t' : ℝ), ∀ (τ : ℝ), ∀ (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric K) (curvedRNCInv K)
            (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) ∧
      (∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp (curvedRNCMetric K) (curvedRNCInv K)
            (vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
            τ (0 : Point n) z|
          ≤ (C * (1 + T)) * gaussDdim (2 * τ) (0 - z)) := by
  classical
  have hg : ∀ (a b : Fin n), ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric K y a b) :=
    fun a b => curvedRNCMetric_contDiff K a b
  have hgsymm : ∀ (y : Point n) a b, curvedRNCMetric K y a b = curvedRNCMetric K y b a :=
    fun y a b => curvedRNCMetric_symm K y a b
  have hinvF : ∀ (y : Point n) a b,
      (∑ σ, curvedRNCMetric K y a σ * curvedRNCInv K y σ b) = if a = b then (1 : ℝ) else 0 :=
    fun y a b => curvedRNCMetric_hinvF K hK.le y a b
  have hg0 : ∀ i j, curvedRNCMetric K (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
    fun i j => curvedRNCMetric_zero K i j
  have hdg0 : ∀ a b e, pd (fun y => curvedRNCMetric K y a b) e (0 : Point n) = 0 :=
    fun a b e => curvedRNCMetric_pd_zero K a b e
  have hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => curvedRNCMetric K y a b)) := by
    intro y
    rw [isUnit_matToCLM_iff (fun a b => curvedRNCMetric K y a b), Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (curvedRNCMetric_det_pos K hK.le y).ne'
  have hframeK : ∀ q ∈ ({(0 : Point n)} : Set (Point n)), ∀ i j,
      curvedRNCMetric K q i j = (if i = j then (1 : ℝ) else 0) := by
    intro q hq i j
    rw [Set.mem_singleton_iff.mp hq]; exact hg0 i j
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck (curvedRNCMetric K)) (curvedRNCMetric K) (curvedRNCInv K))
      (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric K))
      (fun j => transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
        (curvedRNCMetric K) (curvedRNCInv K)) (j + 1)) (hw 1)
  set ρc : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρc := lt_min hρ0 hρ1
  obtain ⟨a, b, C, c, ha, hab, hCnn, hbc, hcε, hbound, -, -, -⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST_prescribed (curvedRNCMetric K) (curvedRNCInv K) hg hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) hgnd hgsymm hinvF hframeK
      (vanVleck (curvedRNCMetric K))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
        (curvedRNCMetric K) (curvedRNCInv K)))
      hw ρc C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
      ε hε
  refine ⟨a, b, C, c, ha, hab, hCnn, hbc, hcε, ?_, ?_⟩
  · intro t' τ p q hτ hτle
    exact hbound t' τ p q hτ hτle
  · intro τ hτ hτle z
    have h := hbound T τ (0 : Point n) z hτ hτle
    rw [baseKernelW_zero_apply] at h
    exact h

/-! ### (A3) — ★★★ THE GOAL: `hBdom` with NO reach and NO `hEmeas` antecedent. -/

/-- **★★★ J4-599 (A3) — `curved_hBdom_unconditional`.**  THE REACH-ALIGNED `hBdom`: for the
    genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`), `1 ≤ n`, any ceiling `T > 0`,
    GIVEN only the mainline-standard carried geometric inputs {`hChr`, `hw`, `hu`}: there are gate
    parameters `0 < a < b < c` and `C_L ≥ 0` with the EXACT width-2 `hBdom` binder on `(0,T]` —
    NO jet-reach antecedent (`c < δ₀` discharged: the pkg radius is produced BELOW the
    requantified jet reach) and NO `hEmeas` antecedent (discharged by
    `ReachRequant.tripleHEmeas_flowball_requant` at the pkg's own parameters).
    Route: requantified jet reach `δ₀` (R13) → pkg with prescribed ceiling `ε := δ₀` (A2) →
    `hEmeas` at `(a,b,c)` since `c < δ₀` → `hEzero` + `hInt` + `leviSeries_dominatedW_le`
    (verbatim J4-597 assembly).  NOT `a₁ = R/6`. -/
theorem curved_hBdom_unconditional (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T : ℝ) (hT : 0 < T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
            s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y) := by
  classical
  have hn0 : 0 < n := by omega
  -- 1. the requantified jet reach for `g^K` — available BEFORE the gate parameters.
  obtain ⟨δjet, hδjet, hjet⟩ :=
    QIQTH.ReachRequant.tripleHEmeas_flowball_requant hn0 (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun a b => curvedRNCInv_contDiff κ hκ.le a b)
      (curvedRNCMetric_hgpos κ hκ.le)
      hu
      (fun i j => (curvedRNCInv_contDiff κ hκ.le i j).continuous.measurable)
      (fun k i j => (hChr k i j).continuous.measurable)
  -- 2. the pkg with the prescribed ceiling `ε := δjet` — so `c < δjet` BY CONSTRUCTION.
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hcδjet, hpkg, -⟩ :=
    curvedRNC_heatOp_dom_pkg_prescribed κ hκ hChr hw T δjet hδjet
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  -- 3. `hEmeas` at the pkg's OWN parameters — the reach antecedent DISCHARGES.
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
        w.1 w.2.1 w.2.2) :=
    hjet a b ha hab c hbc hcδjet
  -- 4. the J4-597 assembly (verbatim): `hEzero` → `hInt` → the D2 engine.
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
        τ p q = 0 :=
    heatOp_gatedWitnessN1_eq_zero_of_nonpos (curvedRNCMetric κ) (curvedRNCInv κ) hn
      ({(0 : Point n)} : Set (Point n))
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
      (vanVleck (curvedRNCMetric κ))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
        (curvedRNCMetric κ) (curvedRNCInv κ))) a b
      (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))))
  have hInt : IterConvIntegrableW
      (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b))
      (2 : ℝ) (0 : ℝ) (C * (1 + T)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
        fun τ p q hτ hτT' => hpkg T' τ p q hτ hτT'⟩)
  obtain ⟨C_L, hCL0, hdom⟩ :=
    leviSeries_dominatedW_le _ (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
      (fun τ p q hτ hτT => hpkg T τ p q hτ hτT) hInt
  refine ⟨C_L, hCL0, fun s hs hsT z y => ?_⟩
  have h := hdom s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

/-! ### (A4) — the ladder consumption: `hInnerCont` reduced to `{hAdom, hmeas, hcont}`. -/

/-- **★★ J4-599 (A4) — `curved_hInnerCont_of_meas`.**  THE CONSUMPTION CERTIFICATE, reach-aligned:
    the J4-596/597 `hInnerCont` ladder for `g^K` with BOTH the `hBdom` slot AND the `hEmeas` slot
    internally discharged — at ∃ gate parameters, given only the THREE remaining raw carries
    `{hAdom, hmeas, hcont}` at those parameters, the capstone's carried `hInnerCont` conclusion
    (the interior-time `ContinuousOn` of the inner space-time pairing on `Ioo 0 u`) HOLDS.
    After this brick the `hInnerCont` reduction owes exactly `{hAdom, hmeas, hcont}` — no reach,
    no measurability-wall member.  NOT `a₁ = R/6`. -/
theorem curved_hInnerCont_of_meas (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
      ∀ (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      (∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) →
      (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
              (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                  a b)) s z 0)
          (volume : Measure (Point n))) →
      (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
              (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                  a b)) s z 0) s₀) →
      ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b
            (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c)
                a b)) s z 0)
        (Set.Ioo 0 u) := by
  classical
  obtain ⟨a, b, c, ha, hab, hbc, C_L, hCL0, hBdom⟩ :=
    curved_hBdom_unconditional κ hκ hn hChr hw hu T hT
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  intro A₀ A₁ hA₀ hA₁ hAdom hmeas hcont
  exact QIQTH.CurvedA1HContDom.curved_hInnerCont_of_dominations κ hChr
    ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) a b c T U hUT
    A₀ A₁ C_L hA₀ hA₁ hCL0 hAdom hBdom hmeas hcont

/-! ### (A5) — non-vacuity. -/

/-- **★ J4-599 (A5) — `curved_reachAlign_satisfiable`.**  Non-vacuity of the witness: for `κ < 0`,
    `n ≥ 2`, `g^K = curvedRNCMetric κ` is genuinely curved (`∃ w, 1 < det g^K w`) — the aligned
    `hBdom`/`hInnerCont` are NOT secretly about the flat kernel.  Re-exports
    `CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_reachAlign_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  (QIQTH.CurvedA1HmassoneBound.curved_hmassoneBound_satisfiable κ hκ hn).2

end QIQTH.CurvedA1ReachAlign

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1ReachAlign

#print axioms gatedWitnessN1_hEboundW_le_lin_CONST_prescribed
#print axioms curvedRNC_heatOp_dom_pkg_prescribed
#print axioms curved_hBdom_unconditional
#print axioms curved_hInnerCont_of_meas
#print axioms curved_reachAlign_satisfiable

end AxiomChecks
