/-
  GateOpennessExport — J4-204: exporting gate-openness from the package chain, and the `∞`-capstone
  with the `hCH` (spatial-`C²`) carry additionally discharged.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It performs ONE
  further mechanical rewiring of the ALREADY-BANKED `∞`-capstone
  (`LeviCarriesAssembly.a1_R6_of_residue_inf_v3`, itself `OmegaHsrcC4cAudit.a1_R6_of_residue_inf` with
  the `hS0` gate-centre membership carry discharged):

    • `a1_R6_of_residue_inf_v4` — `a1_R6_of_residue_inf_v3` with the SPATIAL-`C²` witness-diagonal carry
      `hCH : ContDiffAt ℝ 2 (fun p ↦ vanVleckGatedWitness … t p 0) 0` DISCHARGED internally via
      `InftyRebaseCapstone.hCH_discharge_from_geometry`.  That discharge needs `hSopen : IsOpen (S 0)`
      for the package's gate `S` — a fact the LANDED package `GatedWitnessPackage.gatedWitnessN1_package`
      does NOT export (its `∃ S` exposes the bound + `GateSqControl` + base membership + D1 + chart-origin,
      but never openness).  Yet the openness IS present in the good-witness spec: the `hgood`
      existential body already carries `IsOpen (φ_q '' ball 0 c)` as its 5th conjunct, and the concrete
      gate is `S q = φ_q '' ball 0 (cf q)` with `cf q = (hgood q hq).choose`.  So this file RE-RUNS the
      `_of_good → _lin → package` merge with the openness clause threaded through as ONE extra export,
      exactly as J4-114 threaded base membership.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; each main std-3):

    • `gatedWitnessN1_hEboundW_le_of_good_pkg_open` — the `_of_good` merge, conclusion extended by
      `(∀ q ∈ K, IsOpen (S q))`, read off the `hgood` openness conjunct via `.choose_spec` (verbatim
      the base-membership export pattern).
    • `gatedWitnessN1_hEboundW_le_lin_pkg_open` — the `_lin` merge, threading the openness export; the
      `hgood` requirement is UNCHANGED (openness is already one of its seven conjuncts, discharged at
      `c = (b+ρc)/2` via `(hchartOC c hc0 hc_δ₀).1`).
    • `gatedWitnessN1_package_open` — the concrete van-Vleck package exporting, for the shared gate `S`,
      the `(0,t]`-restricted bound (verbatim) PLUS `(0 ∈ K → 0 ∈ S 0)` AND `(0 ∈ K → IsOpen (S 0))`.
    • `a1_R6_of_residue_inf_v4` — the `∞`-capstone with `hS0` AND `hCH` discharged; the inner carry
      list drops to `{hInt, hDuhamel, hInter, hDConv, hCConv}` (v3's list MINUS `hCH`).  It adds the two
      geometric inputs `hCH_discharge_from_geometry` requires that v3 lacked — `hgiC` (inverse-metric
      `C^∞` smoothness) and `hgpos` (positive metric determinant) — both satisfiable geometry, never the
      conclusion, never vacuous.

  DEFINITIVE `v4` RESIDUE (the inner carry list AFTER this brick):
      `{hInt, hDuhamel, hInter, hDConv, hCConv}`  — exactly `v3`'s inner list MINUS `hCH`.

  No conclusion-in-disguise; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.
  The mains are std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedWitnessPackage
import QIQTH.LeviCarriesAssembly
import QIQTH.InftyRebaseCapstone

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.OmegaHsrcC4cAudit QIQTH.InftyRebaseCapstone
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.GateOpennessExport

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (A1′) — `_of_good_pkg_open`: the `_of_good_pkg` merge PLUS the gate-openness export. -/

/-- **★ J4-204 (A1′) — the STRENGTHENED `_of_good` WITH OPENNESS.**  Verbatim
    `GatedWitnessPackage.gatedWitnessN1_hEboundW_le_of_good_pkg`, with the conclusion extended by ONE
    extra export — `(∀ q ∈ K, IsOpen (S q))` — for the SAME `.choose`-built gate
    `S q = φ_q '' ball 0 (cf q)`.  The openness is the 5th `hgood` conjunct, re-exported through
    `.choose_spec` (verbatim the base-membership export pattern).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_of_good_pkg_open (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b B₀ B₁ : ℝ) (ha : 0 < a) (hab : a < b) (hB0 : 0 ≤ B₀) (hB1 : 0 ≤ B₁)
    (W : Point n → Point n → Point n)
    (hgood : ∀ q ∈ K, ∃ c : ℝ, b < c ∧
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c ∧
      (∀ v : Point n, ‖v‖ < c →
        rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (3 / 2 : ℝ) * rncRadialSq v) ∧
      q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) :
    ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (W))) τ p q|
          ≤ (max B₀ B₁ * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ GateSqControl K S W
      ∧ (∀ q ∈ K, q ∈ S q)
      ∧ (∀ q ∈ K, IsOpen (S q)) := by
  classical
  set H : ℝ → Point n → Point n → ℝ :=
    globalCutoffParametrixWitnessN 1 Θ u a b (W) with hHdef
  set cf : Point n → ℝ := fun q => if hq : q ∈ K then (hgood q hq).choose else 0 with hcfdef
  have hCmax0 : (0 : ℝ) ≤ max B₀ B₁ := le_trans hB0 (le_max_left _ _)
  -- the 3-leg MIXED cover for the concrete gate `S q := φ_q '' (ball 0 (cf q))`.
  have hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
      ((fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)) q ∈ nhds p
          ∧ |heatOp g gi H τ p q|
            ≤ max B₀ B₁ * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)) q}
          ∈ nhds p)
      ∨ ((fun s => H s p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ))) := by
    intro q hq τ hτ p
    have hcfq : cf q = (hgood q hq).choose := dif_pos hq
    set c₀ : ℝ := (hgood q hq).choose with hc0def
    obtain ⟨hbc, hbnd, hinv, hcont, hopen, hclos, _, _⟩ := (hgood q hq).choose_spec
    have hSqeq : uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)
        = uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀ := by rw [hcfq]
    have hb0 : 0 < b := lt_trans ha hab
    simp only [hSqeq]
    by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀
    · -- LEG 1 (in-gate): transfer the mixed in-chart bound, converting to the MIXED `baseKernelW` shape.
      refine Or.inl ⟨hopen.mem_nhds hpS, ?_⟩
      obtain ⟨w, hw, hwp⟩ := hpS
      rw [mem_ball_zero_iff] at hw
      have hb := hbnd τ hτ w hw
      rw [hwp] at hb
      rw [baseKernelW_one_eq_tau_mul, baseKernelW_zero_apply]
      have hG : (0 : ℝ) ≤ gaussDdim (2 * τ) (p - q) := gaussDdim_nonneg _ _
      have hle : B₀ + B₁ * τ ≤ max B₀ B₁ * (1 + τ) := by
        have h2 : B₁ ≤ max B₀ B₁ := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_right h2 hτ.le, le_max_left B₀ B₁]
      calc |heatOp g gi H τ p q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (2 * τ) (p - q) := hb
        _ ≤ (max B₀ B₁ * (1 + τ)) * gaussDdim (2 * τ) (p - q) :=
            mul_le_mul_of_nonneg_right hle hG
        _ = max B₀ B₁ * (gaussDdim (2 * τ) (p - q) + τ * gaussDdim (2 * τ) (p - q)) := by ring
    · by_cases hpcl : p ∈ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀)
      · -- LEG 3 (frontier collar): the cutoff of `W_q` vanishes near `p`, zeroing the whole witness.
        obtain ⟨w', hw', hw'p⟩ := hclos hpcl
        rw [mem_closedBall_zero_iff] at hw'
        have hnormeq : ‖w'‖ = c₀ := by
          rcases lt_or_eq_of_le hw' with hlt | heq
          · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
              p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) hpS
          · exact heq
        have hWp : W q p = w' := by
          rw [← hw'p]; exact hinv w' hw'
        have hb2 : b ^ 2 < rncRadialSq (W q p) := by
          rw [hWp]
          have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
            have hle := norm_le_rncRadial w'
            have := rncRadial_sq w'
            nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, this]
          nlinarith [h1, hnormeq, hb0, hbc]
        have hcontp : ContinuousAt (W q) p := by
          rw [← hw'p]; exact hcont w' hw'
        have hNnhds :
            (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
          hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · refine Filter.Eventually.of_forall (fun s => ?_)
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hb2), zero_mul]
        · filter_upwards [hNnhds] with p' hp'
          have hp'2 : b ^ 2 < rncRadialSq (W q p') := hp'
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hp'2), zero_mul]
      · -- LEG 2 (off-gate): the complement of the closed closure is a neighborhood.
        refine Or.inr (Or.inl ?_)
        have hsub : (closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀))ᶜ
            ⊆ {p' : Point n | p' ∉ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀} :=
          fun x hx hxS => hx (subset_closure hxS)
        exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hpcl) hsub
  refine ⟨fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q), ?_, ?_, ?_, ?_⟩
  · intro t
    exact gatedKernel_hEboundW_le_of_mixedCover g gi K
      (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)) H (max B₀ B₁) t hCmax0 hcover
  · -- `GateSqControl` for the concrete `.choose`-built gate, from the extended `hgood` conjunct.
    intro q hq p hp
    have hcfq : cf q = (hgood q hq).choose := dif_pos hq
    obtain ⟨_, _, hinv, _, _, _, hsqc, _⟩ := (hgood q hq).choose_spec
    obtain ⟨v, hvmem, hvp⟩ := hp
    rw [mem_ball_zero_iff, hcfq] at hvmem
    have hWp : W q p = v := by rw [← hvp]; exact hinv v (le_of_lt hvmem)
    calc rncRadialSq (p - q)
        = rncRadialSq (uniformFlowExp g gi hC hK q v - q) := by rw [hvp]
      _ ≤ (3 / 2 : ℝ) * rncRadialSq v := hsqc v hvmem
      _ = (3 / 2 : ℝ) * rncRadialSq (W q p) := by rw [hWp]
  · -- base-point membership `∀ q ∈ K, q ∈ S q`.
    intro q hq
    have hcfq : cf q = (hgood q hq).choose := dif_pos hq
    obtain ⟨_, _, _, _, _, _, _, hmem⟩ := (hgood q hq).choose_spec
    show q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)
    rw [hcfq]; exact hmem
  · -- NEW: gate-openness export `∀ q ∈ K, IsOpen (S q)`.
    intro q hq
    have hcfq : cf q = (hgood q hq).choose := dif_pos hq
    obtain ⟨_, _, _, _, hopen, _, _, _⟩ := (hgood q hq).choose_spec
    show IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q))
    rw [hcfq]; exact hopen

/-! ### (A2′) — `_lin_pkg_open`: discharges `hgood` at `c = (b+ρc)/2`, threading the openness export. -/

/-- **★★ J4-204 (A2′) — the STRENGTHENED `_lin` WITH OPENNESS.**  Verbatim
    `GatedWitnessPackage.gatedWitnessN1_hEboundW_le_lin_pkg`, threading the extra openness export
    through `_of_good_pkg_open`.  The `hgood` requirement is UNCHANGED (openness is already one of its
    seven conjuncts, discharged at `c = (b+ρc)/2` via `(hchartOC c hc0 hc_δ₀).1`).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_lin_pkg_open (g gi : Point n → Fin n → Fin n → ℝ)
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
        ≤ C_c1 * rncRadial v) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ GateSqControl K S (uniformInverseChart g gi hC hK)
      ∧ (∀ q ∈ K, q ∈ S q)
      ∧ (∀ q ∈ K, IsOpen (S q)) := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc_def
  have hSc0 : 0 ≤ Sc := by positivity
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB0, hB1, hAbound⟩ :=
    cutoffResidualN1_uniformFlow_narrow_mixed_below_lin g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1 ρc hρc
  set B₀' : ℝ := B₀ * Sc with hB0'_def
  set B₁' : ℝ := B₁ * Sc with hB1'_def
  have hB0'0 : 0 ≤ B₀' := by rw [hB0'_def]; positivity
  have hB1'0 : 0 ≤ B₁' := by rw [hB1'_def]; positivity
  refine ⟨a, b, max B₀' B₁', ha, hab, le_trans hB0'0 (le_max_left _ _), ?_⟩
  apply gatedWitnessN1_hEboundW_le_of_good_pkg_open g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0 hB1'0 W
  intro q hq
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  refine ⟨c, hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- NEW: the per-`q` near-isometry square comparison at radius `c` (`4/3 ≤ 3/2` slack).
    intro v hv
    have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
    have hd := hdisp q hq v hvr₁
    linarith [hd, rncRadialSq_nonneg v]
  · -- base-point membership `q ∈ φ_q '' ball 0 c` via `uniformFlowExp_zero`.
    exact ⟨0, by rw [mem_ball_zero_iff, norm_zero]; exact hc0, uniformFlowExp_zero g gi hC hK q hq⟩

/-! ### (A3′) — `gatedWitnessN1_package_open`: the merged certificate exporting gate-openness. -/

/-- **★★★ J4-204 (A3′) CAPSTONE — `gatedWitnessN1_package_open`.**  The `N = 1` van-Vleck gated
    witness with the `(0,t]`-restricted `hEboundW_le` bound (verbatim), the origin gate membership
    `0 ∈ K → 0 ∈ S 0`, AND — the NEW export — the origin gate-openness `0 ∈ K → IsOpen (S 0)`, all on
    ONE shared gate `S`.  This is the minimal set of exports the `hCH`-discharge consumer needs; the
    `GateSqControl` / D1 / chart-origin exports of the landed `gatedWitnessN1_package` are not required
    by that consumer, so they are dropped here.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_package_open (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K → (0 : Point n) ∈ S 0)
      ∧ ((0 : Point n) ∈ K → IsOpen (S 0)) := by
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  obtain ⟨a, b, C, ha, hab, hC0', S, hbound, hgate, hmemS, hopenS⟩ :=
    gatedWitnessN1_hEboundW_le_lin_pkg_open g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
  refine ⟨a, b, C, ha, hab, hC0', S, hbound, ?_, ?_⟩
  · intro h0; exact hmemS 0 h0
  · intro h0; exact hopenS 0 h0

/-! ### (B) — the `∞`-capstone with `hS0` AND `hCH` discharged. -/

/-- **★★★ J4-204 — `a1_R6_of_residue_inf_v4`.**  `LeviCarriesAssembly.a1_R6_of_residue_inf_v3` with the
    spatial-`C²` witness-diagonal carry `hCH : ContDiffAt ℝ 2 (fun p ↦ vanVleckGatedWitness … t p 0) 0`
    DISCHARGED internally via `InftyRebaseCapstone.hCH_discharge_from_geometry`.  The gate `S` is sourced
    from `gatedWitnessN1_package_open`, which additionally exports `0 ∈ K → IsOpen (S 0)`; with `hK0`
    this supplies the `hSopen` the `hCH`-discharge needs (the landed package could not).  Relative to
    `v3` the inner carry list is shorter by exactly the `hCH` slot; the remaining inner carries
    `{hInt, hDuhamel, hInter, hDConv, hCConv}` are the Levi/Duhamel interface + the single L2-facade
    field-`C²` slot (satisfiable interface assembly, never the conclusion).  Two geometric inputs the
    discharge requires and `v3` lacked are added — `hgiC` (inverse-metric `C^∞`) and `hgpos` (positive
    metric determinant) — both satisfiable geometry, neither vacuous nor the conclusion.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem a1_R6_of_residue_inf_v4 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      (IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C' →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
        (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
                t 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t →
        ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
            (0 : Point n) →
        heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
        ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                                t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C * (1 + t), S, ha, hab, mul_nonneg hC0 (by linarith), ?_⟩
  intro hInt hDuhamel hInter hDConv hCConv
  -- ★ discharge 1: the gate-centre membership is FREE from the package's exported field.
  have hS0 : (0 : Point n) ∈ S 0 := hmemS0 hK0
  -- ★ discharge 2: gate-openness at the centre, FREE from the NEW exported field.
  have hSopen : IsOpen (S 0) := hopenS0 hK0
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ discharge 3: the spatial-`C²` witness-diagonal slot, from the `C^∞` geometry alone.
  have hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) :=
    hCH_discharge_from_geometry g gi hChr hK S a b t hK0 hS0 hSopen hg hgiC hgpos hg0'
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτt
    exact hbound t τ p q hτ hτt
  exact a1_R6_of_residue_inf g gi Ric t ht (C * (1 + t)) (mul_nonneg hC0 (by linarith))
    hChr hK S a b ha hab hK0 hS0 (vanVleckGatedWitness g gi hChr hK S a b) rfl
    hg hg0' hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.GateOpennessExport

section AxiomChecks
open QIQTH.GateOpennessExport
#print axioms gatedWitnessN1_hEboundW_le_of_good_pkg_open
#print axioms gatedWitnessN1_hEboundW_le_lin_pkg_open
#print axioms gatedWitnessN1_package_open
#print axioms a1_R6_of_residue_inf_v4
end AxiomChecks
