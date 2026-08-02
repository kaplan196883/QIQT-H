/-
  GatedWitnessPackage — J4-114 (A): the CERTIFICATE MERGE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  The `hEboundW` chain (`gatedWitnessN1_hEboundW_le_vanVleck_final`, `CoeffU1Fix.lean`) returns an
  OPAQUE `∃ S` — the gate set `S q = φ_q '' ball 0 c` is constructed by `.choose` deep inside
  `OrderOneGeometry.gatedWitnessN1_hEboundW_le_of_good`, so its geometric certificate (the near-isometry
  `GateSqControl`) cannot be recovered from the outside.  This file re-runs the `_of_good → _lin → final`
  composition with a STRENGTHENED conclusion, threading the extra facts THROUGH the layer where `S` is
  born, so ONE shared witness set `S` carries simultaneously:

    (1) `hEboundW_le`         — the `(0,t]`-restricted α=0 primitive (verbatim the landed capstone);
    (2) `GateSqControl K S W` — the near-isometry square-comparison certificate D1's Gaussian
                                domination consumes (`ConcreteDominations.gateSqControl_of_flowBall`
                                DISCHARGED inline for the concrete flow-ball gate);
    (3) `0 ∈ K → 0 ∈ S 0`     — the spatial-gate origin membership `hDH` needs;
    (4) the D1 domination      — `∃ A₀ A₁, |gatedKernel K S H₁ τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·G_{3/2}`
                                (from (2) via `exists_D1_constants_of_gateSqControl`);
    (5) `0 ∈ K → W 0 0 = 0`    — the chart-fixes-origin fact `hDH` needs (`uniformInverseChart_zero`).

  MERGE DEPTH.  Strengthened variants at TWO chain layers (`_of_good_pkg`, `_lin_pkg`) plus the
  capstone `gatedWitnessN1_package`.  The extra `hgood` conjuncts (per-`q` square-comparison + base
  membership) are discharged at the `_lin_pkg` layer, exactly where `c = (b+ρc)/2` and the flow-ball
  radii `δ₀`, `r₁` are in scope; `_of_good_pkg` re-exports them through `.choose_spec`.

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CoeffU1Fix
import QIQTH.ConcreteDominations
import QIQTH.CapstoneWiring
import QIQTH.GatedWitnessMeas

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (A1) — `_of_good_pkg`: the mixed-cover `hEboundW_le` PLUS `GateSqControl` + base membership. -/

/-- **★ J4-114 (A1) — the STRENGTHENED `_of_good`.**  `OrderOneGeometry.gatedWitnessN1_hEboundW_le_of_good`
    with the `hgood` existential body extended by TWO extra conjuncts — the per-`q` near-isometry
    square-comparison (`rncRadialSq (φ_q v − q) ≤ (3/2)·rncRadialSq v`) and the base-point membership
    (`q ∈ φ_q '' ball 0 c`) — and the conclusion extended to also return, for the SAME `.choose`-built
    gate `S q = φ_q '' ball 0 (cf q)`, the `GateSqControl K S W` certificate and `∀ q ∈ K, q ∈ S q`.
    The mixed-cover half is verbatim the original (`gatedKernel_hEboundW_le_of_mixedCover`); the two new
    conjuncts are re-exported from the `.choose_spec` of the extended `hgood`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_of_good_pkg (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∧ (∀ q ∈ K, q ∈ S q) := by
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
  refine ⟨fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q), ?_, ?_, ?_⟩
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

/-! ### (A2) — `_lin_pkg`: discharges the extended `hgood` at `c = (b+ρc)/2`. -/

/-- **★★ J4-114 (A2) — the STRENGTHENED `_lin`.**  `CoeffU1Fix.gatedWitnessN1_hEboundW_le_lin` re-run
    against `_of_good_pkg`: the four original `hgood` conjuncts are discharged VERBATIM (the (A) cutoff
    residual / (B) transport identity / chart transfer chain is residual-abstract), and the two NEW
    conjuncts — the per-`q` square comparison (from `uniformFlowExp_hdisp_ball`, `4/3 ≤ 3/2` slack) and
    the base membership (from `uniformFlowExp_zero`) — are discharged at the same radius `c = (b+ρc)/2`.
    The result exposes `GateSqControl` + base membership for the shared gate `S`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_lin_pkg (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∧ (∀ q ∈ K, q ∈ S q) := by
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
  apply gatedWitnessN1_hEboundW_le_of_good_pkg g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0 hB1'0 W
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
  · -- NEW: base-point membership `q ∈ φ_q '' ball 0 c` via `uniformFlowExp_zero`.
    exact ⟨0, by rw [mem_ball_zero_iff, norm_zero]; exact hc0, uniformFlowExp_zero g gi hC hK q hq⟩

/-! ### (A3) — `gatedWitnessN1_package`: the merged certificate for the concrete van-Vleck witness. -/

/-- **★★★★ J4-114 (A) CAPSTONE — `gatedWitnessN1_package`.**  The `N = 1` van-Vleck gated witness with
    ALL of the space-time convolution engine's per-witness inputs merged onto ONE shared gate `S`:
    the `(0,t]`-restricted `hEboundW_le` primitive (verbatim `gatedWitnessN1_hEboundW_le_vanVleck_final`),
    the `GateSqControl` near-isometry certificate, the origin gate membership `0 ∈ K → 0 ∈ S 0`, the D1
    pointwise Gaussian domination `∃ A₀ A₁, |gatedKernel K S H₁ τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·G_{3/2}` (from
    `GateSqControl` via `exists_D1_constants_of_gateSqControl`), and the chart-fixes-origin fact
    `0 ∈ K → W 0 0 = 0` (`uniformInverseChart_zero`).  Hypotheses are IDENTICAL to the landed capstone
    (geometry/gauge + all-`k` folded smoothness `hw` + the RNC gauge inputs `hdg0`/`hg0`).  This is what
    the D1/hDH consumers of the convolution engine ingest.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_package (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∧ GateSqControl K S (uniformInverseChart g gi hC hK)
      ∧ ((0 : Point n) ∈ K → (0 : Point n) ∈ S 0)
      ∧ (∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ (τ : ℝ) (p q : Point n), 0 < τ →
          |gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK)) τ p q|
            ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
      ∧ ((0 : Point n) ∈ K → uniformInverseChart g gi hC hK 0 0 = 0) := by
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  obtain ⟨a, b, C, ha, hab, hC0', S, hbound, hgate, hmemS⟩ :=
    gatedWitnessN1_hEboundW_le_lin_pkg g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
  refine ⟨a, b, C, ha, hab, hC0', S, hbound, hgate, ?_, ?_, ?_⟩
  · intro h0; exact hmemS 0 h0
  · exact exists_D1_constants_of_gateSqControl (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) K S
      ha hab hw hgate
  · intro h0; exact uniformInverseChart_zero g gi hC hK h0

/-! ### (B) — D2: the Levi-series domination `|leviSeries E| ≤ C_L(T)·baseKernelW 2 0` on `(0,T]`. -/

/-- **★★ J4-114 (B) — THE ABSTRACT LEVI-SERIES DOMINATION (D2).**  For a residual `E` with the
    `(0,T]`-restricted width-2 one-step bound and the carried per-step integrability, the SIGNED Levi
    series `leviSeries E = ∑' k, (−1)^(k+1)·iterE E (k+1)` is Gaussian-dominated on `(0,T]` by a single
    `τ`-uniform constant:
        `|leviSeries E τ p q| ≤ C_L·baseKernelW 2 0 τ p q`,   `C_L := ∑' k, C^(k+1)·modelCoeff 0 T (k+1)`.
    Route: `|∑'| ≤ ∑'|·|` (`norm_tsum_le_tsum_norm`), each term dominated by `C^(k+1)·iterKernelW 2 0
    (k+1)` (`iterConvW_bound_le`), the model sum factored (`iterKernelW_eq`, `tsum_mul_right`) into the
    `k`-constant Gaussian `gaussDdim (2τ)` = `baseKernelW 2 0`, and the model-coefficient sum bounded
    `τ ↦ T` termwise (`modelCoeff 0 τ (k+1) ≤ modelCoeff 0 T (k+1)`, monotone in the time via
    `Real.rpow_le_rpow`).  The `Γ`/factorial decay (`scaledModelCoeff_summable`) makes `C_L` finite.
    NOT `a₁ = R/6`. -/
theorem leviSeries_dominatedW_le (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 < T)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ τ p q, 0 < τ → τ ≤ T →
      |leviSeries E τ p q| ≤ C_L * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  classical
  -- The model-coefficient time-monotonicity `modelCoeff 0 τ (k+1) ≤ modelCoeff 0 T (k+1)`.
  have hmono : ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ k : ℕ,
      modelCoeff 0 τ (k + 1) ≤ modelCoeff 0 T (k + 1) := by
    intro τ hτ hτT k
    unfold modelCoeff
    have hAnn : (0 : ℝ) ≤ Real.Gamma (0 + 1) ^ (k + 1)
        / Real.Gamma (((k + 1 : ℕ) : ℝ) * (0 + 1)) :=
      div_nonneg (pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le _)
        (Real.Gamma_pos_of_pos (by positivity)).le
    have hexp : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (0 + 1) - 1 := by
      have : ((k + 1 : ℕ) : ℝ) * (0 + 1) - 1 = (k : ℝ) := by push_cast; ring
      rw [this]; exact Nat.cast_nonneg k
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hτ.le hτT hexp) hAnn
  refine ⟨∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 T (k + 1), ?_, ?_⟩
  · exact tsum_nonneg (fun k => mul_nonneg (pow_nonneg hC _)
      (modelCoeff_pos 0 T (by norm_num) hT (by omega)).le)
  · intro τ p q hτ hτT
    -- termwise iterated-convolution domination and the model summabilities.
    have hterm : ∀ k : ℕ, |iterE E (k + 1) τ p q|
        ≤ C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q :=
      fun k => iterConvW_bound_le E 2 0 C T hEbound hInt (k + 1) (by omega) τ hτ hτT p q
    have hmodelSum : Summable (fun k : ℕ => C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q) :=
      scaledIterKernelW_summable 2 0 τ C (by norm_num) le_rfl hτ hC p q
    have hAbsSum : Summable (fun k : ℕ => |iterE E (k + 1) τ p q|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm hmodelSum
    have hnormeq : (fun k : ℕ => ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖)
        = fun k : ℕ => |iterE E (k + 1) τ p q| := by
      funext k
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    -- (i) `|leviSeries| ≤ ∑' |iterE|`.
    have hstep1 : |leviSeries E τ p q| ≤ ∑' k : ℕ, |iterE E (k + 1) τ p q| := by
      simp only [leviSeries, ← Real.norm_eq_abs]
      calc ‖∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖
          ≤ ∑' k : ℕ, ‖(-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q‖ :=
            norm_tsum_le_tsum_norm (by rw [hnormeq]; exact hAbsSum)
        _ = ∑' k : ℕ, |iterE E (k + 1) τ p q| := by rw [hnormeq]
    -- (ii) `∑' |iterE| ≤ ∑' C^(k+1)·iterKernelW`.
    have hstep2 : ∑' k : ℕ, |iterE E (k + 1) τ p q|
        ≤ ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q :=
      hAbsSum.tsum_le_tsum hterm hmodelSum
    -- (iii) factor the model tsum through `iterKernelW_eq` and `tsum_mul_right`.
    have hfactor : ∀ k : ℕ, C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q
        = (C ^ (k + 1) * modelCoeff 0 τ (k + 1)) * gaussDdim (2 * τ) (p - q) := by
      intro k
      rw [iterKernelW_eq 2 0 (by norm_num) (by norm_num) τ hτ p q (by omega : 1 ≤ k + 1)]
      unfold modelCoeff; ring
    have hmodeltsum : ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q
        = (∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 τ (k + 1)) * gaussDdim (2 * τ) (p - q) := by
      rw [tsum_congr hfactor, tsum_mul_right]
    -- (iv) bound the model-coefficient tsum `τ ↦ T`.
    have hcoeffSumτ : Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff 0 τ (k + 1)) :=
      scaledModelCoeff_summable 0 τ C le_rfl hτ hC
    have hcoeffSumT : Summable (fun k : ℕ => C ^ (k + 1) * modelCoeff 0 T (k + 1)) :=
      scaledModelCoeff_summable 0 T C le_rfl hT hC
    have hcoeffbound : ∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 τ (k + 1)
        ≤ ∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 T (k + 1) :=
      hcoeffSumτ.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_left (hmono τ hτ hτT k) (pow_nonneg hC _))
        hcoeffSumT
    calc |leviSeries E τ p q|
        ≤ ∑' k : ℕ, |iterE E (k + 1) τ p q| := hstep1
      _ ≤ ∑' k : ℕ, C ^ (k + 1) * iterKernelW 2 0 (k + 1) τ p q := hstep2
      _ = (∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 τ (k + 1)) * gaussDdim (2 * τ) (p - q) :=
          hmodeltsum
      _ ≤ (∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 T (k + 1)) * gaussDdim (2 * τ) (p - q) :=
          mul_le_mul_of_nonneg_right hcoeffbound (gaussDdim_nonneg _ _)
      _ = (∑' k : ℕ, C ^ (k + 1) * modelCoeff 0 T (k + 1)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
          rw [baseKernelW_zero_apply]

/-- **★★★ J4-114 (B) — THE CONCRETE `N = 1` VAN-VLECK LEVI-SERIES DOMINATION (D2), CONDITIONAL ON
    `hEmeas`.**  From the SAME geometric/gauge/all-`k`-smoothness inputs as the landed capstone plus
    `1 ≤ n`, and for a fixed ceiling `T > 0`, there are cutoff radii `a < b`, a constant `C ≥ 0`, and a
    gate `S` such that the concrete gated van-Vleck witness residual `E` obeys the `(0,t]`-restricted
    α=0 bound and — GIVEN the single base joint strong measurability `hEmeas` of `E` (M1) — its Levi
    series is dominated on `(0,T]`:  `∃ C_L ≥ 0, ∀ τ p q, 0 < τ → τ ≤ T → |leviSeries E τ p q| ≤
    C_L·baseKernelW 2 0 τ p q`.  Route: `gatedWitnessN1_hEboundW_le_vanVleck_final` supplies the bound
    and the `(0,T]`-LOCAL family; `iterConvIntegrableW_of_locally_bound_baseMeas` (+ `hEzero` from
    `heatOp_gatedWitnessN1_eq_zero_of_nonpos`) supplies `hInt`; `leviSeries_dominatedW_le` concludes.
    The ONLY conditional input is `hEmeas` — exactly the M1 wall of `gatedWitnessN1_hInt_of_hEmeas`.
    NOT `a₁ = R/6`. -/
theorem leviSeries_gatedWitnessN1_dominated (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ (StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) w.1 w.2.1 w.2.2) →
          ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ τ p q, 0 < τ → τ ≤ T →
            |leviSeries (heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) a b
                (uniformInverseChart g gi hC hK)))) τ p q|
              ≤ C_L * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound⟩ :=
    gatedWitnessN1_hEboundW_le_vanVleck_final g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C, ha, hab, hC0, S, hbound, ?_⟩
  intro hEmeas
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK))) τ p q = 0 :=
    heatOp_gatedWitnessN1_eq_zero_of_nonpos g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)
  have hInt : IterConvIntegrableW (heatOp g gi (gatedKernel K S
      (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK)))) 2 0 (C * (1 + T)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
        fun τ p q hτ hτT' => hbound T' τ p q hτ hτT'⟩)
  exact leviSeries_dominatedW_le _ (C * (1 + T)) T
    (mul_nonneg hC0 (by linarith)) hT
    (fun τ p q hτ hτT => hbound T τ p q hτ hτT) hInt

end QIQTH.HeatResidualBound
