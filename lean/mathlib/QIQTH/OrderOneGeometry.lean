/-
  OrderOneGeometry — J4-106: the LAST GEOMETRIC LEG of the `N = 1` rebuild — the middle geometry
  connecting the in-chart `N = 1` residual bound (J4-105 T1, `uniformResidualN1_narrow_mixed`) to the
  MIXED-α gated cover consumed by J4-105's T4 (`gatedKernel_hEboundW_le_of_mixedCover`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE.

  (B) THE `N = 1` RESIDUAL TRANSPORT IDENTITY.  The `N = 1` mirrors of
  `GlobalResidualWitness.heatOp_globalWitness_eq_recentred_inChart` and
  `RadiusOrdering.heatOp_globalWitness_eq_recentred_inChart_hoisted`, with
  `globalCutoffParametrixWitnessN 1` in place of `globalCutoffParametrixWitness` and `heatParametrix 1`
  in the recentred bracket.  The N=0 proofs keep the profile `heatParametrix 0` fully ABSTRACT (only
  `simp only [globalCutoffParametrixWitness, …]` unfolds the witness def), so the N=1 mirrors are
  near-verbatim (the witness def is the only change).

  (A) THE `N = 1` CUTOFF-RESIDUAL MIXED BOUND.  The `N = 1` analogue of
  `WidthMarginEngine.cutoffResidual_uniformFlow_unconditional_tau_narrow` /
  `RadiusOrdering.cutoffResidual_uniformFlow_unconditional_tau_narrow_below`.  The cutoff residual of the
  order-1 parametrix `H₁ = gauss·(w₀ + τ·w₁)` obeys the MIXED bound
      `|χ·∂_τH₁ − Δ_{g̃_q}(χ·H₁)| ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`
  uniformly over `q ∈ K`, `τ > 0`.  ROUTE: fire the PROFILE-INDEPENDENT narrow cutoff engine
  `cutoffResidual_narrow_tauUniform_engine` at fixed `τ` with the AFFINE-in-`τ` constants
  `C := C₀+C₁τ` (near residual, J4-105 T1), `Kcof := (Kcof0+τKcof1)·√(3/2)ⁿ` (annulus value at the mixed
  cofactor), `Kder := Kder0+τKder1` (annulus derivative at the mixed cofactor); the engine constant
  `C + Kcof·Kc2 + 2n²KgKc1Kder` is then affine in `τ`, delivering the `B₀+B₁τ` shape.

  No `sorry`, no new axioms, no `expRho`, no vacuous hypotheses; the genuine load-bearing inputs are the
  firewalled `totalRadialO1_coeff` bounds at the two profiles `u`, `u'` (same as J4-105 T1) and the
  folded-coefficient smoothness `hw`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OrderOneTower
import QIQTH.RadiusOrdering
import QIQTH.GlobalResidualWitness
import QIQTH.PullbackNaturalityLocal
import QIQTH.VanVleckCancellation

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (B) — the `N = 1` residual transport identity, in-chart and hoisted. -/

/-- **★ J4-106 (B) — THE `N = 1` RESIDUAL TRANSPORT IDENTITY (in-chart).**  The `N = 1` mirror of
    `heatOp_globalWitness_eq_recentred_inChart`: the global-chart heat operator of the order-1 witness
    `globalCutoffParametrixWitnessN 1` at the in-chart point `p = φ_q v` equals the recentred cutoff
    residual bracket AT ORDER 1.  Proof near-verbatim (only the witness def / `heatParametrix 1`
    change; the profile stays abstract). -/
theorem heatOp_globalWitnessN1_eq_recentred_inChart
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) (τ : ℝ) (q : Point n) (hq : q ∈ K) :
    ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
      (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
      (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q v) →
      IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
      (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
      (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
      heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) τ
          (uniformFlowExp g gi hC hK q v) q
        = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
  obtain ⟨r₀, hr₀pos, hnat⟩ := laplaceBeltrami_uniformFlow_naturality g gi hC hK hgsymm
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q)
  refine ⟨r₀, hr₀pos, ?_⟩
  intro v hv hgerm hg1 hf hU hGGi hGiG
  have hpt : Vmap q (uniformFlowExp g gi hC hK q v) = v := by
    simpa using hgerm.eq_of_nhds
  have hprofilegerm :
      (fun z => (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q z))
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : Vmap q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
    have hn := hnat q hq v hv hg1 hf hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  simp only [heatOp]
  have hterm1fun :
      (fun s => globalCutoffParametrixWitnessN 1 Θ u a b Vmap s (uniformFlowExp g gi hC hK q v) q)
        = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
    funext s
    simp only [globalCutoffParametrixWitnessN, hpt]
  rw [hterm1fun, deriv_const_mul_field, hlap]

/-- **★ J4-106 (B) — THE `N = 1` RESIDUAL TRANSPORT IDENTITY, `r₀` HOISTED.**  The `N = 1` mirror of
    `heatOp_globalWitness_eq_recentred_inChart_hoisted`: the single τ-free radius `r₀` (from the `∀ f`
    naturality) is shared by ALL `τ`, giving the `∀ τ` transport identity for the order-1 witness.
    Proof near-verbatim. -/
theorem heatOp_globalWitnessN1_eq_recentred_inChart_hoisted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) :
    ∃ r₀ > (0 : ℝ), ∀ (τ : ℝ) (q : Point n), q ∈ K → ∀ v : Point n, ‖v‖ < r₀ →
      (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
      (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q v) →
      IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
      (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
      (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
      heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) τ
          (uniformFlowExp g gi hC hK q v) q
        = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
  obtain ⟨r₀, hr₀pos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  refine ⟨r₀, hr₀pos, ?_⟩
  intro τ q hq v hv hgerm hg1 hf hU hGGi hGiG
  have hpt : Vmap q (uniformFlowExp g gi hC hK q v) = v := by
    simpa using hgerm.eq_of_nhds
  have hprofilegerm :
      (fun z => (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q z))
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : Vmap q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
    have hn := hnat (fun x => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ x q) q hq v hv hg1 hf
      hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  simp only [heatOp]
  have hterm1fun :
      (fun s => globalCutoffParametrixWitnessN 1 Θ u a b Vmap s (uniformFlowExp g gi hC hK q v) q)
        = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
    funext s
    simp only [globalCutoffParametrixWitnessN, hpt]
  rw [hterm1fun, deriv_const_mul_field, hlap]

/-! ### (A) — the `N = 1` cutoff-residual MIXED bound at the narrow width `G_{3/2}`. -/

/-- **★ J4-106 (A) — THE `N = 1` CUTOFF-RESIDUAL MIXED BOUND, re-run below an arbitrary ceiling `ρc`.**
    The `N = 1` analogue of `cutoffResidual_uniformFlow_unconditional_tau_narrow_below`: the cutoff
    residual of the order-1 parametrix `H₁ = gauss·(w₀ + τ·w₁)` on the pullback metric `g̃_q` obeys the
    MIXED bound
        `|χ·∂_τH₁ − Δ_{g̃_q}(χ·H₁)| ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`
    uniformly over `τ > 0`, `q ∈ K`, with the cutoff far-radius `b < ρc`.  ROUTE: fire the
    PROFILE-INDEPENDENT narrow engine `cutoffResidual_narrow_tauUniform_engine` at fixed `τ` with the
    AFFINE-in-`τ` constants `C := B₀ᵣ+B₁ᵣτ` (near residual, J4-105 T1 `uniformResidualN1_narrow_mixed`),
    `Kcof := (Kcof0+τKcof1)·√(3/2)ⁿ` (annulus VALUE at the mixed cofactor `w₀+τw₁`, via
    `parametrixCofactor_value_annulus_tauUniform` at `w₀` and `w₁`), and `Kder := Kder0+τKder1` (annulus
    DERIVATIVE at the mixed cofactor, via `parametrixCofactor_deriv_annulus_narrow_tauUniform` at `w₀` and
    `w₁` with `pd` distributed over the split `H₁ = gauss·w₀ + τ·gauss·w₁`).  The engine constant
    `C + Kcof·Kc2 + 2n²KgKc1Kder` is then affine in `τ`, delivering `B₀+B₁τ`.  Genuine load-bearing
    inputs: the firewalled `totalRadialO1_coeff` bounds at the two profiles (`hCoeffU0`/`hCoeffU1`, as in
    J4-105 T1) and the folded-coefficient smoothness `hw`.  NOT `a₁ = R/6`. -/
theorem cutoffResidualN1_uniformFlow_narrow_mixed_below (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hCoeffU1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadialSq v)
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B₀ B₁ : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
        |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by
  classical
  -- (i) the J4-105 T1 mixed residual bound (the near packet).
  obtain ⟨ρ_u, hρ_u0, Bᵣ0, Bᵣ1, hBᵣ0, hBᵣ1, hResU1⟩ :=
    uniformResidualN1_narrow_mixed g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffU1
  -- (ii) profile-independent annulus suppliers.
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  set bN : ℝ := ρ_u / 2 with hbN_def
  have hbN0 : 0 < bN := by rw [hbN_def]; linarith
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min (min bN (rmin / 2)) (ρc / 2) with hb_def
  have hb0 : 0 < b := lt_min (lt_min hbN0 (by linarith)) (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_lt_ρc : b < ρc := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_le_bN : b ≤ bN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hb_lt_rmin : b < rmin :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  -- (iii) annulus VALUE sups at the two cofactors `w₀`, `w₁`.
  obtain ⟨Kcof0, hKcof00, hHann0U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) (hw 0).continuous
  obtain ⟨Kcof1, hKcof10, hHann1U⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 1) (hw 1).continuous
  -- (iv) annulus DERIVATIVE sups at the two cofactors `w₀`, `w₁` (already narrow).
  obtain ⟨Kder0, hKder00, hDHann0U⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      (hw 0).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) (hw 0) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) (hw 0) j).continuous)
  obtain ⟨Kder1, hKder10, hDHann1U⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 1)
      (hw 1).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 1) (hw 1) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 1) (hw 1) j).continuous)
  -- (v) the two mixed engine constants.
  set S32 : ℝ := Real.sqrt (3 / 2) ^ n with hS32_def
  have hS320 : 0 ≤ S32 := by positivity
  set B₀ : ℝ := Bᵣ0 + Kcof0 * S32 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder0 with hB0_def
  set B₁ : ℝ := Bᵣ1 + Kcof1 * S32 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder1 with hB1_def
  have hB0nn : 0 ≤ B₀ := by
    rw [hB0_def]; positivity
  have hB1nn : 0 ≤ B₁ := by
    rw [hB1_def]; positivity
  refine ⟨a, b, B₀, B₁, ha0, hab, hb_lt_ρc, hB0nn, hB1nn, ?_⟩
  intro τ hτ q hq v
  -- `H₁` as the split `gauss·w₀ + τ·(gauss·w₁)`.
  have hH1eq : (heatParametrix 1 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y
          + τ * (gaussDdim τ y * foldedCoeff Θ u 1 y) := by
    funext y
    rw [heatParametrix_one_split Θ u τ y]
    have e0 : heatParametrix 0 Θ u τ y = gaussDdim τ y * foldedCoeff Θ u 0 y := by
      rw [heatParametrix_folded]; simp
    have e1 : heatParametrix 0 Θ (fun j => u (j + 1)) τ y
        = gaussDdim τ y * foldedCoeff Θ u 1 y := by
      rw [heatParametrix_folded]; simp [foldedCoeff_shift]
    rw [e0, e1]
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 1 Θ u τ) w :=
    fun w => (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
  -- near residual on the ball `rncRadialSq w ≤ b²` (mixed shape).
  have hb_le_ρu2 : b ≤ ρ_u / 2 := hb_le_bN
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
        ≤ (Bᵣ0 + Bᵣ1 * τ) * gaussDdim (3 / 2 * τ) w := by
    intro w hw2
    have hnw : ‖w‖ < ρ_u := by
      have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
      have hb2 : rncRadialSq w ≤ (ρ_u / 2) ^ 2 := by
        refine le_trans hw2 ?_
        have := mul_le_mul hb_le_ρu2 hb_le_ρu2 hb_nonneg (by linarith)
        simpa [pow_two] using this
      have h2 : rncRadial w ≤ ρ_u / 2 := by
        rw [rncRadial]
        calc Real.sqrt (rncRadialSq w)
            ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hb2
          _ = ρ_u / 2 := by rw [Real.sqrt_sq (by linarith)]
      linarith
    have hs := hResU1 τ hτ q hq w hnw
    simpa only [parametrixResidualN] using hs
  -- annulus VALUE bound for `H₁` (mixed, narrow).
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 1 Θ u τ w| ≤ ((Kcof0 + τ * Kcof1) * S32) * gaussDdim (3 / 2 * τ) w := by
    intro w h1 h2
    have hsplit : heatParametrix 1 Θ u τ w
        = gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w) := by
      rw [hH1eq]
    rw [hsplit]
    have hb0v := hHann0U τ hτ w h1 h2
    have hb1v := hHann1U τ hτ w h1 h2
    have hnarrow := gaussDdim_le_gaussDdim_narrow hτ w
    have hKsum : (0 : ℝ) ≤ Kcof0 + τ * Kcof1 := by positivity
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)|
        ≤ |gaussDdim τ w * foldedCoeff Θ u 0 w| + |τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)| :=
          abs_add_le _ _
      _ = |gaussDdim τ w * foldedCoeff Θ u 0 w| + τ * |gaussDdim τ w * foldedCoeff Θ u 1 w| := by
          rw [abs_mul τ (gaussDdim τ w * foldedCoeff Θ u 1 w), abs_of_pos hτ]
      _ ≤ Kcof0 * gaussDdim τ w + τ * (Kcof1 * gaussDdim τ w) :=
          add_le_add hb0v (mul_le_mul_of_nonneg_left hb1v hτ.le)
      _ = (Kcof0 + τ * Kcof1) * gaussDdim τ w := by ring
      _ ≤ (Kcof0 + τ * Kcof1) * (S32 * gaussDdim (3 / 2 * τ) w) :=
          mul_le_mul_of_nonneg_left hnarrow hKsum
      _ = ((Kcof0 + τ * Kcof1) * S32) * gaussDdim (3 / 2 * τ) w := by rw [hS32_def]; ring
  -- annulus DERIVATIVE bound for `H₁` (mixed, narrow) via `pd` distributed over the split.
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 1 Θ u τ) j w| ≤ (Kder0 + τ * Kder1) * gaussDdim (3 / 2 * τ) w := by
    intro w j h1 h2
    have hpdA : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 0)) j w
    have hpdB : PdiffAt (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w :=
      PdiffAt_of_contDiff _ ((gaussDdim_contDiff τ).mul (hw 1)) j w
    have hpdτB : PdiffAt (fun y => τ * (gaussDdim τ y * foldedCoeff Θ u 1 y)) j w :=
      PdiffAt_of_contDiff _ (contDiff_const.mul ((gaussDdim_contDiff τ).mul (hw 1))) j w
    have hpdsplit : pd (heatParametrix 1 Θ u τ) j w
        = pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
          + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w := by
      rw [hH1eq, pd_add _ _ j w hpdA hpdτB,
        pd_const_mul τ (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w hpdB]
    rw [hpdsplit]
    have hd0 := hDHann0U τ hτ w j h1 h2
    have hd1 := hDHann1U τ hτ w j h1 h2
    calc |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w
            + τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w|
        ≤ |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + |τ * pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := abs_add_le _ _
      _ = |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 0 y) j w|
            + τ * |pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w| := by
          rw [abs_mul τ (pd (fun y => gaussDdim τ y * foldedCoeff Θ u 1 y) j w), abs_of_pos hτ]
      _ ≤ Kder0 * gaussDdim (3 / 2 * τ) w + τ * (Kder1 * gaussDdim (3 / 2 * τ) w) :=
          add_le_add hd0 (mul_le_mul_of_nonneg_left hd1 hτ.le)
      _ = (Kder0 + τ * Kder1) * gaussDdim (3 / 2 * τ) w := by ring
  -- inverse-metric symmetry and annulus bound for the engine.
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  have hCnn : (0 : ℝ) ≤ Bᵣ0 + Bᵣ1 * τ := by positivity
  have hKcofnn : (0 : ℝ) ≤ (Kcof0 + τ * Kcof1) * S32 := by positivity
  have hKdernn : (0 : ℝ) ≤ Kder0 + τ * Kder1 := by positivity
  have hres := (cutoffResidual_narrow_tauUniform_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 1 Θ u τ) (fun x => deriv (fun s => heatParametrix 1 Θ u s x) τ)
    a b τ ha0 hab hτ hH2 hgisymm_q
    (Bᵣ0 + Bᵣ1 * τ) hCnn hEnear_q
    ((Kcof0 + τ * Kcof1) * S32) hKcofnn hHann
    (Kder0 + τ * Kder1) hKdernn hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v
  calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
      ≤ ((Bᵣ0 + Bᵣ1 * τ) + ((Kcof0 + τ * Kcof1) * S32) * Kc2
          + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * (Kder0 + τ * Kder1)) * gaussDdim (3 / 2 * τ) v := hres
    _ = (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by rw [hB0_def, hB1_def]; ring

/-! ### (C) — the concrete `N = 1` gated-witness mixed cover ⟹ the restricted `hEboundW_le`. -/

/-- **★ J4-106 (C) — THE `N = 1` GATED-WITNESS RESTRICTED `hEboundW_le`, FROM THE MIXED `hgood`.**
    The `N = 1` / MIXED analogue of `HunifTrichotomy.gatedWitness_hEboundW_of_good` composed with J4-105's
    T4.  From the mixed per-base-point in-chart Gaussian input `hgood` (the τ-uniform-radius restatement
    of the (A)+(B) chart-Gaussian bound, plus the T1/J4-93 chart geometry), the 3-leg MIXED cover is
    discharged for the concrete order-1 gated witness (leg 1 = in-gate mixed bound converted to
    `C·(baseKernelW 2 0 + baseKernelW 2 1)` with `C := max B₀ B₁`; leg 2 = off-gate; leg 3 = the cutoff
    COLLAR at the gate frontier, where `radialCutoff a b (W_q p') = 0` zeros the WHOLE witness — the
    order-`N` witness factors as `radialCutoff · heatParametrix N`, so the collar leg is `N`-generic).
    Feeding the cover to J4-105's T4 (`gatedKernel_hEboundW_le_of_mixedCover`) gives, for every ceiling
    `t`, the `(0,t]`-restricted pure-α=0 primitive.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_of_good (g gi : Point n → Fin n → Fin n → ℝ)
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
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) :
    ∃ S : Point n → Set (Point n), ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (gatedKernel K S
          (globalCutoffParametrixWitnessN 1 Θ u a b (W))) τ p q|
        ≤ (max B₀ B₁ * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
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
    obtain ⟨hbc, hbnd, hinv, hcont, hopen, hclos⟩ := (hgood q hq).choose_spec
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
  refine ⟨fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q), fun t => ?_⟩
  exact gatedKernel_hEboundW_le_of_mixedCover g gi K
    (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)) H (max B₀ B₁) t hCmax0 hcover

/-- **★★★ J4-106 (C) CAPSTONE — `gatedWitnessN1_hEboundW_le`: the `N = 1` gated-witness restricted
    `hEboundW_le`, ASSEMBLED.**  The `N = 1` mirror of `RadiusOrdering.gatedWitness_hEboundW_final`.
    Chaining (A) `cutoffResidualN1_uniformFlow_narrow_mixed_below`, (B)
    `heatOp_globalWitnessN1_eq_recentred_inChart_hoisted`, the J4-95 chart-Gaussian transfer (A3
    `gaussDdim_le_gaussDdim_chart`, `c=3/2`, `d=2`, via `uniformFlowExp_hdisp_ball`), and the (C) mixed
    cover builder `gatedWitnessN1_hEboundW_le_of_good`, delivers for the CONCRETE order-1 gated witness
    `globalCutoffParametrixWitnessN 1 Θ u a b (basepointInverseChart …)` the exact `(0,t]`-restricted
    pure-α=0 primitive `TrueKernelA1Reduced` (via J4-105 T4) consumes:
        `∀ t τ p q, 0<τ → τ≤t → |heatOp g gi (gatedKernel K S H₁_w) τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q`.

    Hypotheses are ONLY the genuine geometric data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`), the
    heat-side data (`Θ`/`u`/`hw` — BOTH the `w₀` and `w₁` jets, via the all-`k` folded smoothness), the two
    firewalled `totalRadialO1_coeff` coefficient bounds at the profiles `u`, `u'` (`hCoeffU0`/`hCoeffU1`,
    exactly J4-105 T1's), and the single isolated K-uniform chart residue `huniformChart` (identical to
    R4's — the quantitative uniform IFT radius over the compact `K`).  This is the `N = 1` counterpart of
    the recenter capstone's HARDEST C4c input — with J4-105 T5 (`hHdiag`) it completes the capstone's two
    hardest inputs at `N = 1`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_gen (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hCoeffU1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadialSq v)
    (W : Point n → Point n → Point n)
    (huniformChart : ∃ δ₀ > (0 : ℝ), ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => W q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (W q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c)) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (W))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := huniformChart
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc_def
  have hSc0 : 0 ≤ Sc := by positivity
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  -- (A) the mixed cutoff-residual bound with the cutoff far-radius `b < ρc`.
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB0, hB1, hAbound⟩ :=
    cutoffResidualN1_uniformFlow_narrow_mixed_below g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffU1 ρc hρc
  set B₀' : ℝ := B₀ * Sc with hB0'_def
  set B₁' : ℝ := B₁ * Sc with hB1'_def
  have hB0'0 : 0 ≤ B₀' := by rw [hB0'_def]; positivity
  have hB1'0 : 0 ≤ B₁' := by rw [hB1'_def]; positivity
  refine ⟨a, b, max B₀' B₁', ha, hab, le_trans hB0'0 (le_max_left _ _), ?_⟩
  -- discharge `hgood` of the (C) cover builder from (A)+(B, inline)+chart transfer + `huniformChart`.
  apply gatedWitnessN1_hEboundW_le_of_good g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0 hB1'0 W
  intro q hq
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  refine ⟨c, hbc, ?_, ?_, ?_, ?_⟩
  · -- BOUND leg: inline transport identity (radius `rN`) + (A) engine + chart transfer to width 2.
    intro τ hτ v hv
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
    -- inline transport identity.
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
  · -- INVERSE leg.
    intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
  · -- CONTINUITY leg.
    intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    exact (hchartGerm v hvδ₀).2.continuousAt
  · -- OPEN + CLOSURE legs.
    exact hchartOC c hc0 hc_δ₀

/-- **★★★ J4-106 (C) — `gatedWitnessN1_hEboundW_le`: the `N = 1` gated-witness restricted `hEboundW_le`,
    `huniformChart` DISCHARGED via the K-uniform chart.**  Instantiates `gatedWitnessN1_hEboundW_le_gen`
    at `W := uniformInverseChart g gi hC hK`, whose `huniformChart` shape is proved UNCONDITIONALLY by
    `uniformInverseChart_huniformChart` (`UniformChartRadius`).  Hyps are ONLY the geometric data and the
    heat-side data (`hw` — both the `w₀`/`w₁` jets — and the two firewalled `totalRadialO1_coeff`
    coefficient bounds `hCoeffU0`/`hCoeffU1` J4-105 T1 requires).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hCoeffU1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadialSq v) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  gatedWitnessN1_hEboundW_le_gen g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
    ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffU1
    (uniformInverseChart g gi hC hK) (uniformInverseChart_huniformChart g gi hC hK)

/-- **★★★★ J4-106 (C) CAPSTONE — `gatedWitnessN1_hEboundW_le_vanVleck`: the CONCRETE van-Vleck order-1
    gated-witness restricted `hEboundW_le`.**  The `N = 1` counterpart of
    `CapstoneWiring.gatedWitness_hEboundW_vanVleck`, specialising `gatedWitnessN1_hEboundW_le` to the
    DeWitt profile `Θ := vanVleck g`, `u := transportCoeff (transportOp (vanVleck g) g gi)`.  Delivers,
    for the concrete order-1 gated van-Vleck witness with the K-uniform chart, the exact
    `(0,t]`-restricted pure-α=0 primitive the residual `a₁ = R/6` capstone consumes at `N = 1`:
        `∀ t τ p q, 0<τ → τ≤t → |heatOp g gi (gatedKernel K S H₁_vV) τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q`.
    Hyps: the geometric data plus the firewalled van-Vleck heat-side inputs (`hw`/`hCoeffU0`/`hCoeffU1` at
    the van-Vleck profile).  With J4-105 T5 (`gatedWitnessN1_diag_eval_vanVleck`, the order-1 `hHdiag`),
    this completes the residual capstone's TWO HARDEST inputs at `N = 1`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) v| ≤ C_c0 * rncRadialSq v)
    (hCoeffU1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (vanVleck g)
          (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) v| ≤ C_c1 * rncRadialSq v) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  gatedWitnessN1_hEboundW_le g gi hg hC hK hgnd hgsymm hinvF hframeK
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
    ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffU1

end QIQTH.HeatResidualBound
