/-
  CommonGateShell — J4-380: THE COMMON-`(a,b)` SHELL.  Composing the two uniformized affine legs into
  the concrete `AffineGateBound`, and (milestone) retiring the `hgate` label of the width-3/2 `hEdom`
  ∃-shape for the concrete van-Vleck gated witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole convergence / geometric-wiring stack.  This file is ONE COMPOSITION /
  GLUE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign: it takes the two banked
  UNIFORMIZED legs (the PLATEAU leg `LegUniformization.gatedHeatOp_plateau_uniform`, J4-378, and the
  ANNULUS leg `AnnulusUniformization.gatedHeatOp_annulus_uniform`, J4-379), each of which `∃`-chooses its
  OWN cutoff pair `(a, b)` from its own radius-min, and RE-EXPRESSES their analytic cores as `∀-(a,b)`
  bodies below a shared radius bound.  It then chooses ONE common `(a, b)` (with a matching constant-radius
  gate `S`), feeds both legs into the 3-region capstone `AffineGateCapstone.affineGateBound_of_legs`
  (J4-377), and composes with the affine bridge `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine` (J4-368)
  to obtain the width-3/2 `hEdom` ∃-shape for the concrete van-Vleck gated witness FROM GEOMETRY ALONE —
  the surviving `hgate` label RETIRED.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`,
  NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing
  file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE BLOCKER (J4-379 report).  Each uniformized leg's OUTPUT existentially chose its own `(a, b) =
  (m/4, m/2)` from its own radius-min; the 3-region stitch demands ONE shared `(a, b)`.  But both legs'
  BODIES are parametric in `(a, b)` — the `∃`-intro is packaging only.  This file lifts the packaging: it
  obtains the radius / constant data ONCE (before the `∀ a b`), then re-runs each leg's compiled body for
  a GIVEN `(a, b)` below the shared radius bound (the plateau coefficient pair is `(a,b)`-independent, so
  it stays outside; the annulus coefficient pair is `(a,b)`-dependent, so its `∃ P₀ P₁` moves INSIDE the
  `∀ a b`).

  ## DELIVERABLES.
  •  (S1) `gatedHeatOp_plateau_at` — the `∀-(a,b)` plateau leg (compiled body of
     `gatedHeatOp_plateau_uniform` with `(a, b)` and the gate `S` moved to `∀`-inputs below a shared
     radius `ρ_plat`).  NOT `a₁ = R/6`.
  •  (S2) `gatedHeatOp_annulus_at` — the `∀-(a,b)` annulus leg (compiled body of
     `gatedHeatOp_annulus_uniform` with `(a, b)` / `S` moved to `∀`-inputs below `ρ_ann`; the
     `(a,b)`-dependent coefficient `∃ P₀ P₁` moved inside).  NOT `a₁ = R/6`.
  •  (S3) `affineGateBound_concrete` — ★ chooses ONE common `(a, b)` and the constant-radius gate `S`, and
     assembles `HgateAffineRepair.AffineGateBound` at the concrete `N = 1` witness via
     `affineGateBound_of_legs`.  NOT `a₁ = R/6`.
  •  (S4) `hEdom_from_geometry` — ★★★★ THE MILESTONE.  The width-3/2 `hEdom` ∃-shape for the concrete
     van-Vleck gated witness FROM GEOMETRY ONLY — the two coefficient bounds `hCoeffU0`/`hCoeffLin1` are
     discharged INTERNALLY from the geometric inputs (`hCoeffU0_vanVleck` / `uniformCoeffLinear_bound`),
     so the `hgate` label is RETIRED.  NOT `a₁ = R/6`.

  ## SATISFIABILITY / HONESTY.  Every surviving hypothesis of `hEdom_from_geometry` is a genuine
  geometric / gauge / smoothness / compactness input: `hg`/`hC`/`hw` (smoothness), `hdg0`/`hg0` (gauge at
  the base point), `hframeK`/`hinvF`/`hgnd`/`hgsymm` (frame / metric), `hK` (compactness).  NONE is
  vacuous, NONE equals the conclusion, and the `hgate` on-gate carry is DERIVED (not assumed).  `a₁ = R/6`
  stays CONDITIONAL on the full convergence stack.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LegUniformization
import QIQTH.AnnulusUniformization
import QIQTH.AffineGateCapstone
import QIQTH.HgateAffineRepair
import QIQTH.CoeffBoundsN1
import QIQTH.CoeffU1Fix
import QIQTH.ConvApproximants
import QIQTH.OnGateGlue
import QIQTH.AffineGateTransport
import QIQTH.GlobalHunifAssembly
import QIQTH.UniformChartRadius
import QIQTH.RadiusOrdering
import QIQTH.UniformFlowMetricInvProps
import QIQTH.CutoffAnnulusBounds
import QIQTH.AnnulusAmbientTransfer
import QIQTH.UniformCutoffEngine
import QIQTH.VanVleckCancellation

open Set Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.RNCDecay
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianPolyBound QIQTH.GaussianWidthTolerant
open QIQTH.AnnulusAmbientTransfer
open scoped Topology BigOperators ContDiff

namespace QIQTH.CommonGateShell

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (S1) — the `∀-(a,b)` plateau leg.
    ############################################################################### -/

/-- **★ (S1) — `gatedHeatOp_plateau_at`.**  THE `∀-(a,b)` PLATEAU LEG.  The compiled analytic core of
    `LegUniformization.gatedHeatOp_plateau_uniform` (J4-378) with the cutoff pair `(a, b)` and the gate
    `S` moved from `∃`-outputs to `∀`-INPUTS below a SHARED radius `ρ_plat` (obtained ONCE, before the
    `∀`): for EVERY gate `S` and EVERY `(a, b)` with `0 < a < b < ρ_plat`, the gated witness's `heatOp`
    at the exp point is bounded by the ambient width-`4/3` affine QUAD envelope on `z := φ_q v − q`,
    uniformly over `q ∈ K`, the plateau `rncRadialSq v < a²`, and all `τ > 0`.  The coefficient pair
    `(P₀, P₁)` is `(a,b)`-INDEPENDENT (threaded UNCHANGED from `plat_residual_uniform_width43`), hence
    stays OUTSIDE the `∀ a b`.  Body: obtain the uniform residual envelope `plat_residual_uniform_width43`
    + the banked chart germ + Laplacian naturality ONCE; for each `(a, b)` the plateau constraint
    `rncRadialSq v < a²` forces `‖v‖ < a < b < ρ_plat`, discharging every supplier radius, and the
    `hpt`/`hlap` glue + `OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau` close as in J4-378.
    NOT `a₁ = R/6`. -/
theorem gatedHeatOp_plateau_at (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ ρ_plat P₀ P₁ : ℝ, 0 < ρ_plat ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      ∀ (S : Point n → Set (Point n)) (a b : ℝ), 0 < a → a < b → b < ρ_plat →
        ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n, rncRadialSq v < a ^ 2 →
          S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
          |heatOp g gi (gatedKernel K S
              (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ (P₀ + P₁ * τ)
                * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                      + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                    * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨ρ, P₀, P₁, hρ0, hP00, hP10, hres⟩ :=
    QIQTH.LegUniformization.plat_residual_uniform_width43 g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set ρ_plat : ℝ := min ρ (min δ₀ rN) with hρplatdef
  have hρplat0 : 0 < ρ_plat := lt_min hρ0 (lt_min hδ₀ hrNpos)
  refine ⟨ρ_plat, P₀, P₁, hρplat0, hP00, hP10, ?_⟩
  intro S a b ha0 hab hbρplat τ hτ q hq v hplateau hS
  -- the plateau constraint forces `‖v‖ < a`, hence below every supplier radius.
  have hrv : rncRadial v < a := by
    have hsq : Real.sqrt (rncRadialSq v) < Real.sqrt (a ^ 2) :=
      Real.sqrt_lt_sqrt (rncRadialSq_nonneg v) hplateau
    rw [Real.sqrt_sq ha0.le] at hsq
    exact hsq
  have hnv : ‖v‖ < a := lt_of_le_of_lt (norm_le_rncRadial v) hrv
  have hvρ : ‖v‖ < ρ :=
    lt_of_lt_of_le (lt_trans (lt_trans hnv hab) hbρplat) (min_le_left _ _)
  have hvδ₀ : ‖v‖ < δ₀ :=
    lt_of_lt_of_le (lt_trans (lt_trans hnv hab) hbρplat) ((min_le_right _ _).trans (min_le_left _ _))
  have hvrN : ‖v‖ < rN :=
    lt_of_lt_of_le (lt_trans (lt_trans hnv hab) hbρplat) ((min_le_right _ _).trans (min_le_right _ _))
  -- discharge the glue carries `hpt`, `hlap` (mirrors `gatedHeatOp_plateau_uniform`).
  obtain ⟨hchartGerm, _hchartOC⟩ := hchart q hq
  obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
  have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by simpa using hgerm.eq_of_nhds
  have hf : ContDiffAt ℝ 2
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      (uniformFlowExp g gi hC hK q v) := by
    have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
        (W q (uniformFlowExp g gi hC hK q v)) := by
      apply ContDiffAt.mul
      · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
    exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
  have hprofilegerm :
      (fun z => globalCutoffParametrixWitnessN 1 Θ u a b W τ
          (uniformFlowExp g gi hC hK q z) q)
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
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
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitnessN 1 Θ u a b W τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
    have hn := hnat
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      q hq v hvrN hg1 hf hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  -- rewrite the gated heatOp to the pullback residual, then close with the uniform envelope.
  rw [QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau g gi hC hK S Θ u ha0 hab
      q v hq hS hpt hlap hplateau]
  exact hres τ hτ q hq v hvρ

/-! ###############################################################################
    ### (S2) — the `∀-(a,b)` annulus leg.
    ############################################################################### -/

/-- **★ (S2) — `gatedHeatOp_annulus_at`.**  THE `∀-(a,b)` ANNULUS LEG.  The compiled analytic core of
    `AnnulusUniformization.gatedHeatOp_annulus_uniform` (J4-379) with the cutoff pair `(a, b)` and the
    gate `S` moved from `∃`-outputs to `∀`-INPUTS below a SHARED radius `ρ_ann` (obtained ONCE, before the
    `∀`): for EVERY gate `S` and EVERY `(a, b)` with `0 < a < b < ρ_ann`, there is a coefficient pair
    `(P₀, P₁)` (which GENUINELY depends on `(a, b)` via the annulus suppliers `Kc2`/`Kc1`/`Kcof·`/`Kder·`
    — hence the `∃ P₀ P₁` lives INSIDE the `∀ a b`) bounding the gated witness's `heatOp` at the exp point
    by the ambient width-`4/3` affine QUAD envelope on `z := φ_q v − q`, uniformly over `q ∈ K`, the
    annulus `a² ≤ rncRadialSq v ≤ b²`, and all `τ > 0`.  Body: obtain the `(a,b)`-INDEPENDENT suppliers
    (`hEnear_uniform`, the ambient annulus transfer, the metric-inverse / cutoff-Laplacian annulus bounds,
    the chart germ, Laplacian naturality) ONCE; for each `(a, b)` obtain the `(a,b)`-DEPENDENT suppliers,
    re-run the ambient annulus transfer with the τ-affine value / derivative refold, and close via the
    plateau `hpt`/`hlap` glue + `AffineGateTransport.heatOp_globalCutoffWitness_transport` as in J4-379.
    NOT `a₁ = R/6`. -/
theorem gatedHeatOp_annulus_at (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ ρ_ann : ℝ, 0 < ρ_ann ∧
      ∀ (S : Point n → Set (Point n)) (a b : ℝ), 0 < a → a < b → b < ρ_ann →
        ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
          ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n,
            a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
            S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
            |heatOp g gi (gatedKernel K S
                (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
                (uniformFlowExp g gi hC hK q v) q|
              ≤ (P₀ + P₁ * τ)
                  * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                        + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                      * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  classical
  -- the `(a,b)`-INDEPENDENT suppliers, obtained ONCE.
  obtain ⟨ρ, C₀, C₁, hρ0, hC₀0, hC₁0, hEnearU⟩ :=
    QIQTH.AnnulusUniformization.hEnear_uniform g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨r₁, hr₁pos, hW2⟩ :=
    QIQTH.AnnulusAmbientTransfer.cutoffResidual_annulusAmbient43_bound g gi hC hK
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set ρ_ann : ℝ := min ρ (min r₁ (min rKg (min rKc2 (min δ₀ rN)))) with hρanndef
  have hρann0 : 0 < ρ_ann :=
    lt_min hρ0 (lt_min hr₁pos (lt_min hrKg0 (lt_min hrKc20 (lt_min hδ₀ hrNpos))))
  refine ⟨ρ_ann, hρann0, ?_⟩
  intro S a b ha0 hab hbρann
  have hb0 : 0 < b := lt_trans ha0 hab
  have hb_nonneg : (0 : ℝ) ≤ b := hb0.le
  -- radius bookkeeping from the shared bound.
  have hbρ : b < ρ := lt_of_lt_of_le hbρann (min_le_left _ _)
  have hbr : b < r₁ := lt_of_lt_of_le hbρann ((min_le_right _ _).trans (min_le_left _ _))
  have hb_lt_rKg : b < rKg :=
    lt_of_lt_of_le hbρann ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb_lt_rKc2 : b < rKc2 :=
    lt_of_lt_of_le hbρann ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hbδ₀ : b < δ₀ :=
    lt_of_lt_of_le hbρann ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbrN : b < rN :=
    lt_of_lt_of_le hbρann ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  -- the `(a,b)`-DEPENDENT uniform annulus suppliers.
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kcof0, hKcof00, hHann0U⟩ :=
    parametrixCofactor_value_annulus54 a b (foldedCoeff Θ u 0) (hw 0).continuous
  obtain ⟨Kcof1, hKcof10, hHann1U⟩ :=
    parametrixCofactor_value_annulus54 a b (foldedCoeff Θ u 1) (hw 1).continuous
  obtain ⟨Kder0, hKder00, hDHann0U⟩ :=
    parametrixCofactor_deriv_annulus54 a b ha0 hb0 (foldedCoeff Θ u 0)
      (hw 0).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) (hw 0) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) (hw 0) j).continuous)
  obtain ⟨Kder1, hKder10, hDHann1U⟩ :=
    parametrixCofactor_deriv_annulus54 a b ha0 hb0 (foldedCoeff Θ u 1)
      (hw 1).continuous (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 1) (hw 1) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 1) (hw 1) j).continuous)
  refine ⟨25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
        * (C₀ + Kcof0 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder0),
    25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
        * (Kcof1 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder1 + C₁),
    by positivity, by positivity, ?_⟩
  intro τ hτ q hq v ha2 hb2 hS
  -- the `heatParametrix 1` value / derivative split (τ-affine).
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
  -- radius bookkeeping from the annulus membership.
  have hnvb : ‖v‖ ≤ b := by
    have hrb : rncRadial v ≤ b := by
      have hdef : rncRadial v = Real.sqrt (rncRadialSq v) := rfl
      rw [hdef]
      calc Real.sqrt (rncRadialSq v) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hb2
        _ = b := Real.sqrt_sq hb_nonneg
    exact le_trans (norm_le_rncRadial v) hrb
  have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hnvb hbδ₀
  have hvrN : ‖v‖ < rN := lt_of_le_of_lt hnvb hbrN
  have hnormlt : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 → ‖w‖ < ρ := by
    intro w hw2
    have hrb : rncRadial w ≤ b := by
      have hdef : rncRadial w = Real.sqrt (rncRadialSq w) := rfl
      rw [hdef]
      calc Real.sqrt (rncRadialSq w) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hw2
        _ = b := Real.sqrt_sq hb_nonneg
    exact lt_of_le_of_lt (le_trans (norm_le_rncRadial w) hrb) hbρ
  -- discharge the transport glue `hpt`, `hlap` (leg-agnostic plateau block).
  obtain ⟨hchartGerm, _hchartOC⟩ := hchart q hq
  obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
  have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by simpa using hgerm.eq_of_nhds
  have hf : ContDiffAt ℝ 2
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      (uniformFlowExp g gi hC hK q v) := by
    have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
        (W q (uniformFlowExp g gi hC hK q v)) := by
      apply ContDiffAt.mul
      · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
    exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
  have hprofilegerm :
      (fun z => globalCutoffParametrixWitnessN 1 Θ u a b W τ
          (uniformFlowExp g gi hC hK q z) q)
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
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
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitnessN 1 Θ u a b W τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
    have hn := hnat
      (fun x => globalCutoffParametrixWitnessN 1 Θ u a b W τ x q)
      q hq v hvrN hg1 hf hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  -- the six pointwise annulus carries (τ-affine value / derivative).
  have hEnear : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
        ≤ (C₀ + C₁ * τ) * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1)
            * gaussDdim (5 / 4 * τ) w) :=
    fun w _h1 h2 => hEnearU τ hτ q hq w (hnormlt w h2)
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 1 Θ u τ w| ≤ (Kcof0 + τ * Kcof1) * gaussDdim (5 / 4 * τ) w := by
    intro w h1 h2
    have hsplit : heatParametrix 1 Θ u τ w
        = gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w) := by
      rw [hH1eq]
    rw [hsplit]
    have hb0v := hHann0U τ hτ w h1 h2
    have hb1v := hHann1U τ hτ w h1 h2
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w + τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)|
        ≤ |gaussDdim τ w * foldedCoeff Θ u 0 w| + |τ * (gaussDdim τ w * foldedCoeff Θ u 1 w)| :=
          abs_add_le _ _
      _ = |gaussDdim τ w * foldedCoeff Θ u 0 w| + τ * |gaussDdim τ w * foldedCoeff Θ u 1 w| := by
          rw [abs_mul τ (gaussDdim τ w * foldedCoeff Θ u 1 w), abs_of_pos hτ]
      _ ≤ Kcof0 * gaussDdim (5 / 4 * τ) w + τ * (Kcof1 * gaussDdim (5 / 4 * τ) w) :=
          add_le_add hb0v (mul_le_mul_of_nonneg_left hb1v hτ.le)
      _ = (Kcof0 + τ * Kcof1) * gaussDdim (5 / 4 * τ) w := by ring
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 1 Θ u τ) j w| ≤ (Kder0 + τ * Kder1) * gaussDdim (5 / 4 * τ) w := by
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
      _ ≤ Kder0 * gaussDdim (5 / 4 * τ) w + τ * (Kder1 * gaussDdim (5 / 4 * τ) w) :=
          add_le_add hd0 (mul_le_mul_of_nonneg_left hd1 hτ.le)
      _ = (Kder0 + τ * Kder1) * gaussDdim (5 / 4 * τ) w := by ring
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  have hKcofnn : (0 : ℝ) ≤ Kcof0 + τ * Kcof1 := by positivity
  have hKdernn : (0 : ℝ) ≤ Kder0 + τ * Kder1 := by positivity
  -- the ambient annulus transfer at the pullback pair.
  have hW2b := hW2 q hq (uniformFlowPullbackMetric g gi hC hK q)
    (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 1 Θ u τ) (fun w => deriv (fun s => heatParametrix 1 Θ u s w) τ)
    a b τ ha0 hab hbr hτ hH2 hgisymm_q
    C₀ C₁ hC₀0 hC₁0 hEnear
    (Kcof0 + τ * Kcof1) hKcofnn hHann
    (Kder0 + τ * Kder1) hKdernn hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd hDchi (hLapChiU q hq) v ha2 hb2
  -- rewrite the gated heatOp to the transport RHS, then re-fold the τ-affine coefficient.
  rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S
        (globalCutoffParametrixWitnessN 1 Θ u a b W) τ
        (uniformFlowExp g gi hC hK q v) q hq hS,
      QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport g gi hC hK Θ u a b W q v
        hpt hlap]
  exact le_trans hW2b (le_of_eq (by ring))

/-! ###############################################################################
    ### (S3) — ★ the common-`(a,b)` `AffineGateBound` assembly.
    ############################################################################### -/

/-- **★★★ (S3) — `affineGateBound_concrete`.**  THE COMMON-`(a,b)` SHELL.  Chooses ONE common cutoff pair
    `(a, b)` and the constant-radius flow-ball gate `S q = φ_q '' ball 0 c₀` (with `b < c₀ < δ₀`), feeds
    the two `∀-(a,b)` legs (S1 / S2) below the shared radius bound `m = min ρ_plat (min ρ_ann δ₀)`, and
    assembles `HgateAffineRepair.AffineGateBound g gi K S (globalCutoffParametrixWitnessN 1 Θ u a b
    (uniformInverseChart g gi hC hK)) (max P₀a P₀b) (max P₁a P₁b)` via
    `AffineGateCapstone.affineGateBound_of_legs`.  The gate facts (`hcb`/`hSopen`/`hSmem`/`hSclos`/`hWpt`/
    `hWcont`) are discharged UNIFORMLY at the constant `c₀` from the banked chart germ
    `uniformInverseChart_huniformChart` (mirroring the `hgoodC` block of
    `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST`).  The carries `hCoeffU0`/`hCoeffLin1`
    stay as SATISFIABLE hypotheses (discharged internally by the milestone S4).  NOT `a₁ = R/6`. -/
theorem affineGateBound_concrete (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n), ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
      QIQTH.HgateAffineRepair.AffineGateBound g gi K S
        (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)) P₀ P₁ := by
  obtain ⟨ρ_plat, P₀a, P₁a, hρplat0, hP₀a, hP₁a, hplatbody⟩ :=
    gatedHeatOp_plateau_at g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨ρ_ann, hρann0, hannbody⟩ :=
    gatedHeatOp_annulus_at g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  set m : ℝ := min ρ_plat (min ρ_ann δ₀) with hmdef
  have hm0 : 0 < m := lt_min hρplat0 (lt_min hρann0 hδ₀)
  set c₀ : ℝ := m / 2 with hc₀def
  set b : ℝ := m / 4 with hbdef
  set a : ℝ := m / 8 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hbm : b < m := by rw [hbdef]; linarith
  have hcm : c₀ < m := by rw [hc₀def]; linarith
  have hbc : b < c₀ := by rw [hbdef, hc₀def]; linarith
  have hc0 : 0 < c₀ := by rw [hc₀def]; linarith
  have hbρplat : b < ρ_plat := lt_of_lt_of_le hbm (min_le_left _ _)
  have hbρann : b < ρ_ann := lt_of_lt_of_le hbm ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ₀ : c₀ < δ₀ := lt_of_lt_of_le hcm ((min_le_right _ _).trans (min_le_right _ _))
  -- the two legs at the common `(a, b)` and the constant-radius gate.
  have hplat := hplatbody (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀)
    a b ha0 hab hbρplat
  obtain ⟨P₀b, P₁b, hP₀b, hP₁b, hann⟩ :=
    hannbody (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) a b ha0 hab hbρann
  -- the gate facts at the single constant `c₀` (mirrors the `hgoodC` block).
  have hcb : ∀ q ∈ K, b < (fun _ : Point n => c₀) q := fun q _ => hbc
  have hSopen : ∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) :=
    fun q hq => ((hchart q hq).2 c₀ hc0 hcδ₀).1
  have hSmem : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < (fun _ : Point n => c₀) q →
      uniformFlowExp g gi hC hK q v ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀ :=
    fun q _ v hv => ⟨v, mem_ball_zero_iff.mpr hv, rfl⟩
  have hSclos : ∀ q ∈ K,
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 ((fun _ : Point n => c₀) q) :=
    fun q hq => ((hchart q hq).2 c₀ hc0 hcδ₀).2
  have hWpt : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ (fun _ : Point n => c₀) q →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v :=
    fun q hq v hv => by simpa using ((hchart q hq).1 v (lt_of_le_of_lt hv hcδ₀)).1.eq_of_nhds
  have hWcont : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ (fun _ : Point n => c₀) q →
      ContinuousAt (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v) :=
    fun q hq v hv => ((hchart q hq).1 v (lt_of_le_of_lt hv hcδ₀)).2.continuousAt
  refine ⟨a, b, ha0, hab, (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀),
    max P₀a P₀b, max P₁a P₁b, le_trans hP₀a (le_max_left _ _), le_trans hP₁a (le_max_left _ _), ?_⟩
  exact QIQTH.AffineGateCapstone.affineGateBound_of_legs g gi hC hK
    (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c₀) Θ u a b
    (uniformInverseChart g gi hC hK) (fun _ => c₀) ha0 hab
    P₀a P₁a P₀b P₁b hP₀a hP₁a hP₀b hP₁b
    hcb hSopen hSmem hSclos hWpt hWcont hplat hann

/-! ###############################################################################
    ### (S4) — ★★★★ the width-3/2 `hEdom` ∃-shape FROM GEOMETRY (hgate RETIRED).
    ############################################################################### -/

/-- **★★★★ (S4) — `hEdom_from_geometry`.**  THE MILESTONE.  The width-3/2 `hEdom` ∃-shape for the concrete
    van-Vleck gated witness `vanVleckGatedWitness g gi hC hK S a b`, FROM GEOMETRY ONLY — the `hgate`
    on-gate carry is DERIVED (not assumed).  Composes the common-`(a,b)` shell S3 (specialized to
    `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`) with the affine bridge
    `HgateAffineRepair.hEdom_vanVleck_of_hgate_affine` (the `vanVleckGatedWitness` head-rewrite).  The two
    coefficient carries `hCoeffU0`/`hCoeffLin1` are discharged INTERNALLY from the SAME geometric inputs
    via `CoeffBoundsN1.hCoeffU0_vanVleck` / `CoeffU1Fix.uniformCoeffLinear_bound` (mirroring
    `ConstRadiusGateExport.gatedWitnessN1_package_open_CONSTRADIUS`).

    ══ THE FINAL INPUT LIST (everything `hEdom_from_geometry` needs).  ONLY genuine geometric / gauge /
    smoothness / compactness data — NO labelled `hgate`:
      •  smoothness:   `hg` (metric `C^∞`), `hC` (Christoffel `C^∞`), `hw` (folded vanVleck coeff `C^∞`);
      •  gauge (base): `hdg0` (∂g = 0 at 0), `hg0` (g = δ at 0);
      •  frame/metric: `hframeK` (g = δ on `K`), `hinvF` (g·gi = 1), `hgnd` (g invertible), `hgsymm`
                       (g symmetric);
      •  compactness:  `hK` (`K` compact).
    The on-gate `hgate` label is RETIRED.  NOT `a₁ = R/6`. -/
theorem hEdom_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n), ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
      ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  -- discharge the two coefficient carries INTERNALLY from geometry (mirrors the CONSTRADIUS export).
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    QIQTH.HeatResidualBound.hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    QIQTH.HeatResidualBound.uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  have hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) v| ≤ C0 * rncRadialSq v :=
    fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _))
  have hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (vanVleck g)
          (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) v| ≤ C1 * rncRadial v :=
    fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _))
  -- the common-`(a,b)` `AffineGateBound` at the concrete van-Vleck witness.
  obtain ⟨a, b, ha0, hab, S, P₀, P₁, hP₀, hP₁, hAGB⟩ :=
    affineGateBound_concrete g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1 hCoeffU0 hCoeffLin1
  -- the affine bridge (`vanVleckGatedWitness` head-rewrite) closes the width-3/2 `hEdom` ∃-shape.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    QIQTH.HgateAffineRepair.hEdom_vanVleck_of_hgate_affine g gi hC hK S a b P₀ P₁ hP₀ hP₁ hAGB
  exact ⟨a, b, ha0, hab, S, E₀, E₁, hE₀, hE₁, hEdom⟩

end QIQTH.CommonGateShell

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CommonGateShell.gatedHeatOp_plateau_at
#print axioms QIQTH.CommonGateShell.gatedHeatOp_annulus_at
#print axioms QIQTH.CommonGateShell.affineGateBound_concrete
#print axioms QIQTH.CommonGateShell.hEdom_from_geometry
