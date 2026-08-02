/-
  RadiusOrdering — J4-99: the RADIUS-ORDERING discharge of the `hunif` tower's last residue.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What J4-98 (`HunifTrichotomy.lean`) left, and what this file delivers (ns `QIQTH.HeatResidualBound`).

  J4-98 reduced the width-2 residual primitive `hEboundW` (for the CONCRETE gated witness) to a single
  isolated input `hgood`, whose sole irreducible content is the RADIUS ORDERING: the cutoff far-radius
  `b` (chosen internally by the J4-95 engine chain from annulus suppliers) must sit BELOW a gate radius
  `c` which itself sits below the τ-FREE transport radius `r₀` and the base-point chart radius `δ`.  The
  engine's `b` was previously unforced.

  This file forces it:

    * (R1) `cutoffResidual_uniformFlow_unconditional_tau_narrow_below` — the J4-95 τ-narrow engine
      re-run with the cutoff far-radius `b` ALSO capped below an ARBITRARY requested ceiling `ρc`.  The
      engine works for ANY smaller `b` (the annulus suppliers hold on any annulus inside their radius;
      the near bound holds a fortiori on the smaller ball; the cutoff-derivative constants exist for any
      `0 < a < b`), so the whole proof goes through verbatim with `b := min (min bN (rmin/2)) (ρc/2)`.

    * (R2) `globalWitness_residual_bound_chartGaussian_final_below` — the J4-96 consumer-width chart
      Gaussian bound, but with (i) the ceiling `b < ρc` threaded through the transport chain and (ii) the
      per-`(τ,q)` transport radius `r₀` HOISTED OUTSIDE the `∀ τ` binder (J4-98 verified the VALUE is
      τ-free = `min ρ₀ uniformFlowRadius`, and `basepointInverseChart_spec`'s germ radius `δ`).  The
      hoist needs a `∀ f` restatement of the pullback-Laplacian naturality
      (`laplaceBeltrami_uniformFlow_naturality_forall_f`, whose radius is manifestly `f`-free) plus a
      hoisted transport identity (`heatOp_globalWitness_eq_recentred_inChart_hoisted`).  Result:
      `∀ ρc>0, ∃ a b B, 0<a ∧ a<b ∧ b<ρc ∧ 0≤B ∧ ∀ q∈K, ∃ r₀>0, ∀ τ>0 ∀ ‖v‖<r₀ : [J4-96 bound]`.

    * (R4) `gatedWitness_hEboundW_final` — the summit.  With R1+R2, the concrete gate radius `c` is
      pinned between `b` and the τ-free transport/chart radii, discharging the τ-uniformity and the
      per-`q` radius ordering of J4-98's `hgood`.  The SOLE remaining input is a K-UNIFORM lower bound
      on the base-point inverse-chart radius (`huniformChart`): a single `δ₀>0` on which the concrete
      chart facts hold for EVERY `q ∈ K`.  This is strictly weaker & more isolated than J4-98's `hgood`
      (which bundled the τ-uniformity, the radius ordering, AND the geometry): it is the uniform IFT
      radius over the compact base `K`, a pure compactness fact (`uniformFlowExp_common_nondeg_radius`
      already supplies the K-uniform NONDEGENERACY radius; the residue is the K-uniform IFT SOURCE-ball
      radius).  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## FIREWALL — the single isolated input `huniformChart` (binding, honest).

  `huniformChart` packages ONE radius `δ₀ > 0`, uniform over `K`, on which the base-point inverse chart
  `basepointInverseChart` is the genuine `C²` left inverse of `φ_q = uniformFlowExp g gi hC hK q` and the
  chart-image ball is open with compact-image closure.  Every per-`q` piece already exists
  (`basepointInverseChart_spec` for the germ/`C²`, `chartImage_ball_open_closure` for the open/closure);
  the ONLY residue is that their radius `δ_q` be bounded below UNIFORMLY over the compact `K`.  This is
  the quantitative uniform inverse function theorem over a compact family — genuine, satisfiable (flat
  `g`: `φ_q v = q + v`, `δ_q = +∞`), and NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HunifTrichotomy
import QIQTH.NearIsometryBudget
import QIQTH.WidthMarginEngine
import QIQTH.GlobalResidualWitness
import QIQTH.PullbackNaturalityLocal

open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.HeatParametrixOrder
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.RadialDistance QIQTH.RNCDecay
open Set Filter
open scoped BigOperators Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (R1) The τ-narrow cutoff-residual engine, re-run below an arbitrary ceiling `ρc`. -/

/-- **★ R1 — `cutoffResidual_uniformFlow_unconditional_tau_narrow_below`.**  The J4-95 τ-narrow engine
    (`cutoffResidual_uniformFlow_unconditional_tau_narrow`) re-run with the cutoff far-radius `b` ALSO
    capped below an arbitrary requested ceiling `ρc > 0`.  The engine's radius choice is
    `b := min (min bN (rmin/2)) (ρc/2)` (was `min bN (rmin/2)`), `a := b/2`; every downstream annulus /
    near / cutoff-derivative supplier holds for the smaller `b` verbatim (monotone in `b`), and the
    smaller `b` adds `b < ρc`.  Delivers the SAME τ-narrow recentred-residual bound plus `b < ρc`. -/
theorem cutoffResidual_uniformFlow_unconditional_tau_narrow_below (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
        ≤ B * gaussDdim (3 / 2 * τ) v := by
  classical
  obtain ⟨ρ_c, hρ_c, C_c, hC_c0, hCoeffU⟩ :=
    uniformCoeff_bound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
  obtain ⟨ρ_u, hρ_u0, C, hC0, hResU⟩ :=
    uniformResidual_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth
      ρ_c C_c hρ_c hC_c0 hCoeffU
  obtain ⟨bN, hbN0, hEnearU⟩ :=
    near_uncutResidual_uniform_tau_narrow g gi hC hK Θ u C ρ_u hρ_u0 hResU
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
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
  obtain ⟨Kcof, hKcof0, hHannU⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) hw0smooth.continuous
  obtain ⟨Kder, hKder0, hDHannU⟩ :=
    parametrixCofactor_deriv_annulus_narrow_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  set Kcof' : ℝ := Kcof * Real.sqrt (3 / 2) ^ n with hKcof'_def
  have hKcof'0 : 0 ≤ Kcof' := by positivity
  have hBnn : 0 ≤ C + Kcof' * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
    have h1 : 0 ≤ Kcof' * Kc2 := mul_nonneg hKcof'0 hKc20
    have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
    linarith
  refine ⟨a, b, C + Kcof' * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder, ha0, hab, hb_lt_ρc, hBnn, ?_⟩
  intro τ hτ q hq v
  have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
    funext x; rw [heatParametrix_folded]; simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u τ w = gaussDdim τ w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
    rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u τ) w :=
    fun w => hH.contDiffAt.of_le le_top
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u τ w| ≤ Kcof' * gaussDdim (3 / 2 * τ) w := by
    intro w h1 h2
    rw [hHeqw w]
    calc |gaussDdim τ w * foldedCoeff Θ u 0 w|
        ≤ Kcof * gaussDdim τ w := hHannU τ hτ w h1 h2
      _ ≤ Kcof * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) w) :=
          mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow hτ w) hKcof0
      _ = Kcof' * gaussDdim (3 / 2 * τ) w := by rw [hKcof'_def]; ring
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u τ) j w| ≤ Kder * gaussDdim (3 / 2 * τ) w := by
    intro w j h1 h2; rw [hHeq]; exact hDHannU τ hτ w j h1 h2
  have hb2_le : b ^ 2 ≤ bN ^ 2 := by nlinarith [hb_le_bN, hb0, hbN0]
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 0 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u τ) w|
        ≤ C * gaussDdim (3 / 2 * τ) w :=
    fun w hw => hEnearU τ hτ q hq w (le_trans hw hb2_le)
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  exact (cutoffResidual_narrow_tauUniform_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 0 Θ u τ) (fun x => deriv (fun s => heatParametrix 0 Θ u s x) τ)
    a b τ ha0 hab hτ hH2 hgisymm_q
    C hC0 hEnear_q Kcof' hKcof'0 hHann Kder hKder0 hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v

/-! ### (R2) The ceiling-threaded, `r₀`-hoisted consumer-width chart Gaussian bound. -/

/-- **R2 helper — `∀ f` naturality: the pullback-Laplacian naturality with the radius `f`-free.**
    Verbatim `laplaceBeltrami_uniformFlow_naturality`, but with the function `f` quantified AFTER the
    radius `r₀ = min ρ₀ (uniformFlowRadius …)` (which the original proof already chose independently of
    `f`).  This is the single fact that lets the transport identity's radius be hoisted OUTSIDE the
    `∀ τ` binder (the witness `f_τ` is τ-dependent, but the naturality radius is not). -/
theorem laplaceBeltrami_uniformFlow_naturality_forall_f (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a) :
    ∃ r₀ > (0 : ℝ), ∀ (f : Point n → ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      (∀ a b, ContDiffAt ℝ 1 (fun y => g y a b) (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 f (uniformFlowExp g gi hC hK q v) →
      IsUnit (QIQTH.PullbackMetric.matToCLM
        (fun a b => g (uniformFlowExp g gi hC hK q v) a b)) →
      (∀ p c, (∑ b, g (uniformFlowExp g gi hC hK q v) p b
          * gi (uniformFlowExp g gi hC hK q v) b c) = if p = c then (1 : ℝ) else 0) →
      (∀ p c, (∑ a, gi (uniformFlowExp g gi hC hK q v) p a
          * g (uniformFlowExp g gi hC hK q v) a c) = if p = c then (1 : ℝ) else 0) →
      laplaceBeltrami (QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun z => f (uniformFlowExp g gi hC hK q z)) v
        = laplaceBeltrami g gi f (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨ρ₀, hρ₀pos, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  refine ⟨min ρ₀ (uniformFlowRadius g gi hC hK),
    lt_min hρ₀pos (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro f q hq v hv hg1 hf hgU hGGi hGiG
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvR : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
  have hφreg : ∀ a, ContDiffAt ℝ 2 (fun y => uniformFlowExp g gi hC hK q y a) v :=
    fun a => contDiffAt2_uniformFlowExp_comp g gi hC hK q hq v hvR a
  have hφinv : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnondeg q hq v hvρ₀
  have hU : IsUnit (QIQTH.PullbackMetric.matToCLM
      (fun a b => QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q v a b)) :=
    QIQTH.PullbackMetric.uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit g gi hC hK q v hφinv hgU
  have hbridge : ∀ i j, pullbackMet g (uniformFlowExp g gi hC hK q) v i j
      = QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q v i j :=
    fun i j => pullbackMet_eq_uniformFlowPullbackMetric g gi hC hK q hq v hvR i j
  have hgtinv : ∀ p qq, (∑ k, uniformFlowPullbackMetricInv g gi hC hK q v p k
        * pullbackMet g (uniformFlowExp g gi hC hK q) v k qq) = if p = qq then (1 : ℝ) else 0 := by
    intro p qq
    rw [← uniformFlowPullbackMetricInv_mul_metric g gi hC hK q v hU p qq]
    exact Finset.sum_congr rfl fun k _ => by rw [hbridge k qq]
  have hL2 := laplaceBeltrami_pullback_naturality_local g gi (uniformFlowExp g gi hC hK q)
    (uniformFlowPullbackMetricInv g gi hC hK q) f hgsymm v hφinv hGGi hGiG
    hgtinv hg1 hφreg hf
  have hne : ∀ a b,
      (fun y => QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q y a b) =ᶠ[nhds v]
        (fun y => pullbackMet g (uniformFlowExp g gi hC hK q) y a b) := by
    intro a b
    have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ nhds v :=
      Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
    filter_upwards [hball] with w hw
    rw [mem_ball_zero_iff] at hw
    exact (pullbackMet_eq_uniformFlowPullbackMetric g gi hC hK q hq w hw a b).symm
  rw [laplaceBeltrami_congr_metric_nhds
      (QIQTH.PullbackMetric.uniformFlowPullbackMetric g gi hC hK q)
      (pullbackMet g (uniformFlowExp g gi hC hK q))
      (uniformFlowPullbackMetricInv g gi hC hK q)
      (fun z => f (uniformFlowExp g gi hC hK q z)) v hne]
  exact hL2

/-- **R2 helper — the residual transport identity, `r₀` HOISTED outside `∀ τ`.**  Verbatim
    `heatOp_globalWitness_eq_recentred_inChart` (W2), but with the single τ-free radius `r₀` (from the
    `∀ f` naturality) shared by ALL `τ`.  For `q ∈ K`, `‖v‖ < r₀`, and the germ + far-point hypotheses,
    the global-chart heat operator of the witness at `φ_q v` equals the recentred cutoff-residual. -/
theorem heatOp_globalWitness_eq_recentred_inChart_hoisted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) :
    ∃ r₀ > (0 : ℝ), ∀ (τ : ℝ) (q : Point n), q ∈ K → ∀ v : Point n, ‖v‖ < r₀ →
      (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
      (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q v) →
      IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
      (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
      (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
      heatOp g gi (globalCutoffParametrixWitness Θ u a b Vmap) τ
          (uniformFlowExp g gi hC hK q v) q
        = radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
  obtain ⟨r₀, hr₀pos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  refine ⟨r₀, hr₀pos, ?_⟩
  intro τ q hq v hv hgerm hg1 hf hU hGGi hGiG
  have hpt : Vmap q (uniformFlowExp g gi hC hK q v) = v := by
    simpa using hgerm.eq_of_nhds
  have hprofilegerm :
      (fun z => (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q z))
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : Vmap q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitness, hz']
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitness Θ u a b Vmap τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
    have hn := hnat (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q) q hq v hv hg1 hf
      hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  simp only [heatOp]
  have hterm1fun :
      (fun s => globalCutoffParametrixWitness Θ u a b Vmap s (uniformFlowExp g gi hC hK q v) q)
        = (fun s => radialCutoff a b v * heatParametrix 0 Θ u s v) := by
    funext s
    simp only [globalCutoffParametrixWitness, hpt]
  rw [hterm1fun, deriv_const_mul_field, hlap]

/-- **★★ R2 — `globalWitness_residual_bound_chartGaussian_final_below`.**  The J4-96 consumer-width
    chart Gaussian bound, ceiling-threaded and `r₀`-hoisted.  For any requested ceiling `ρc > 0` there
    is a SINGLE `(a,b,B)` with the cutoff far-radius `b < ρc`, and per `q ∈ K` a τ-FREE radius `r₀`
    (`= min (min r_transport δ_chart) r_disp`, all τ-free) such that for EVERY `τ > 0` and `‖v‖ < r₀`,
        `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdim (2τ) (φ_q v − q)`.
    The `∀ q ∃ r₀ ∀ τ` order is the honest hoist J4-98 flagged: the value of the transport radius is
    τ-free (`heatOp_globalWitness_eq_recentred_inChart_hoisted`), the chart germ radius is τ-free
    (`basepointInverseChart_spec`), and the near-isometry radius is τ-free (`uniformFlowExp_hdisp_ball`).
    Hypotheses are the genuine geometric/heat data only.  NOT `a₁ = R/6`. -/
theorem globalWitness_residual_bound_chartGaussian_final_below (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (ρc : ℝ) (hρc : 0 < ρc) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ b < ρc ∧ 0 ≤ B ∧
      ∀ q ∈ K, ∃ r₀ > (0 : ℝ), ∀ (τ : ℝ), 0 < τ → ∀ v : Point n, ‖v‖ < r₀ →
        |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ B * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
  obtain ⟨a, b, B0, ha, hab, hbρc, hB0, hAbound⟩ :=
    cutoffResidual_uniformFlow_unconditional_tau_narrow_below g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u hw0smooth hw0flat ρc hρc
  obtain ⟨rT, hrTpos, htrans⟩ :=
    heatOp_globalWitness_eq_recentred_inChart_hoisted g gi hC hK hgsymm Θ u a b
      (basepointInverseChart g gi hC hK)
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  refine ⟨a, b, B0 * Real.sqrt (2 / (3 / 2)) ^ n, ha, hab, hbρc, by positivity, ?_⟩
  intro q hq
  obtain ⟨δ, hδ, hspec⟩ := basepointInverseChart_spec g gi hC hK q hq
  refine ⟨min (min rT δ) r₁, lt_min (lt_min hrTpos hδ) hr₁pos, ?_⟩
  intro τ hτ v hv
  have hvT : ‖v‖ < rT := lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_left _ _))
  have hvδ : ‖v‖ < δ := lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_right _ _))
  have hvr₁ : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hgerm, hWc2⟩ := hspec v hvδ
  -- far-point hypotheses from the global data.
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
  -- the witness `C²` at `(τ, φ_q v)` from the chart `C²` composed with the smooth profile.
  have hf : ContDiffAt ℝ 2
      (fun x => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ x q)
      (uniformFlowExp g gi hC hK q v) := by
    have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 0 Θ u τ y)
        (basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)) := by
      apply ContDiffAt.mul
      · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      · have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
            = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
          funext x; rw [heatParametrix_folded]; simp
        have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
          rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
        exact hH.contDiffAt.of_le le_top
    exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
  -- transport identity → recentred residual, bounded by the engine, chart-transferred to width 2.
  rw [htrans τ q hq v hvT hgerm hg1 hf hU hGGi hGiG]
  have hnarrow := hAbound τ hτ q hq v
  have htransfer :
      gaussDdim (3 / 2 * τ) v
        ≤ Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
    gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
      (hdisp q hq v hvr₁)
  calc |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
      ≤ B0 * gaussDdim (3 / 2 * τ) v := hnarrow
    _ ≤ B0 * (Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) :=
        mul_le_mul_of_nonneg_left htransfer hB0
    _ = B0 * Real.sqrt (2 / (3 / 2)) ^ n
          * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by ring

/-! ### (R4) The summit — the `hEboundW` primitive, discharged to the K-uniform chart radius. -/

/-- **★★★★ R4 CAPSTONE — `gatedWitness_hEboundW_final`: the `hEboundW` primitive, τ-uniformity and
    radius-ordering DISCHARGED.**

    For the concrete gated witness, delivers the exact width-2 `hEboundW` primitive shape consumed by
    `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`:
        `∃ a b B S, 0<a ∧ a<b ∧ 0≤B ∧ ∀ τ p q, 0<τ →
           |heatOp g gi (gatedKernel K S H_w) τ p q| ≤ B · baseKernelW 2 0 τ p q`.

    Hypotheses are ONLY the genuine geometric/heat data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`/
    `Θ`/`u`/`hw0smooth`/`hw0flat`) PLUS the single isolated input `huniformChart`: a K-UNIFORM lower
    bound `δ₀` on the base-point inverse-chart radius (the germ + `C²` of `basepointInverseChart` and the
    open-image / compact-closure facts hold at `δ₀` for EVERY `q ∈ K`).  Every per-`q` piece already
    exists (`basepointInverseChart_spec`, `chartImage_ball_open_closure`); `huniformChart` asks only for
    a UNIFORM radius over the compact `K` — the quantitative uniform IFT radius, of which the K-uniform
    NONDEGENERACY radius is already supplied by `uniformFlowExp_common_nondeg_radius`.

    This DISCHARGES J4-98's `hgood` down to `huniformChart`: the τ-uniformity (via the τ-free transport,
    chart, and near-isometry radii — R2's hoist) and the per-`q` radius ordering `b < c < r₀`
    (via R1's ceiling-threaded engine, `ρc := min (min rN δ₀) r₁`) are now PROVED, not assumed.  The gate
    radius `c := (b + ρc)/2 ∈ (b, ρc)` sits strictly above the cutoff `b` and strictly below the τ-free
    transport radius `rN`, the uniform chart radius `δ₀`, and the near-isometry radius `r₁`.  NOT
    `a₁ = R/6`. -/
theorem gatedWitness_hEboundW_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (huniformChart : ∃ δ₀ > (0 : ℝ), ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (basepointInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ c : ℝ, 0 < c → c < δ₀ →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c)) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK))) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := huniformChart
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  obtain ⟨a, b, B0, ha, hab, hbρc, hB0, hAbound⟩ :=
    cutoffResidual_uniformFlow_unconditional_tau_narrow_below g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u hw0smooth hw0flat ρc hρc
  refine ⟨a, b, B0 * Real.sqrt (2 / (3 / 2)) ^ n, ha, hab, by positivity, ?_⟩
  -- discharge `hgood` of `gatedWitness_hEboundW_of_good` from `R1 + R2-style transport + huniformChart`.
  apply gatedWitness_hEboundW_of_good g gi hC hK Θ u a b (B0 * Real.sqrt (2 / (3 / 2)) ^ n) ha hab
    (by positivity)
  intro q hq
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
  refine ⟨c, hbc, ?_, ?_, ?_, ?_⟩
  · -- BOUND leg: transport identity (inline) + engine + chart transfer, for all `τ` on `‖v‖ < c`.
    intro τ hτ v hv
    have hvN : ‖v‖ < rN := lt_trans hv hc_rN
    have hvδ₀ : ‖v‖ < δ₀ := lt_trans hv hc_δ₀
    have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
    obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
    -- far-point hypotheses from global data.
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
    -- witness `C²` at `(τ, φ_q v)`.
    have hf : ContDiffAt ℝ 2
        (fun x => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ x q)
        (uniformFlowExp g gi hC hK q v) := by
      have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 0 Θ u τ y)
          (basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)) := by
        apply ContDiffAt.mul
        · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
        · have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
              = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
            funext x; rw [heatParametrix_folded]; simp
          have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
            rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
          exact hH.contDiffAt.of_le le_top
      exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
    -- inline transport identity (radius `rN`, shared with `ρc`).
    have hpt : basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
      simpa using hgerm.eq_of_nhds
    have hprofilegerm :
        (fun z => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ
            (uniformFlowExp g gi hC hK q z) q)
          =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) := by
      filter_upwards [hgerm] with z hz
      have hz' : basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z) = z := hz
      simp only [globalCutoffParametrixWitness, hz']
    have hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
      have hn := hnat
        (fun x => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ x q)
        q hq v hvN hg1 hf hU hGGi hGiG
      rw [← hn]
      exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
        (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
        _ _ v hprofilegerm
    have htransport :
        heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
            (uniformFlowExp g gi hC hK q v) q
          = radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q)
                (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
      simp only [heatOp]
      have hterm1fun :
          (fun s => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) s
              (uniformFlowExp g gi hC hK q v) q)
            = (fun s => radialCutoff a b v * heatParametrix 0 Θ u s v) := by
        funext s
        simp only [globalCutoffParametrixWitness, hpt]
      rw [hterm1fun, deriv_const_mul_field, hlap]
    rw [htransport]
    have hnarrow := hAbound τ hτ q hq v
    have htransfer :
        gaussDdim (3 / 2 * τ) v
          ≤ Real.sqrt (2 / (3 / 2)) ^ n
              * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
      gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
        (hdisp q hq v hvr₁)
    calc |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
        ≤ B0 * gaussDdim (3 / 2 * τ) v := hnarrow
      _ ≤ B0 * (Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) :=
          mul_le_mul_of_nonneg_left htransfer hB0
      _ = B0 * Real.sqrt (2 / (3 / 2)) ^ n
            * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by ring
  · -- INVERSE leg: from the uniform chart germ.
    intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
  · -- CONTINUITY leg: from the uniform chart `C²`.
    intro v hv
    have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
    exact (hchartGerm v hvδ₀).2.continuousAt
  · -- OPEN + CLOSURE legs: from the uniform chart open/closure facts at radius `c`.
    exact hchartOC c hc0 hc_δ₀

end QIQTH.HeatResidualBound
