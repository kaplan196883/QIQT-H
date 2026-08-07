/-
  AnnulusUniformization — J4-379: THE FLOW-FRAME UNIFORMIZATION of the annulus (off-plateau) affine
  leg's analytic core (the annulus counterpart of `QIQTH.LegUniformization`, J4-378).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  UNIFORMIZATION / GLUE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  The banked
  per-point annulus leg `QIQTH.AnnulusAmbientTransfer.gatedHeatOp_affine_onAnnulus` (J4-376) emits its
  affine coefficient pair `(P₀, P₁)` as a PER-POINT existential fed by per-point coefficient carries
  (the width-`5/4` near-diag residual `hEnear`, the value/derivative cofactor bounds `hHann`/`hDHann`,
  the metric/cutoff carries `hgibd`/`hDchi`/`hLapChi`).  The 3-region capstone
  `QIQTH.AffineGateCapstone.affineGateBound_of_legs` (J4-377) demands a SINGLE `(P₀, P₁)` valid
  uniformly over `q ∈ K`, over the whole annulus, and over all `τ > 0`.  This file performs the annulus
  uniformization: it lifts the width-`1` uniform residual bound (the internal `hwidth1` of J4-378's
  `plat_residual_uniform_width43`) to a standalone lemma, folds it `1 → 5/4` into the near-diagonal
  QUAD supplier, obtains the six banked compact-`K` uniform annulus suppliers ONCE, and re-runs the
  annulus AMBIENT transfer assembly with a genuine τ-AFFINE re-fold of the τ-dependent
  value/derivative constants, yielding a SINGLE uniform pair `(B₀, B₁)` over `K` in the EXACT binder
  shape the 3-region capstone consumes.

  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable
  hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing file edited, nothing
  committed.  `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-wiring stack AND on the
  surviving LABELLED inputs (the two uniform coefficient bounds `hCoeffU0`/`hCoeffLin1` and the
  geometric data piles).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## DELIVERABLES.
  •  (A1a) `width1_residual_uniform` — the width-`1` uniform pullback-metric `N = 1` residual envelope
     over `K` (the lifted internal `hwidth1` of J4-378).  NOT `a₁ = R/6`.
  •  (A1b) `hEnear_uniform` — the width-`5/4` QUAD near-diagonal residual supplier (`hEnear`'s shape):
     `width1_residual_uniform` folded `1 → 5/4` via `gaussDdim_le_gaussDdim_narrow54`.  NOT `a₁ = R/6`.
  •  (A2)  `gatedHeatOp_annulus_uniform` — ★★ the UNIFORMIZED ANNULUS LEG: a SINGLE `(a, b, P₀, P₁)`
     bounding the gated witness's `heatOp` at the exp point by the ambient width-`4/3` affine QUAD
     envelope on `z := uniformFlowExp q v − q`, uniformly over `q ∈ K` and the annulus
     `a² ≤ rncRadialSq v ≤ b²` and all `τ > 0`, in the EXACT `affineGateBound_of_legs` `hann` binder
     shape.  Obtains the six annulus suppliers ONCE and re-runs the AMBIENT annulus transfer (W2) with
     the τ-affine re-fold, reusing the leg-agnostic plateau `hpt`/`hlap` glue block.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AffineRawResidual
import QIQTH.Transfer43Quad
import QIQTH.UniformFlowJetZero
import QIQTH.UniformResidualBound
import QIQTH.OnGateGlue
import QIQTH.UniformChartRadius
import QIQTH.RadiusOrdering
import QIQTH.GlobalWitnessHunif
import QIQTH.SmoothCutoff
import QIQTH.VanVleckCancellation
import QIQTH.AnnulusAmbientTransfer
import QIQTH.AffineGateTransport
import QIQTH.AffineGateCapstone
import QIQTH.GlobalHunifAssembly
import QIQTH.UniformFlowMetricInvProps
import QIQTH.CutoffAnnulusBounds
import QIQTH.WidthMarginEngine
import QIQTH.CoeffU1Fix
import QIQTH.HgateAffineRepair

open Set Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.RNCDecay
open QIQTH.GaussianPolyBound QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.AnnulusAmbientTransfer
open scoped Topology BigOperators ContDiff

namespace QIQTH.AnnulusUniformization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A1a) — the width-`1` uniform residual envelope (lifted `hwidth1`).
    ############################################################################### -/

/-- **★ (A1a) — `width1_residual_uniform`.**  THE WIDTH-`1` UNIFORM PLATEAU/ANNULUS RESIDUAL ENVELOPE.
    A single coefficient pair `(P₀, P₁)` and radius `ρ > 0` such that, uniformly over `q ∈ K` and over
    `v` with `‖v‖ < ρ` and all `τ > 0`, the pullback-metric `N = 1` parametrix residual is bounded by
    the affine width-`1` quadratic envelope on `v`:
        `|parametrixResidualN 1 g̃_q g̃i_q Θ u τ v|
            ≤ (P₀ + P₁·τ)·(((r²/τ)² + r²/τ + 1)·gaussDdim τ v)`.
    This is the internal `hwidth1` of J4-378's `plat_residual_uniform_width43` lifted to a standalone
    lemma (the near-isometry `1 → 4/3` chart fold is NOT applied — the width-`1` core is the exact
    starting point the width-`5/4` annulus supplier needs).  NOT `a₁ = R/6`. -/
theorem width1_residual_uniform (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ ρ P₀ P₁ : ℝ, 0 < ρ ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ (P₀ + P₁ * τ)
            * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  classical
  obtain ⟨r_d, hr_d0, Md, hMd0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨r_L0, hr_L00, L0, hL00, hlap0U⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u (hw 0)
  obtain ⟨r_L1, hr_L10, L1, hL10, hlap1U⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ (fun j => u (j + 1)) (hw 1)
  set ρ : ℝ := min r_d (min r_L0 (min r_L1 ρ_c)) with hρdef
  have hρ0 : 0 < ρ := lt_min hr_d0 (lt_min hr_L00 (lt_min hr_L10 hρ_c))
  obtain ⟨W0, hW00, hW0bd⟩ : ∃ W0 : ℝ, 0 ≤ W0 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ, |foldedCoeff Θ u 0 v| ≤ W0 := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ).exists_bound_of_continuousOn
        (hw 0).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨W1, hW10, hW1bd⟩ : ∃ W1 : ℝ, 0 ≤ W1 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ, |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  set P0₁ : ℝ := (L0 + C_c0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0) + W1 + C_c1 with hP0₁def
  set P1₁ : ℝ := C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1 with hP1₁def
  have hP0₁0 : 0 ≤ P0₁ := by rw [hP0₁def]; positivity
  have hP1₁0 : 0 ≤ P1₁ := by rw [hP1₁def]; positivity
  refine ⟨ρ, P0₁, P1₁, hρ0, hP0₁0, hP1₁0, ?_⟩
  intro τ hτ q hq v hv
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL0 : ‖v‖ < r_L0 := lt_of_lt_of_le hv ((min_le_right _ _).trans (min_le_left _ _))
  have hvL1 : ‖v‖ < r_L1 :=
    lt_of_lt_of_le hv ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hvc : ‖v‖ < ρ_c :=
    lt_of_lt_of_le hv ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hdev : ∀ i j : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v i j
      - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v := fun i j => hdevU q hq v hvd i j
  have hlap0 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L0 := hlap0U q hq v hvL0
  have hlap1 : |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ (fun j => u (j + 1)) 0) v| ≤ L1 :=
    hlap1U q hq v hvL1
  have hcoeff0 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v := hCoeffU0 q hq v hvc
  have hcoeff1 : |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v := hCoeffLin1 q hq v hvc
  have hw0bd : |foldedCoeff Θ u 0 v| ≤ W0 := hW0bd v hvball
  have hw1bd : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W1 := hW1bd v hvball
  have hcd0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := (hw 0).contDiffAt.of_le le_top
  have hcd1 : ContDiffAt ℝ 2 (foldedCoeff Θ (fun j => u (j + 1)) 0) v :=
    (hw 1).contDiffAt.of_le le_top
  set gM : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hgMdef
  set giM : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hgiMdef
  have hA := QIQTH.AffineRawResidual.rawResidualN0_graded_quadPoly_width1 gM giM Θ u hτ v hcd0
    C_c0 Md W0 L0 hC_c0 hMd0 hW00 hL00 hcoeff0 hdev hw0bd hlap0
  have hmideq : heatParametrix 0 Θ (fun j => u (j + 1)) τ v
      = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
    rw [heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
  have hq1poly : (1 : ℝ) ≤ (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1 := by
    nlinarith [sq_nonneg (rncRadialSq v / τ), div_nonneg (rncRadialSq_nonneg v) hτ.le]
  have hB : |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
      ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [hmideq, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W1 := mul_le_mul_of_nonneg_left hw1bd (gaussDdim_nonneg τ v)
      _ = W1 * (1 * gaussDdim τ v) := by ring
      _ ≤ W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
          apply mul_le_mul_of_nonneg_left _ hW10
          exact mul_le_mul_of_nonneg_right hq1poly (gaussDdim_nonneg τ v)
  have hCbr : |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v|
      ≤ (C_c1 + (C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
    rw [abs_mul, abs_of_pos hτ]
    exact QIQTH.AffineRawResidual.tauResidualN0_Or_graded_quadPoly_width1 gM giM Θ
      (fun j => u (j + 1)) hτ v hcd1 C_c1 Md W1 L1 hC_c1 hMd0 hW10 hL10 hcoeff1 hdev hw1bd hlap1
  rw [parametrixResidual_one_split gM giM Θ u τ hτ v hw]
  calc |parametrixResidualN 0 gM giM Θ u τ v
          + heatParametrix 0 Θ (fun j => u (j + 1)) τ v
          + τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v|
      ≤ |parametrixResidualN 0 gM giM Θ u τ v
          + heatParametrix 0 Θ (fun j => u (j + 1)) τ v|
          + |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v| :=
        abs_add_le _ _
    _ ≤ (|parametrixResidualN 0 gM giM Θ u τ v|
          + |heatParametrix 0 Θ (fun j => u (j + 1)) τ v|)
          + |τ * parametrixResidualN 0 gM giM Θ (fun j => u (j + 1)) τ v| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ ((L0 + C_c0 + (1 / 4) * (n : ℝ) ^ 2 * Md * W0)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v)
            + W1 * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v))
          + (C_c1 + (C_c1 + (1 / 4) * (n : ℝ) ^ 2 * Md * W1 + L1) * τ)
              * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) :=
        add_le_add (add_le_add hA hB) hCbr
    _ = (P0₁ + P1₁ * τ)
          * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
        rw [hP0₁def, hP1₁def]; ring

/-! ###############################################################################
    ### (A1b) — the width-`5/4` QUAD near-diagonal residual supplier.
    ############################################################################### -/

/-- **★ (A1b) — `hEnear_uniform`.**  THE WIDTH-`5/4` QUAD NEAR-DIAGONAL RESIDUAL SUPPLIER (`hEnear`'s
    shape).  Folds the width-`1` uniform residual envelope `width1_residual_uniform` `1 → 5/4` via the
    free pure-Gaussian upgrade `AnnulusAmbientTransfer.gaussDdim_le_gaussDdim_narrow54` (`gaussDdim τ v
    ≤ √(5/4)ⁿ·gaussDdim (5/4·τ) v`), depositing the normalizer `√(5/4)ⁿ` into both coefficients.  The
    result is exactly the near-diagonal carry the ambient annulus transfer consumes:
        `|∂_τ(heatParametrix 1 · v)
            − Δ_{g̃_q}(heatParametrix 1 τ ·) v| ≤ (C₀ + C₁·τ)·(((r²/τ)² + r²/τ + 1)·gaussDdim (5/4·τ) v)`.
    NOT `a₁ = R/6`. -/
theorem hEnear_uniform (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ ρ C₀ C₁ : ℝ, 0 < ρ ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ w : Point n, ‖w‖ < ρ →
      |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
        ≤ (C₀ + C₁ * τ)
            * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1) * gaussDdim (5 / 4 * τ) w) := by
  obtain ⟨ρ, P₀, P₁, hρ0, hP₀, hP₁, hres⟩ :=
    width1_residual_uniform g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  refine ⟨ρ, P₀ * Real.sqrt (5 / 4) ^ n, P₁ * Real.sqrt (5 / 4) ^ n, hρ0,
    by positivity, by positivity, ?_⟩
  intro τ hτ q hq w hw'
  have h := hres τ hτ q hq w hw'
  simp only [parametrixResidualN] at h
  have hfold : gaussDdim τ w ≤ Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) w :=
    QIQTH.AnnulusAmbientTransfer.gaussDdim_le_gaussDdim_narrow54 hτ w
  have hX0 : 0 ≤ rncRadialSq w / τ := div_nonneg (rncRadialSq_nonneg w) hτ.le
  have hQ0 : 0 ≤ (rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hX0) zero_le_one
  have hfac0 : 0 ≤ P₀ + P₁ * τ := add_nonneg hP₀ (mul_nonneg hP₁ hτ.le)
  calc |deriv (fun s => heatParametrix 1 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 1 Θ u τ) w|
      ≤ (P₀ + P₁ * τ)
          * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1) * gaussDdim τ w) := h
    _ ≤ (P₀ + P₁ * τ)
          * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1)
              * (Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) w)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfold hQ0) hfac0
    _ = (P₀ * Real.sqrt (5 / 4) ^ n + P₁ * Real.sqrt (5 / 4) ^ n * τ)
          * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1) * gaussDdim (5 / 4 * τ) w) := by ring

/-! ###############################################################################
    ### (A2) — ★★ the uniformized annulus leg (`hann_uniform`).
    ############################################################################### -/

/-- **★★ (A2) — `gatedHeatOp_annulus_uniform`.**  THE UNIFORMIZED ANNULUS LEG (`hann_uniform`).  The
    single-`(P₀, P₁)` version of the banked per-point annulus leg
    `AnnulusAmbientTransfer.gatedHeatOp_affine_onAnnulus`, in the EXACT binder shape the 3-region
    capstone `AffineGateCapstone.affineGateBound_of_legs` consumes for its `hann` hypothesis
    (specialized to the concrete chart `W = uniformInverseChart g gi hC hK`): a SINGLE cutoff radius
    pair `(a, b)` and coefficient pair `(P₀, P₁)`, valid uniformly over `q ∈ K`, over the whole annulus
    `a² ≤ rncRadialSq v ≤ b²`, and over all `τ > 0`, bounding the GATED witness's `heatOp` at the exp
    point by the ambient width-`4/3` affine QUAD envelope on `z := uniformFlowExp g gi hC hK q v − q`.

    ROUTE: obtain the width-`5/4` near-diagonal QUAD supplier `hEnear_uniform` ONCE (giving `ρ, C₀, C₁`),
    the ambient annulus transfer `cutoffResidual_annulusAmbient43_bound` (radius `r₁`), and the compact-`K`
    uniform annulus suppliers (metric-inverse entry, cutoff Laplacian, cutoff derivative, and the value /
    derivative cofactor bounds at width `5/4` for the base / shifted van-Vleck profiles); choose
    `b := m/2`, `a := m/4` below `m := min ρ (min r₁ (min rKg (min rKc2 (min δ₀ rN))))`.  For each point,
    discharge the transport glue `hpt`/`hlap` exactly as J4-378's plateau leg, split the `heatParametrix 1`
    value / derivative into the τ-AFFINE combination `(Kcof0 + τ·Kcof1)` / `(Kder0 + τ·Kder1)`, feed the
    ambient annulus transfer (W2), and re-fold its τ-affine coefficient into a SINGLE uniform pair
    `(B₀, B₁)` over `K`.  The carries `hCoeffU0`/`hCoeffLin1` are the banked satisfiable uniform outputs;
    the geometric data and folded smoothness are genuine; NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem gatedHeatOp_annulus_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (S : Point n → Set (Point n))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ a b P₀ P₁ : ℝ, 0 < a ∧ a < b ∧ 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
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
  -- the width-`5/4` near-diagonal QUAD supplier (radius `ρ`), obtained ONCE.
  obtain ⟨ρ, C₀, C₁, hρ0, hC₀0, hC₁0, hEnearU⟩ :=
    hEnear_uniform g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1
  -- the ambient annulus transfer (W2), radius `r₁`.
  obtain ⟨r₁, hr₁pos, hW2⟩ :=
    QIQTH.AnnulusAmbientTransfer.cutoffResidual_annulusAmbient43_bound g gi hC hK
  -- the metric-inverse entry annulus bound (radius `rKg`, constant `Kg`).
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  -- the cutoff-Laplacian annulus bound (radius `rKc2`).
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  -- the uniform chart germ (radius `δ₀`) and Laplacian naturality (radius `rN`).
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set m : ℝ := min ρ (min r₁ (min rKg (min rKc2 (min δ₀ rN)))) with hmdef
  have hm0 : 0 < m :=
    lt_min hρ0 (lt_min hr₁pos (lt_min hrKg0 (lt_min hrKc20 (lt_min hδ₀ hrNpos))))
  set b : ℝ := m / 2 with hbdef
  set a : ℝ := m / 4 with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hb_nonneg : (0 : ℝ) ≤ b := hb0.le
  have hbm : b < m := by rw [hbdef]; linarith
  have hbρ : b < ρ := lt_of_lt_of_le hbm (min_le_left _ _)
  have hbr : b < r₁ := lt_of_lt_of_le hbm ((min_le_right _ _).trans (min_le_left _ _))
  have hb_lt_rKg : b < rKg :=
    lt_of_lt_of_le hbm ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb_lt_rKc2 : b < rKc2 :=
    lt_of_lt_of_le hbm ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hbδ₀ : b < δ₀ :=
    lt_of_lt_of_le hbm ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbrN : b < rN :=
    lt_of_lt_of_le hbm ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  -- the `a,b`-dependent uniform annulus suppliers.
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
  refine ⟨a, b,
    25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
        * (C₀ + Kcof0 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder0),
    25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
        * (Kcof1 * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder1 + C₁),
    ha0, hab, by positivity, by positivity, ?_⟩
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

end QIQTH.AnnulusUniformization

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AnnulusUniformization.width1_residual_uniform
#print axioms QIQTH.AnnulusUniformization.hEnear_uniform
#print axioms QIQTH.AnnulusUniformization.gatedHeatOp_annulus_uniform
