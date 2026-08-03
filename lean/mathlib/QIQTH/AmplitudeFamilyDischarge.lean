/-
  AmplitudeFamilyDischarge — J4-154: discharging the amplitude `PdiffAt` / bounds interface family
  for the CONCRETE van-Vleck witness amplitude `chartFieldAmp`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the `a₁ = R/6` heat-kernel campaign (the F3-frontier amplitude-family item).  It supplies the
  amplitude field-differentiability (`PdiffAt`) and local sup-bound slots that
  `NormalFormDischarge.hNormalForm_concrete` (the `hAmp1`/`hAmp2` slots) and
  `EngineInstantiation`/`SliverAssembly` (the `|A| ≤ Ba`, `|∂A| ≤ Bd` factor bounds) carry for the
  concrete on-gate amplitude `chartFieldAmp = radialCutoff a b (W z ·) · Θ(W z ·)^{−1/2} · (u₀+u₁·τ)`
  of the gated `N = 1` van-Vleck parametrix.

  The `p`-dependence of `chartFieldAmp g gi hC hK a b τ z` runs entirely through the field-slot inverse
  chart `W z = uniformInverseChart g gi hC hK z`, exactly as the proven spatial-`C²` discharge
  `SpatialC2.hCH_discharge` handled the FULL witness (Gaussian × amplitude).  This file MIRRORS that
  route on the amplitude factor alone (dropping the `gaussDdim` factor).

  ── WHAT LANDS.
    • `amp_contDiffAt_general` — ★ for the amplitude at a GENERAL base `z`, given the honest field-
        chart-center `C²` carry `hWz : ContDiffAt ℝ 2 (W z) 0` and the Riemannian positivity carry
        `hdetz : 0 < det g (W z 0)`:  `ContDiffAt ℝ 2 (chartFieldAmp … z) 0`.  Route:  each factor
        (`radialCutoff∘W`, `Θ∘W`, its `−1/2` rpow, `u_k∘W`) is `ContDiffAt ℝ 2` at `0` via
        `ContDiffAt.comp`; product via `ContDiffAt.mul`.
    • `amp_contDiffAt_center` — ★★ the amplitude `C²` at BASE `z = 0`, GENUINELY PROVED (no chart
        carry): the base-`0` field chart is `C²` at the field centre
        (`ChartJetBounds.chartField_contDiffAt_center`, unconditional given `0 ∈ K`), and the RNC gauge
        `g(0) = δ` gives `det g(W₀ 0) = det g(0) = 1 > 0`.
    • `amp_pdiffAt_center` / `_general`      — the `hAmp1`-at-`0` fragment `PdiffAt (chartFieldAmp … z) i 0`
        (via `LaplaceBeltrami.PdiffAt_of_contDiffAt`, `C² ⟹ C¹`).
    • `amp_pd_pdiffAt_center` / `_general`   — ★★ the `hAmp2` slot exactly:
        `PdiffAt (fun y => pd (chartFieldAmp … z) i y) i 0` (via `PdiffAt_pd_of_contDiffAt`).
    • `amp_bound_center` / `_general`        — the amplitude sup-bound on a ball:
        `∃ r>0, ∃ M, ∀ p ∈ closedBall 0 r, |chartFieldAmp … z p| ≤ M` (continuity ⟹ local bound).
    • `amp_deriv_bound_center` / `_general`  — the field-derivative sup-bound on a ball:
        `∃ r>0, ∃ M, ∀ p ∈ closedBall 0 r, |pd (chartFieldAmp … z) i p| ≤ M` (the first partial is
        continuous near `0` since the amplitude is `C²`).
    • `chartField_contDiffAt_center_general` — the general-base provider of the `hWz` carry: an explicit
        `δ₀ > 0` s.t. for `z ∈ K` and `v` with `expᵤ z v = 0`, `‖v‖ < δ₀`, the field chart `W z` is `C²`
        at `0` (from `uniformInverseChart_huniformChart`; combine with `chartW0_rightInverse` to reach
        the field centre `0` as an image point).
    • `amp_hAmp1_of_globalC1`                — the honest reduction of the `∀ x` `hAmp1` family to the
        global-`C¹` regularity carry `∀ x, ContDiffAt ℝ 1 (chartFieldAmp … z) x`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, never the conclusion).
    • `hWz` / `hdetz` at a GENERAL base — the field-chart-center `C²` and Riemannian positivity.  Both
      PROVEN unconditionally at `z = 0`; at general `z ∈ K ∩ ball` they follow from the germ tower
      (`chartField_contDiffAt_center_general`) plus the near-isometry `‖W z 0‖`-smallness input.
    • The `∀ x` (GLOBAL) form of `hAmp1` reduces to global `C¹` of the amplitude — the chart is only
      known `C²` near image points, so the global family is carried (`amp_hAmp1_of_globalC1`), NOT the
      local `PdiffAt`-at-`0` fragment (which is PROVED).
    • The uniform-in-`z` constants of the sup-bounds (a compact-covering / continuity-in-`z` argument)
      are the per-`z` local bounds here; the uniform packaging is left to the sliver-integral brick.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CapstoneStatus
import QIQTH.NormalFormDischarge
import QIQTH.ChartJetBounds
import QIQTH.AmplitudePackage
import QIQTH.UniformChartRadius
import QIQTH.LaplaceBeltramiFiniteReg

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation QIQTH.HeatParametrixOrder
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators Topology Interval

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Local boundedness from continuity at the centre. -/

/-- A function continuous at the centre `0` is bounded on a small closed ball around `0`. -/
private theorem bound_of_continuousAt (f : Point n → ℝ) (hf : ContinuousAt f 0) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : Point n) r, |f p| ≤ M := by
  have htend : Filter.Tendsto f (𝓝 (0 : Point n)) (𝓝 (f 0)) := hf
  have hev : ∀ᶠ p in 𝓝 (0 : Point n), |f p| ≤ |f 0| + 1 := by
    filter_upwards [Metric.tendsto_nhds.mp htend 1 one_pos] with p hp
    have hlt : |f p - f 0| < 1 := by rw [Real.dist_eq] at hp; exact hp
    have key : |f p| - |f 0| ≤ |f p - f 0| := abs_sub_abs_le_abs_sub (f p) (f 0)
    linarith
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by linarith, |f 0| + 1, fun p hp => ?_⟩
  exact hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) (half_lt_self hε))

/-! ### A1/A3 — the amplitude `C²` at the field centre (general base + base `0`). -/

/-- **★ A3 — `amp_contDiffAt_general`.**  For the concrete on-gate amplitude `chartFieldAmp` at a
    GENERAL base `z`, the amplitude is `ContDiffAt ℝ 2` at the field centre `0`, given the two honest
    carries:  the field-chart-centre `C²` `hWz : ContDiffAt ℝ 2 (W z) 0` and the Riemannian positivity
    `hdetz : 0 < det g (W z 0)`.  Each of the four factors — `radialCutoff∘W`, `Θ∘W`, its `−1/2`
    rpow branch (`Θ(W z 0) > 0` from `vanVleck_pos`), and the two transport coefficients `u_k∘W` — is
    `ContDiffAt ℝ 2` at `0` via `ContDiffAt.comp`; assembled by `ContDiffAt.mul`.  NOT `a₁ = R/6`. -/
theorem amp_contDiffAt_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n))
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))) :
    ContDiffAt ℝ 2 (chartFieldAmp g gi hChr hK a b τ z) (0 : Point n) := by
  have hcut : ContDiffAt ℝ 2
      (fun p => radialCutoff a b (uniformInverseChart g gi hChr hK z p)) (0 : Point n) :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp 0 hWz
  have hvv : ContDiffAt ℝ 2
      (fun p => vanVleck g (uniformInverseChart g gi hChr hK z p)) (0 : Point n) :=
    (vanVleck_contDiffAt g hg (uniformInverseChart g gi hChr hK z 0) hdetz (k := 2)).comp 0 hWz
  have hne : (fun p => vanVleck g (uniformInverseChart g gi hChr hK z p)) (0 : Point n) ≠ 0 :=
    ne_of_gt (vanVleck_pos g (uniformInverseChart g gi hChr hK z 0) hdetz)
  have hrpow : ContDiffAt ℝ 2
      (fun p => vanVleck g (uniformInverseChart g gi hChr hK z p) ^ (-(1 : ℝ) / 2)) (0 : Point n) :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0
        (uniformInverseChart g gi hChr hK z p)) (0 : Point n) :=
    (((hu 0).contDiffAt).of_le le_top).comp 0 hWz
  have hu1 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1
        (uniformInverseChart g gi hChr hK z p)) (0 : Point n) :=
    (((hu 1).contDiffAt).of_le le_top).comp 0 hWz
  have hsum : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0
          (uniformInverseChart g gi hChr hK z p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hChr hK z p) * τ) (0 : Point n) :=
    hu0.add (hu1.mul contDiffAt_const)
  -- `chartFieldAmp … z` is definitionally this product; assemble and close by defeq.
  exact hcut.mul (hrpow.mul hsum)

/-- **★★ A1 — `amp_contDiffAt_center`.**  The concrete amplitude at BASE `z = 0` is `ContDiffAt ℝ 2`
    at the field centre `0`, GENUINELY PROVED (no chart carry).  The base-`0` field chart
    `W₀ = uniformInverseChart g gi hChr hK 0` is `C²` at the field centre
    (`ChartJetBounds.chartField_contDiffAt_center`, unconditional given `0 ∈ K`) with `W₀ 0 = 0`, and
    the RNC gauge `g(0) = δ` gives `det g(W₀ 0) = det g(0) = 1 > 0`.  Instantiates
    `amp_contDiffAt_general`.  NOT `a₁ = R/6`. -/
theorem amp_contDiffAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (chartFieldAmp g gi hChr hK a b τ 0) (0 : Point n) := by
  have hW2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK 0) (0 : Point n) :=
    chartField_contDiffAt_center g gi hChr hK hK0
  have hW0 : uniformInverseChart g gi hChr hK 0 0 = 0 :=
    chartField_centerValue_base0 g gi hChr hK hK0
  have hgmat : (fun i j => g 0 i j) = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hdet0 : Matrix.det (g 0) = 1 := by
    rw [show (g 0) = (1 : Matrix (Fin n) (Fin n) ℝ) from hgmat, Matrix.det_one]
  have hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK 0 0)) := by
    rw [hW0, hdet0]; norm_num
  exact amp_contDiffAt_general g gi hChr hK a b τ 0 hg hu hW2 hdetz

/-! ### A1/A3 — the `PdiffAt` slots (`hAmp1`-at-`0` fragment and `hAmp2`). -/

/-- **A3 — `amp_pdiffAt_general`.**  The `hAmp1`-at-`0` fragment for a general base:
    `PdiffAt (chartFieldAmp … z) i 0`.  (`C² ⟹ C¹ ⟹ PdiffAt`.)  NOT `a₁ = R/6`. -/
theorem amp_pdiffAt_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n))
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))) :
    PdiffAt (chartFieldAmp g gi hChr hK a b τ z) i (0 : Point n) :=
  QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ i 0
    ((amp_contDiffAt_general g gi hChr hK a b τ z hg hu hWz hdetz).of_le (by norm_num))

/-- **A1 — `amp_pdiffAt_center`.**  The `hAmp1`-at-`0` fragment at base `0`, unconditional. -/
theorem amp_pdiffAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (hK0 : (0 : Point n) ∈ K) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    PdiffAt (chartFieldAmp g gi hChr hK a b τ 0) i (0 : Point n) :=
  QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ i 0
    ((amp_contDiffAt_center g gi hChr hK a b τ hK0 hg hg0 hu).of_le (by norm_num))

/-- **★★ A3 — `amp_pd_pdiffAt_general`.**  The `hAmp2` slot for a general base, EXACTLY as carried by
    `hNormalForm_concrete`:  `PdiffAt (fun y => pd (chartFieldAmp … z) i y) i 0`
    (`C² ⟹` second partial exists).  NOT `a₁ = R/6`. -/
theorem amp_pd_pdiffAt_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n))
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))) :
    PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b τ z) i y) i (0 : Point n) :=
  QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt _ i i 0
    (amp_contDiffAt_general g gi hChr hK a b τ z hg hu hWz hdetz)

/-- **★★ A1 — `amp_pd_pdiffAt_center`.**  The `hAmp2` slot at base `0`, unconditional. -/
theorem amp_pd_pdiffAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (hK0 : (0 : Point n) ∈ K) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b τ 0) i y) i (0 : Point n) :=
  QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt _ i i 0
    (amp_contDiffAt_center g gi hChr hK a b τ hK0 hg hg0 hu)

/-! ### A2 — the amplitude and field-derivative sup-bounds on a ball. -/

/-- **A2 — `amp_bound_center`.**  The amplitude sup-bound on a ball at base `0`:
    `∃ r>0, ∃ M, ∀ p ∈ closedBall 0 r, |chartFieldAmp … 0 p| ≤ M`.  Continuity of the (proven `C²`)
    amplitude at `0` gives local boundedness.  This supplies the `|A| ≤ Ba` factor-bound slot of E2 at
    the field centre.  NOT `a₁ = R/6`. -/
theorem amp_bound_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : Point n) r,
      |chartFieldAmp g gi hChr hK a b τ 0 p| ≤ M :=
  bound_of_continuousAt _ (amp_contDiffAt_center g gi hChr hK a b τ hK0 hg hg0 hu).continuousAt

/-- **A2/A3 — `amp_bound_general`.**  The amplitude sup-bound on a ball at a general base. -/
theorem amp_bound_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n))
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : Point n) r,
      |chartFieldAmp g gi hChr hK a b τ z p| ≤ M :=
  bound_of_continuousAt _ (amp_contDiffAt_general g gi hChr hK a b τ z hg hu hWz hdetz).continuousAt

/-- **Continuity of the first field partial of the amplitude at the centre.**  From the amplitude `C²`
    at `0`, the first partial `y ↦ pd A i y` is continuous at `0`:  near `0` the amplitude is
    differentiable so `pd A i = (fderiv A ·) (eᵢ)` (`pd_eq_fderiv`), and `fderiv A` is `C¹` hence
    continuous. -/
private theorem amp_pd_continuousAt_of_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hC2 : ContDiffAt ℝ 2 (chartFieldAmp g gi hChr hK a b τ z) (0 : Point n)) :
    ContinuousAt (fun y => pd (chartFieldAmp g gi hChr hK a b τ z) i y) (0 : Point n) := by
  have hdiff : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (chartFieldAmp g gi hChr hK a b τ z) y := by
    filter_upwards [hC2.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have heq : (fun y => pd (chartFieldAmp g gi hChr hK a b τ z) i y) =ᶠ[𝓝 (0 : Point n)]
      (fun y => (fderiv ℝ (chartFieldAmp g gi hChr hK a b τ z) y) (Pi.single i 1)) := by
    filter_upwards [hdiff] with y hy using pd_eq_fderiv (chartFieldAmp g gi hChr hK a b τ z) i y hy
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ (chartFieldAmp g gi hChr hK a b τ z) y) (0 : Point n) :=
    hC2.fderiv_right (m := 1) (by norm_num)
  have hcontF : ContinuousAt
      (fun y => (fderiv ℝ (chartFieldAmp g gi hChr hK a b τ z) y) (Pi.single i 1)) (0 : Point n) :=
    hfd.continuousAt.clm_apply continuousAt_const
  exact hcontF.congr heq.symm

/-- **A2 — `amp_deriv_bound_center`.**  The field-derivative sup-bound on a ball at base `0`:
    `∃ r>0, ∃ M, ∀ p ∈ closedBall 0 r, |pd (chartFieldAmp … 0) i p| ≤ M`.  Supplies the `|∂A| ≤ Bd`
    factor-bound slot of E2 at the field centre.  NOT `a₁ = R/6`. -/
theorem amp_deriv_bound_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (hK0 : (0 : Point n) ∈ K) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : Point n) r,
      |pd (chartFieldAmp g gi hChr hK a b τ 0) i p| ≤ M :=
  bound_of_continuousAt _
    (amp_pd_continuousAt_of_contDiffAt g gi hChr hK a b τ 0 i
      (amp_contDiffAt_center g gi hChr hK a b τ hK0 hg hg0 hu))

/-- **A2/A3 — `amp_deriv_bound_general`.**  The field-derivative sup-bound on a ball at a general
    base. -/
theorem amp_deriv_bound_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n))
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ p ∈ Metric.closedBall (0 : Point n) r,
      |pd (chartFieldAmp g gi hChr hK a b τ z) i p| ≤ M :=
  bound_of_continuousAt _
    (amp_pd_continuousAt_of_contDiffAt g gi hChr hK a b τ z i
      (amp_contDiffAt_general g gi hChr hK a b τ z hg hu hWz hdetz))

/-! ### A3 — the general-base provider of the field-chart-centre `C²` carry `hWz`. -/

/-- **A3 — `chartField_contDiffAt_center_general`.**  A single radius `δ₀ > 0` over `K` such that
    whenever the field centre `0` is an IMAGE point of the base-`z` exponential map with pre-image `v`
    of size `‖v‖ < δ₀` (i.e. `expᵤ z v = 0`), the field chart `W z` is `ContDiffAt ℝ 2` at the field
    centre `0`.  This is the `hWz` provider for the general-base amplitude theorems: at `z = 0`,
    `v = W₀ 0 = 0` (`chartField_centerValue_base0`); at general `z ∈ K ∩ ball`, take `v = W z 0` and
    combine with `chartW0_rightInverse` (`expᵤ z (W z 0) = 0`) and the near-isometry `‖W z 0‖`-bound.
    Straight from `uniformInverseChart_huniformChart`.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt_center_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n,
      uniformFlowExp g gi hChr hK z v = 0 → ‖v‖ < δ₀ →
      ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) (0 : Point n) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hChr hK
  refine ⟨δ₀, hδ₀, fun z hz v hexp hvlt => ?_⟩
  have h2 := ((hspec z hz).1 v hvlt).2
  rwa [hexp] at h2

/-! ### A4 — the honest global reduction of the `∀ x` `hAmp1` family. -/

/-- **A4 — `amp_hAmp1_of_globalC1`.**  The full `∀ x` `hAmp1` family carried by `hNormalForm_concrete`,
    reduced HONESTLY to the global-`C¹` regularity of the amplitude.  Since the field chart `W z` is
    only known `C²` near image points, the GLOBAL `PdiffAt`-at-every-`x` family cannot be produced from
    the local centre `C²` alone; it is exactly the global-`C¹` carry, discharged pointwise by
    `PdiffAt_of_contDiffAt`.  (The `PdiffAt`-at-`0` FRAGMENT is PROVED — see `amp_pdiffAt_center`.)
    Non-vacuous, never the conclusion.  NOT `a₁ = R/6`. -/
theorem amp_hAmp1_of_globalC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hAmpC1 : ∀ x, ContDiffAt ℝ 1 (chartFieldAmp g gi hChr hK a b τ z) x) :
    ∀ x, PdiffAt (chartFieldAmp g gi hChr hK a b τ z) i x :=
  fun x => QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ i x (hAmpC1 x)

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms amp_contDiffAt_general
#print axioms amp_contDiffAt_center
#print axioms amp_pdiffAt_center
#print axioms amp_pd_pdiffAt_center
#print axioms amp_bound_center
#print axioms amp_deriv_bound_center
#print axioms amp_pd_pdiffAt_general
#print axioms chartField_contDiffAt_center_general
#print axioms amp_hAmp1_of_globalC1
end AxiomChecks
