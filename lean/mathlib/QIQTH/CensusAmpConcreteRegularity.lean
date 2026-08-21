/-
  CensusAmpConcreteRegularity — the CONCRETE amplitude half of junction piece (3) of J4-933's
  `hCensusBound` re-audit: the census weights `chartFieldAmp·F` (q₁) and `censusAmpTauDeriv·F` (q₂)
  are made CONCRETE in their AMPLITUDE factor.  J4-931/932 (`paired_ratio_center_lipschitz` /
  `transported_ratio_regularity`) take an ABSTRACT bounded+Lipschitz weight `P` (e.g. `amp·F`); this
  file pins `P`'s amplitude factor to the ACTUAL concrete chart amplitude `chartFieldAmp … τ z 0` and
  its `∂_τ`-slope `censusAmpTauDeriv`, discharging their base-ball bounded+Lipschitz regularity
  UNCONDITIONALLY at base `0` (given only the standard g/gi smoothness carries `hg`/`hg0`/`hu`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT THIS DOES — AND DOES NOT — CLOSE (honest).
  Piece (3) of J4-933's re-audit is "concrete `amp·F`/`Cfield·F` bounded+Lipschitz inputs to
  J4-931/932".  This file discharges the **AMPLITUDE FACTORS** (`amp = chartFieldAmp`, `Cfield =
  censusAmpTauDeriv`) as CONCRETE base-ball bounded+Lipschitz functions (unconditional at base `0`),
  reducing the `amp·F` / `Cfield·F` weight regularity to the SINGLE remaining honest carry: the Levi
  kernel `F = leviSeries` being ball-locally bounded+Lipschitz in the base variable (which is
  downstream of the `Ebound`/`heatConv` analytic carries, i.e. the `{hDuhamel, hDConv, hCConv}`-family
  input — NOT proved here).  So: the AMPLITUDE half of piece (3) is CLOSED concretely; the F factor
  remains an explicit abstract carry.

  ## WHAT LANDS (amplitude side unconditional at base `0`; ratio side conditional on `hbaseC2`).
    • `chartFieldAmp_apply_eq_chartAmp` — the value bridge `chartFieldAmp … τ z 0 = chartAmp … τ z 0`
        (pure `mul_assoc`; lets the banked `DataAmpAssembly` chart-amplitude regularity be reused).
    • `chartFieldAmp_base_regularity_center` — ★ the CONCRETE amplitude `z ↦ chartFieldAmp … τ z 0` is
        bounded (`M_A`) AND pairwise-Lipschitz (`L_A`) on a base ball, UNCONDITIONAL at base `0`.
    • `censusAmpTauDeriv_eq_amp_diff` — `censusAmpTauDeriv = chartFieldAmp(τ=1) − chartFieldAmp(τ=0)`
        (both amplitudes affine in τ; the slope is their difference).
    • `censusAmpTauDeriv_base_regularity_center` — ★ the CONCRETE `∂_τ`-slope `Cfield =
        censusAmpTauDeriv` is bounded + pairwise-Lipschitz on a base ball, UNCONDITIONAL at base `0`.
    • `census_ampF_weight_regularity` — ★★ for ANY ball-locally bounded+Lipschitz `F0` (the honest
        carry, e.g. `fun z ↦ leviSeries … s z 0`), the CONCRETE product weight `z ↦ chartFieldAmp …
        τ z 0 · F0 z` is bounded + pairwise-Lipschitz on a base ball — the exact abstract-`P` input of
        J4-931's `paired_ratio_center_lipschitz`.
    • `census_CfieldF_weight_regularity` — ★★ the same for `z ↦ censusAmpTauDeriv … z · F0 z` (q₂).
    • `census_ampF_ratio_regularity` — ★★ THE CONCRETE q₁: `z ↦ (chartFieldAmp … τ z 0 · F0 z) /
        |det (fderiv Wbv z)|` bounded + pairwise-Lipschitz on a base ball (via `det_fderiv_regularity_
        bundle` + `ratio_abs_lipschitzOn`), CONDITIONAL on the J4-930/931 residual `hbaseC2`.
    • `census_CfieldF_ratio_regularity` — ★★ THE CONCRETE q₂ ratio.
    • `census_abstractF_slot_satisfiable` — non-vacuity of the abstract-F carry slot (TEETH: `cos‖·‖`,
        bounded but genuinely varying, Lipschitz `1`).

  ⚠  STILL NOT `a₁ = R/6`.  `hCensusBound`/`hCross`/`hDuhamel`/`hDConv` remain carried; `hCConv`
  unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.NormalFormDischarge
import QIQTH.HrepGermFactorization
import QIQTH.CensusTauDerivGateSplit
import QIQTH.DataAmpAssembly
import QIQTH.BaseSlotDetRegularity
import QIQTH.GaussTauTraceChartDetFactor
import QIQTH.DisplacementDerivative

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.CensusAmpConcreteRegularity

open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization QIQTH.CensusTauDerivGateSplit
open QIQTH.DataAmpAssembly QIQTH.BaseSlotDetRegularity QIQTH.DisplacementDerivative

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the value bridge `chartFieldAmp = chartAmp` (pure associativity).
    ############################################################################### -/

/-- **`chartFieldAmp_apply_eq_chartAmp` — the value bridge.**  The concrete census field amplitude
    `chartFieldAmp … τ z 0` (`NormalFormDischarge`, `A·(B·C)` grouping) coincides with the base-slot
    amplitude `chartAmp … τ z 0` (`HrepGermFactorization`, `(A·B)·C` grouping) — same product, pure
    `mul_assoc`.  This lets the banked `DataAmpAssembly` regularity of `chartAmp` be reused verbatim
    for `chartFieldAmp`.  ⚠ NOT `a₁ = R/6`. -/
theorem chartFieldAmp_apply_eq_chartAmp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) :
    chartFieldAmp g gi hC hK a b τ z 0
      = chartAmp g gi hC hK a b τ z 0 := by
  simp only [chartFieldAmp, chartAmp]
  ring

/-! ###############################################################################
    ### §B — the CONCRETE amplitude `chartFieldAmp … τ z 0` is bounded + Lipschitz.
    ############################################################################### -/

/-- **★ `chartFieldAmp_base_regularity_center`.**  The concrete census field amplitude
    `z ↦ chartFieldAmp … τ z 0` is globally bounded (`M_A`) on a base ball AND pairwise-Lipschitz
    (`L_A`) on it, UNCONDITIONALLY at base `0` (only the standard g/gi smoothness carries).  Route:
    the value bridge (§A) + the banked `DataAmpAssembly.chartAmp_base_bounded_near_zero` /
    `chartAmp_base_lipschitz_center` (both discharged at base `0`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartFieldAmp_base_regularity_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      (∀ z : Point n, ‖z‖ < r → |chartFieldAmp g gi hC hK a b τ z 0| ≤ M) ∧
      (∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
        |chartFieldAmp g gi hC hK a b τ z 0 - chartFieldAmp g gi hC hK a b τ w 0| ≤ L * dist z w) := by
  obtain ⟨rM, hrM, M, hM, hbnd⟩ :=
    chartAmp_base_bounded_near_zero g gi hC hK a b τ h0Kmem hg hg0 hu
  obtain ⟨rL, hrL, L, hL, hlip⟩ :=
    chartAmp_base_lipschitz_center g gi hC hK a b τ h0Kmem hg hg0 hu
  refine ⟨min rM rL, lt_min hrM hrL, M, L, hM, hL, ?_, ?_⟩
  · intro z hz
    rw [chartFieldAmp_apply_eq_chartAmp]
    exact hbnd z (lt_of_lt_of_le hz (min_le_left _ _))
  · intro z w hz hw
    rw [chartFieldAmp_apply_eq_chartAmp, chartFieldAmp_apply_eq_chartAmp]
    exact hlip z w (lt_of_lt_of_le hz (min_le_right _ _)) (lt_of_lt_of_le hw (min_le_right _ _))

/-! ###############################################################################
    ### §C — the CONCRETE `∂_τ`-slope `censusAmpTauDeriv` is bounded + Lipschitz.
    ############################################################################### -/

/-- **`censusAmpTauDeriv_eq_amp_diff`.**  The census amplitude is AFFINE in `τ`, so its `∂_τ`-slope is
    the endpoint difference `chartFieldAmp(τ=1) − chartFieldAmp(τ=0)`.  Pure `ring` in the shared atoms
    (`= C·u₁` with `C = radialCutoff·Θ^{−1/2}`).  ⚠ NOT `a₁ = R/6`. -/
theorem censusAmpTauDeriv_eq_amp_diff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z : Point n) :
    censusAmpTauDeriv g gi hC hK a b z
      = chartFieldAmp g gi hC hK a b 1 z 0 - chartFieldAmp g gi hC hK a b 0 z 0 := by
  simp only [censusAmpTauDeriv, chartFieldAmp]
  ring

/-- **★ `censusAmpTauDeriv_base_regularity_center`.**  The concrete `∂_τ`-slope
    `z ↦ censusAmpTauDeriv … z` (`= Cfield`) is globally bounded on a base ball AND pairwise-Lipschitz
    on it, UNCONDITIONALLY at base `0`.  Route: `censusAmpTauDeriv_eq_amp_diff` writes it as the
    difference of the amplitude at `τ=1` and `τ=0`, each bounded+Lipschitz (§B); sub-additivity of
    `|·|` closes both.  ⚠ NOT `a₁ = R/6`. -/
theorem censusAmpTauDeriv_base_regularity_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      (∀ z : Point n, ‖z‖ < r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M) ∧
      (∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
        |censusAmpTauDeriv g gi hC hK a b z - censusAmpTauDeriv g gi hC hK a b w| ≤ L * dist z w) := by
  obtain ⟨r1, hr1, M1, L1, hM1, hL1, hb1, hl1⟩ :=
    chartFieldAmp_base_regularity_center g gi hC hK a b 1 h0Kmem hg hg0 hu
  obtain ⟨r0, hr0, M0, L0, hM0, hL0, hb0, hl0⟩ :=
    chartFieldAmp_base_regularity_center g gi hC hK a b 0 h0Kmem hg hg0 hu
  refine ⟨min r1 r0, lt_min hr1 hr0, M1 + M0, L1 + L0, add_nonneg hM1 hM0, add_nonneg hL1 hL0,
    ?_, ?_⟩
  · intro z hz
    rw [censusAmpTauDeriv_eq_amp_diff]
    have hz1 : ‖z‖ < r1 := lt_of_lt_of_le hz (min_le_left _ _)
    have hz0 : ‖z‖ < r0 := lt_of_lt_of_le hz (min_le_right _ _)
    have hsub : |chartFieldAmp g gi hC hK a b 1 z 0 - chartFieldAmp g gi hC hK a b 0 z 0|
        ≤ |chartFieldAmp g gi hC hK a b 1 z 0| + |chartFieldAmp g gi hC hK a b 0 z 0| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    exact hsub.trans (add_le_add (hb1 z hz1) (hb0 z hz0))
  · intro z w hz hw
    rw [censusAmpTauDeriv_eq_amp_diff, censusAmpTauDeriv_eq_amp_diff]
    have hz1 : ‖z‖ < r1 := lt_of_lt_of_le hz (min_le_left _ _)
    have hz0 : ‖z‖ < r0 := lt_of_lt_of_le hz (min_le_right _ _)
    have hw1 : ‖w‖ < r1 := lt_of_lt_of_le hw (min_le_left _ _)
    have hw0 : ‖w‖ < r0 := lt_of_lt_of_le hw (min_le_right _ _)
    set A1z := chartFieldAmp g gi hC hK a b 1 z 0
    set A0z := chartFieldAmp g gi hC hK a b 0 z 0
    set A1w := chartFieldAmp g gi hC hK a b 1 w 0
    set A0w := chartFieldAmp g gi hC hK a b 0 w 0
    have hrw : (A1z - A0z) - (A1w - A0w) = (A1z - A1w) + -(A0z - A0w) := by ring
    calc |(A1z - A0z) - (A1w - A0w)|
        = |(A1z - A1w) + -(A0z - A0w)| := by rw [hrw]
      _ ≤ |A1z - A1w| + |-(A0z - A0w)| := abs_add_le _ _
      _ = |A1z - A1w| + |A0z - A0w| := by rw [abs_neg]
      _ ≤ L1 * dist z w + L0 * dist z w := add_le_add (hl1 z w hz1 hw1) (hl0 z w hz0 hw0)
      _ = (L1 + L0) * dist z w := by ring

/-! ###############################################################################
    ### §D — the CONCRETE product weights `amp·F` / `Cfield·F` (abstract F carry).
    ############################################################################### -/

/-- Abstract helper: a bounded+pairwise-Lipschitz factor `P` (the concrete amplitude) times a
    bounded+pairwise-Lipschitz factor `F0` (the honest Levi carry) is bounded+pairwise-Lipschitz on
    the common ball.  Pure `collar_product_lipschitz_increment`.  ⚠ NOT `a₁ = R/6`. -/
private theorem product_ball_regularity
    (P F0 : Point n → ℝ) (rP rF M_P M_F L_P L_F : ℝ)
    (hMPnn : 0 ≤ M_P) (hMFnn : 0 ≤ M_F)
    (hPb : ∀ z : Point n, ‖z‖ < rP → |P z| ≤ M_P)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hPl : ∀ z w : Point n, ‖z‖ < rP → ‖w‖ < rP → |P z - P w| ≤ L_P * dist z w)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    (∀ z ∈ Metric.ball (0 : Point n) (min rP rF), |P z * F0 z| ≤ M_P * M_F) ∧
      (∀ x ∈ Metric.ball (0 : Point n) (min rP rF), ∀ y ∈ Metric.ball (0 : Point n) (min rP rF),
        |P x * F0 x - P y * F0 y| ≤ (M_P * L_F + M_F * L_P) * dist x y) := by
  constructor
  · intro z hz
    have hzn : ‖z‖ < min rP rF := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hzP : ‖z‖ < rP := lt_of_lt_of_le hzn (min_le_left _ _)
    have hzF : ‖z‖ < rF := lt_of_lt_of_le hzn (min_le_right _ _)
    rw [abs_mul]
    exact mul_le_mul (hPb z hzP) (hFb z hzF) (abs_nonneg _) hMPnn
  · intro x hx y hy
    have hxn : ‖x‖ < min rP rF := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hyn : ‖y‖ < min rP rF := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have hxP : ‖x‖ < rP := lt_of_lt_of_le hxn (min_le_left _ _)
    have hxF : ‖x‖ < rF := lt_of_lt_of_le hxn (min_le_right _ _)
    have hyP : ‖y‖ < rP := lt_of_lt_of_le hyn (min_le_left _ _)
    have hyF : ‖y‖ < rF := lt_of_lt_of_le hyn (min_le_right _ _)
    exact collar_product_lipschitz_increment P F0 M_P M_F L_P L_F x y hMPnn hMFnn
      (hPb x hxP) (hFb y hyF) (hPl x y hxP hyP) (hFl x y hxF hyF)

/-- **★★ `census_ampF_weight_regularity` — the CONCRETE `amp·F` weight (q₁ pre-`/det`).**  For ANY
    ball-locally bounded (`M_F`) + pairwise-Lipschitz (`L_F`) factor `F0` on a genuine ball `rF > 0`
    (the honest Levi carry, e.g. `fun z ↦ leviSeries … s z 0`), the CONCRETE product
    `z ↦ chartFieldAmp … τ z 0 · F0 z` is bounded (`M_A·M_F`) + pairwise-Lipschitz on a base ball —
    the exact abstract-`P` input of J4-931's `paired_ratio_center_lipschitz`.  The AMPLITUDE factor is
    concrete (§B); only `F0` is carried.  ⚠ NOT `a₁ = R/6`. -/
theorem census_ampF_weight_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ ρ > (0 : ℝ), ∃ M_P L_P : ℝ, 0 ≤ M_P ∧ 0 ≤ L_P ∧
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        |chartFieldAmp g gi hC hK a b τ z 0 * F0 z| ≤ M_P) ∧
      (∀ x ∈ Metric.ball (0 : Point n) ρ, ∀ y ∈ Metric.ball (0 : Point n) ρ,
        |chartFieldAmp g gi hC hK a b τ x 0 * F0 x - chartFieldAmp g gi hC hK a b τ y 0 * F0 y|
          ≤ L_P * dist x y) := by
  obtain ⟨rA, hrA, M_A, L_A, hMA, hLA, hAb, hAl⟩ :=
    chartFieldAmp_base_regularity_center g gi hC hK a b τ h0Kmem hg hg0 hu
  obtain ⟨hbnd, hlip⟩ :=
    product_ball_regularity (fun z => chartFieldAmp g gi hC hK a b τ z 0) F0
      rA rF M_A M_F L_A L_F hMA hMFnn hAb hFb hAl hFl
  exact ⟨min rA rF, lt_min hrA hrF, M_A * M_F, M_A * L_F + M_F * L_A,
    mul_nonneg hMA hMFnn, add_nonneg (mul_nonneg hMA hLFnn) (mul_nonneg hMFnn hLA), hbnd, hlip⟩

/-- **★★ `census_CfieldF_weight_regularity` — the CONCRETE `Cfield·F` weight (q₂ pre-`/det`).**  As
    `census_ampF_weight_regularity` but with the concrete `∂_τ`-slope `censusAmpTauDeriv` (§C) in
    place of the amplitude.  ⚠ NOT `a₁ = R/6`. -/
theorem census_CfieldF_weight_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ ρ > (0 : ℝ), ∃ M_P L_P : ℝ, 0 ≤ M_P ∧ 0 ≤ L_P ∧
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        |censusAmpTauDeriv g gi hC hK a b z * F0 z| ≤ M_P) ∧
      (∀ x ∈ Metric.ball (0 : Point n) ρ, ∀ y ∈ Metric.ball (0 : Point n) ρ,
        |censusAmpTauDeriv g gi hC hK a b x * F0 x - censusAmpTauDeriv g gi hC hK a b y * F0 y|
          ≤ L_P * dist x y) := by
  obtain ⟨rA, hrA, M_A, L_A, hMA, hLA, hAb, hAl⟩ :=
    censusAmpTauDeriv_base_regularity_center g gi hC hK a b h0Kmem hg hg0 hu
  obtain ⟨hbnd, hlip⟩ :=
    product_ball_regularity (fun z => censusAmpTauDeriv g gi hC hK a b z) F0
      rA rF M_A M_F L_A L_F hMA hMFnn hAb hFb hAl hFl
  exact ⟨min rA rF, lt_min hrA hrF, M_A * M_F, M_A * L_F + M_F * L_A,
    mul_nonneg hMA hMFnn, add_nonneg (mul_nonneg hMA hLFnn) (mul_nonneg hMFnn hLA), hbnd, hlip⟩

/-! ###############################################################################
    ### §E — the CONCRETE ratio weights `(amp·F)/|det|` (q₁) and `(Cfield·F)/|det|` (q₂).
    ############################################################################### -/

/-- **★★ `census_ampF_ratio_regularity` — THE CONCRETE q₁ (post-`/det`, base ball).**  Composing the
    concrete `amp·F` weight (§D) with the determinant-factor regularity `det_fderiv_regularity_bundle`
    (J4-931) through `ratio_abs_lipschitzOn` (J4-925), the CONCRETE transformed weight
    `z ↦ (chartFieldAmp … τ z 0 · F0 z) / |det (fderiv Wbv z)|` is bounded + pairwise-Lipschitz on a
    base ball.  This is EXACTLY the base-slot change-of-variables integrand `q₁` that the census
    machinery consumes — with the amplitude concrete and only `F0` carried.  CONDITIONAL on the
    J4-930/931 residual `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem census_ampF_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ ρ > (0 : ℝ), ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        abs (chartFieldAmp g gi hC hK a b τ z 0 * F0 z
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) ρ, ∀ y ∈ Metric.ball (0 : Point n) ρ,
        abs (chartFieldAmp g gi hC hK a b τ x 0 * F0 x
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) x).det|
            - chartFieldAmp g gi hC hK a b τ y 0 * F0 y
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det|)
          ≤ L * dist x y) := by
  obtain ⟨rW, hrW, M_P, L_P, hMP, hLP, hPb, hPl⟩ :=
    census_ampF_weight_regularity g gi hC hK a b τ h0Kmem hg hg0 hu F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨rD, hrD, L_D, hLD, hlbdet, hDlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  set S : Set (Point n) := Metric.ball (0 : Point n) (min rW rD) with hSdef
  have hSW : S ⊆ Metric.ball (0 : Point n) rW := Metric.ball_subset_ball (min_le_left _ _)
  have hSD : S ⊆ Metric.ball (0 : Point n) rD := Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨hRb, hRl⟩ :=
    ratio_abs_lipschitzOn S (fun z => chartFieldAmp g gi hC hK a b τ z 0 * F0 z)
      (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det)
      M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD
      (fun x hx => hPb x (hSW hx))
      (fun x hx y hy => hPl x (hSW hx) y (hSW hy))
      (fun x hx => hlbdet x (hSD hx))
      (fun x hx y hy => hDlip x (hSD hx) y (hSD hy))
  refine ⟨min rW rD, lt_min hrW hrD, M_P / (1 / 2 : ℝ),
    L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2,
    by positivity, by positivity, hRb, hRl⟩

/-- **★★ `census_CfieldF_ratio_regularity` — THE CONCRETE q₂ (post-`/det`, base ball).**  As
    `census_ampF_ratio_regularity` but for the `∂_τ`-slope weight `censusAmpTauDeriv · F0` — the
    concrete second census integrand `q₂ = (Cfield·F)/|det|`.  CONDITIONAL on `hbaseC2`.
    ⚠ NOT `a₁ = R/6`. -/
theorem census_CfieldF_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ ρ > (0 : ℝ), ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      (∀ z ∈ Metric.ball (0 : Point n) ρ,
        abs (censusAmpTauDeriv g gi hC hK a b z * F0 z
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) ρ, ∀ y ∈ Metric.ball (0 : Point n) ρ,
        abs (censusAmpTauDeriv g gi hC hK a b x * F0 x
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) x).det|
            - censusAmpTauDeriv g gi hC hK a b y * F0 y
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) y).det|)
          ≤ L * dist x y) := by
  obtain ⟨rW, hrW, M_P, L_P, hMP, hLP, hPb, hPl⟩ :=
    census_CfieldF_weight_regularity g gi hC hK a b h0Kmem hg hg0 hu F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨rD, hrD, L_D, hLD, hlbdet, hDlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  set S : Set (Point n) := Metric.ball (0 : Point n) (min rW rD) with hSdef
  have hSW : S ⊆ Metric.ball (0 : Point n) rW := Metric.ball_subset_ball (min_le_left _ _)
  have hSD : S ⊆ Metric.ball (0 : Point n) rD := Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨hRb, hRl⟩ :=
    ratio_abs_lipschitzOn S (fun z => censusAmpTauDeriv g gi hC hK a b z * F0 z)
      (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det)
      M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD
      (fun x hx => hPb x (hSW hx))
      (fun x hx y hy => hPl x (hSW hx) y (hSW hy))
      (fun x hx => hlbdet x (hSD hx))
      (fun x hx y hy => hDlip x (hSD hx) y (hSD hy))
  refine ⟨min rW rD, lt_min hrW hrD, M_P / (1 / 2 : ℝ),
    L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2,
    by positivity, by positivity, hRb, hRl⟩

/-! ###############################################################################
    ### §F — non-vacuity of the abstract-F carry slot (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of the abstract-F carry slot.**  The `F0` hypothesis bundle of the weight/ratio
    theorems (bounded + pairwise-Lipschitz on a genuine ball) is satisfiable with TEETH by
    `F0 z := cos ‖z‖` (bounded by `1`, genuinely varying, Lipschitz `1` via `Real.lipschitzWith_cos`
    ∘ `abs_norm_sub_norm_le`), `rF = 1`.  Confirms the carried slot is not vacuous.  ⚠ NOT `a₁ = R/6`. -/
theorem census_abstractF_slot_satisfiable :
    ∃ (F0 : Point n → ℝ) (rF M_F L_F : ℝ), 0 < rF ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F) ∧
      (∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) := by
  refine ⟨fun z => Real.cos ‖z‖, 1, 1, 1, one_pos, zero_le_one, zero_le_one, ?_, ?_⟩
  · intro z _
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · intro z w _ _
    have h1 : |Real.cos ‖z‖ - Real.cos ‖w‖| ≤ |‖z‖ - ‖w‖| := by
      have hlip := Real.lipschitzWith_cos.dist_le_mul ‖z‖ ‖w‖
      simpa [Real.dist_eq, one_mul] using hlip
    have h2 : |‖z‖ - ‖w‖| ≤ dist z w := by
      rw [dist_eq_norm]; exact abs_norm_sub_norm_le z w
    calc |Real.cos ‖z‖ - Real.cos ‖w‖| ≤ |‖z‖ - ‖w‖| := h1
      _ ≤ dist z w := h2
      _ = 1 * dist z w := (one_mul _).symm

end QIQTH.CensusAmpConcreteRegularity

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusAmpConcreteRegularity
#print axioms chartFieldAmp_apply_eq_chartAmp
#print axioms chartFieldAmp_base_regularity_center
#print axioms censusAmpTauDeriv_eq_amp_diff
#print axioms censusAmpTauDeriv_base_regularity_center
#print axioms census_ampF_weight_regularity
#print axioms census_CfieldF_weight_regularity
#print axioms census_ampF_ratio_regularity
#print axioms census_CfieldF_ratio_regularity
#print axioms census_abstractF_slot_satisfiable
end AxiomChecks
