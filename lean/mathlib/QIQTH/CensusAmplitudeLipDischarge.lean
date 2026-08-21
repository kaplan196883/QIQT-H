/-
  CensusAmplitudeLipDischarge — the τ↓0-UNIFORM SPATIAL LIPSCHITZ bound for the concrete census field
  amplitude `chartFieldAmp … cutA cutB τ z 0` (as a function of the spatial variable `z` on a base ball),
  UNIFORM over `0 < τ ≤ τ₀`.  Companion to `census_amplitude_supBounds` (J4-949, τ-uniform VALUE bounds):
  that file bounds `|chartFieldAmp|` uniformly in τ; THIS file bounds the spatial Lipschitz INCREMENT
  `|chartFieldAmp τ z 0 − chartFieldAmp τ w 0|` uniformly in τ.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  real-analysis / structural brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing banked file edited.

  ## THE PROBLEM.  The C1 ball-rate glue needs a spatial-Lipschitz constant for `z ↦ chartFieldAmp … τ z 0`
  that is UNIFORM as `τ ↓ 0`.  The per-τ Lipschitz `chartFieldAmp_base_regularity_center` (J4, one fixed τ)
  yields a constant that may a-priori depend on τ, and `(0, τ₀]` is not compact at `0` — so a naive "take
  the sup over τ" is blocked.

  ## THE DISCHARGE (mechanism, affine-in-τ shortcut).  `chartFieldAmp` is AFFINE in `τ`
  (`chartFieldAmp_affine_slope`, J4-949, pure `ring`):
      `chartFieldAmp … cutA cutB τ z 0 = chartFieldAmp … cutA cutB 0 z 0 + censusAmpTauDeriv … z · τ`.
  So the spatial increment splits:
      `chartFieldAmp τ z − chartFieldAmp τ w = (base_z − base_w) + (slope_z − slope_w)·τ`,
  giving
      `|Δ| ≤ L₀·dist(z,w) + τ·L'·dist(z,w) ≤ (L₀ + τ₀·L')·dist(z,w)`,
  a SINGLE τ-uniform Lipschitz constant `L₀ + τ₀·L'` — NO compactness needed (the τ-scaled slope term
  `τ·L' → 0` as `τ ↓ 0`, and is bounded by `τ₀·L'` throughout `(0, τ₀]`).  `L₀` is the spatial Lipschitz
  constant of the τ=0 base (`chartFieldAmp_base_regularity_center … 0 …`); `L'` is that of the slope
  (`censusAmpTauDeriv_base_regularity_center`).  Both are banked, UNCONDITIONALLY at base `0`, from the
  standard geometry carries `{hg, hg0, hu, h0Kmem}` alone.  (Sol audit 2026-08-21 confirmed the argument
  is valid and complete; the earlier "not compact at 0" caution was overly pessimistic given the affine
  structure.)

  ## WHAT LANDS.
    • `census_amplitude_lipBounds` — ★★★ the τ-UNIFORM amplitude spatial-Lipschitz package (∃ rAmp, L, L'),
        with the amplitude increment `L`-Lipschitz UNIFORMLY over `0 < τ ≤ τ₀` on `ball 0 rAmp` and the
        slope `L'`-Lipschitz.  Discharges the τ↓0-uniform amplitude-Lipschitz content to the standard
        geometry carries alone.

  ## HONEST STATUS.  The τ↓0-uniform `chartFieldAmp` spatial Lipschitz is DISCHARGED (from banked
  base-point regularity, via the affine-in-τ shortcut).  This is one of the C1/`hballrate` glue-item-3
  sub-pieces; it does NOT by itself close `hballrate`, `hCensusBound`, `hDuhamel`, `hDConv`, or `hCConv`.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusAmplitudeSupDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.OnGateJets
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open QIQTH.CensusAmplitudeSupDischarge
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusAmplitudeLipDischarge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★★★ `census_amplitude_lipBounds` — the τ↓0-UNIFORM amplitude spatial-Lipschitz package.**  From the
    standard geometry carries (`hg` metric smoothness, `hg0` `g(0)=I`, `hu` transport smoothness,
    `h0Kmem` `K∈𝓝 0`) and a positive time cap `τ₀`, there is a base ball radius `rAmp > 0` and explicit
    constants `L, L' ≥ 0` with, on `ball 0 rAmp`,
      • `|chartFieldAmp … cutA cutB τ z 0 − chartFieldAmp … cutA cutB τ w 0| ≤ L · dist z w`  UNIFORMLY
        over `0 < τ ≤ τ₀`  (τ↓0-uniform spatial Lipschitz), and
      • `|censusAmpTauDeriv … z − censusAmpTauDeriv … w| ≤ L' · dist z w`.
    Route: the affine-in-τ form `chartFieldAmp τ = chartFieldAmp 0 + slope·τ`
    (`chartFieldAmp_affine_slope`) splits the spatial increment into the τ=0 base increment (Lipschitz
    `L₀` from `chartFieldAmp_base_regularity_center … 0 …`) plus `τ·(slope increment)` (Lipschitz `τ·L'`,
    `L'` from `censusAmpTauDeriv_base_regularity_center`), giving the SINGLE τ-uniform `L := L₀ + L'·τ₀` —
    NO compactness at `τ = 0`.  This DISCHARGES the τ↓0-uniform amplitude-Lipschitz content to the
    standard geometry carries alone.  ⚠ NOT `a₁ = R/6`. -/
theorem census_amplitude_lipBounds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cutA cutB τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ rAmp : ℝ, 0 < rAmp ∧ ∃ L L' : ℝ, 0 ≤ L ∧ 0 ≤ L' ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z w : Point n, ‖z‖ < rAmp → ‖w‖ < rAmp →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0 - chartFieldAmp g gi hC hK cutA cutB τ w 0|
          ≤ L * dist z w) ∧
      (∀ z w : Point n, ‖z‖ < rAmp → ‖w‖ < rAmp →
        |censusAmpTauDeriv g gi hC hK cutA cutB z - censusAmpTauDeriv g gi hC hK cutA cutB w|
          ≤ L' * dist z w) := by
  obtain ⟨r0, hr0, _M0, L0, _hM0, hL0, _hb0, hlip0⟩ :=
    chartFieldAmp_base_regularity_center g gi hC hK cutA cutB 0 h0Kmem hg hg0 hu
  obtain ⟨r', hr', _M', L', _hM', hL', _hb', hlip'⟩ :=
    censusAmpTauDeriv_base_regularity_center g gi hC hK cutA cutB h0Kmem hg hg0 hu
  refine ⟨min r0 r', lt_min hr0 hr', L0 + L' * τ₀, L',
    add_nonneg hL0 (mul_nonneg hL' hτ₀.le), hL', ?_, ?_⟩
  · intro τ hτ hτ0 z w hz hw
    have hz0 : ‖z‖ < r0 := lt_of_lt_of_le hz (min_le_left _ _)
    have hw0 : ‖w‖ < r0 := lt_of_lt_of_le hw (min_le_left _ _)
    have hz' : ‖z‖ < r' := lt_of_lt_of_le hz (min_le_right _ _)
    have hw' : ‖w‖ < r' := lt_of_lt_of_le hw (min_le_right _ _)
    have ez := chartFieldAmp_affine_slope g gi hC hK cutA cutB τ z
    have ew := chartFieldAmp_affine_slope g gi hC hK cutA cutB τ w
    rw [ez, ew]
    set Bz := chartFieldAmp g gi hC hK cutA cutB 0 z 0 with hBz
    set Bw := chartFieldAmp g gi hC hK cutA cutB 0 w 0 with hBw
    set Sz := censusAmpTauDeriv g gi hC hK cutA cutB z with hSz
    set Sw := censusAmpTauDeriv g gi hC hK cutA cutB w with hSw
    have hb : |Bz - Bw| ≤ L0 * dist z w := hlip0 z w hz0 hw0
    have hs : |Sz - Sw| ≤ L' * dist z w := hlip' z w hz' hw'
    have hstep : |Sz - Sw| * τ ≤ L' * dist z w * τ₀ := by
      have h1 : |Sz - Sw| * τ ≤ (L' * dist z w) * τ :=
        mul_le_mul_of_nonneg_right hs hτ.le
      have h2 : (L' * dist z w) * τ ≤ (L' * dist z w) * τ₀ :=
        mul_le_mul_of_nonneg_left hτ0 (mul_nonneg hL' dist_nonneg)
      linarith
    have hrw : (Bz + Sz * τ) - (Bw + Sw * τ) = (Bz - Bw) + (Sz - Sw) * τ := by ring
    calc |(Bz + Sz * τ) - (Bw + Sw * τ)|
        = |(Bz - Bw) + (Sz - Sw) * τ| := by rw [hrw]
      _ ≤ |Bz - Bw| + |(Sz - Sw) * τ| := abs_add_le _ _
      _ = |Bz - Bw| + |Sz - Sw| * τ := by rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ L0 * dist z w + L' * dist z w * τ₀ := by linarith
      _ = (L0 + L' * τ₀) * dist z w := by ring
  · intro z w hz hw
    exact hlip' z w (lt_of_lt_of_le hz (min_le_right _ _)) (lt_of_lt_of_le hw (min_le_right _ _))

end QIQTH.CensusAmplitudeLipDischarge

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.CensusAmplitudeLipDischarge
#print axioms census_amplitude_lipBounds
end AxiomChecks
