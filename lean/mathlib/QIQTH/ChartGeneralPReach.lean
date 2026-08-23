/-
  ChartGeneralPReach — the p-GENERAL analogue of `CurvedRNCChartReach.hVmapMeasK_zero_of_reach`
  (J4-529): collapsing `ChartGeneralPContinuity.chartP_continuousOn`'s THREE geometric side-conditions
  {`hball`, `hnorm`, `hRI`} at an ARBITRARY field point `p` (not just the origin `p = 0`) into a SINGLE
  reach hypothesis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and discharges NOTHING toward it.  It is a pure
  bookkeeping consolidation, mechanically mirroring J4-529's `p = 0` collapse with `0 ↦ p`, using the
  fact that the underlying left-inverse germ `UniformChartRadius.uniformInverseChart_huniformChart` is
  ALREADY stated for an arbitrary velocity `v` (not merely `v = 0`), so the SAME collapse argument goes
  through verbatim for any target point `p` reached via `uniformFlowExp _ _ _ _ z v = p`.

  ── WHAT THIS DOES *NOT* DO (checked BEFORE writing, per `gpt-5.6-sol` (high) consult).  It does
  **not** discharge the reach hypothesis itself from the substrate — the K-uniform reach
  `∀ z ∈ S, ∃ v, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p` remains exactly as carried/unbanked as the
  three original side-conditions were (`ExpRhoReachability`'s GENUINE-INPUT verdict, J4-485, is
  UNCHANGED).  It therefore has **no** bearing on the currently-blocked `hbnd` (boundary-uniform
  Christoffel/Taylor control) or `hDConv`'s `hbdry` branch (blocked at concrete chart instantiation,
  J4-1099): those fronts need the reach *proved* at the actual curved-tower witness, and this file
  supplies no such proof — only a cleaner (1-hypothesis instead of 3-hypothesis) INTERFACE for whichever
  future brick, if any, does supply it.  Sol's verdict: "provides no substantive progress on `hbnd` or
  `hDConv.hbdry` ... unless [the reach hypothesis] is separately assumed or supplied by stronger
  geometry, both fronts remain blocked exactly where they were."

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `chartP_reach_radius_pos` — the uniform radius `ρ > 0` (min of the germ radius, the flow radius,
      and the p-Lipschitz-modulus ball radius) over which the collapse below is valid.
    * `chartP_continuousOn_of_reach` — **★ the p-general collapse.**  `ContinuousOn (z ↦ W z p) S` from
      the SINGLE reach hypothesis `∀ z ∈ S, ∃ v, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p`, in place of
      `ChartGeneralPContinuity.chartP_continuousOn`'s three side-conditions {`hball`, `hnorm`, `hRI`}.
    * `hVmapMeasK_at_p_of_reach` — the measurability-level companion: the same collapse, feeding
      `ChartGeneralPContinuity.hVmapMeasK_at_p_of_geom` instead of `chartP_continuousOn` directly, giving
      `AEStronglyMeasurable (z ↦ W z p) (volume.restrict K)` from the single reach hypothesis on all of
      `K`.  The p-general analogue of `CurvedRNCChartReach.hVmapMeasK_zero_of_reach`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartGeneralPContinuity

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.GeodesicGronwall QIQTH.FoldedCoeffChartMeas QIQTH.ChartGeneralPContinuity

namespace QIQTH.ChartGeneralPReach

variable {n : ℕ}

/-! ###############################################################################
    ### The p-general reduction — three side-conditions ↦ one reachability input.
    ############################################################################### -/

/-- **★ `chartP_continuousOn_of_reach` — the p-GENERAL collapse.**  For any `(g, gi)` with smooth
    Christoffel data over a compact `K`, and any field point `p`, there is a uniform radius `ρ > 0` such
    that the reach `∀ z ∈ S, ∃ v : Point n, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p` (`S ⊆ K`) IMPLIES
    `ContinuousOn (z ↦ uniformInverseChart g gi hC hK z p) S`.  Mirrors
    `CurvedRNCChartReach.hVmapMeasK_zero_of_reach` with `0 ↦ p`, feeding
    `ChartGeneralPContinuity.chartP_continuousOn` instead of `hVmapMeasK_zero_of_geom` directly.  The
    three geometric side-conditions {`hball`, `hnorm`, `hRI`} are DERIVED internally from the reach via
    the (already p-general) left-inverse germ `uniformInverseChart_huniformChart`.  NOT `a₁ = R/6`. -/
theorem chartP_continuousOn_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) :
    ∃ ρ > (0 : ℝ), ∀ {S : Set (Point n)}, S ⊆ K →
      (∀ z ∈ S, ∃ v : Point n, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p) →
      ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) S := by
  obtain ⟨δg, hδg, hgerm⟩ := uniformInverseChart_huniformChart g gi hC hK
  set δlip := (chartP_lipschitz_modulus g gi hC hK p).choose with hδlip_def
  have hδlip_pos : 0 < δlip := (chartP_lipschitz_modulus g gi hC hK p).choose_spec.1
  have hρK_pos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min (min δg (uniformFlowRadius g gi hC hK)) δlip,
    lt_min (lt_min hδg hρK_pos) hδlip_pos, ?_⟩
  intro S hSK hReach
  have hcombined : ∀ z ∈ S,
      uniformInverseChart g gi hC hK z p
        ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose ∧
      ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK ∧
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p := by
    intro z hz
    have hzK : z ∈ K := hSK hz
    obtain ⟨v, hv, hexp⟩ := hReach z hz
    have hlt_δg : ‖v‖ < δg :=
      lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_left _ _))
    have hlt_ρK : ‖v‖ < uniformFlowRadius g gi hC hK :=
      lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_right _ _))
    have hlt_lip : ‖v‖ < δlip := lt_of_lt_of_le hv (min_le_right _ _)
    obtain ⟨hgermC2, _hOC⟩ := hgerm z hzK
    -- left-inverse germ at `v`: `W z (exp_z v) = v`.
    have hLI : uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v :=
      (hgermC2 v hlt_δg).1.eq_of_nhds
    -- hence `W z p = v` (since `exp_z v = p`).
    have hWp : uniformInverseChart g gi hC hK z p = v := by rw [← hexp]; exact hLI
    refine ⟨?_, ?_, ?_⟩
    · rw [hWp]; exact mem_ball_zero_iff.mpr hlt_lip
    · rw [hWp]; exact le_of_lt hlt_ρK
    · rw [hWp]; exact hexp
  exact chartP_continuousOn g gi hC hK p hSK
    (fun z hz => (hcombined z hz).1) (fun z hz => (hcombined z hz).2.1)
    (fun z hz => (hcombined z hz).2.2)

/-! ###############################################################################
    ### The measurability-level companion.
    ############################################################################### -/

/-- **`hVmapMeasK_at_p_of_reach` — the p-GENERAL measurability collapse.**  The measurability-level
    companion of `chartP_continuousOn_of_reach`: for any field point `p`, a uniform radius `ρ > 0` such
    that the K-uniform reach `∀ z ∈ K, ∃ v, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p` IMPLIES
    `AEStronglyMeasurable (z ↦ uniformInverseChart g gi hC hK z p) (volume.restrict K)`.  The p-general
    analogue of `CurvedRNCChartReach.hVmapMeasK_zero_of_reach` (its `p = 0` instance).  NOT `a₁ = R/6`. -/
theorem hVmapMeasK_at_p_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ K, ∃ v : Point n, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = p) →
      AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
        ((volume : Measure (Point n)).restrict K) := by
  obtain ⟨ρ, hρ, himpl⟩ := chartP_continuousOn_of_reach g gi hC hK p
  refine ⟨ρ, hρ, fun hReach => ?_⟩
  have hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) K :=
    himpl (Set.Subset.refl K) hReach
  exact hcont.aestronglyMeasurable hK.measurableSet

end QIQTH.ChartGeneralPReach

section AxiomChecks
open QIQTH.ChartGeneralPReach
#print axioms chartP_continuousOn_of_reach
#print axioms hVmapMeasK_at_p_of_reach
end AxiomChecks
