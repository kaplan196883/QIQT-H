/-
  Hfwd2WeldUniform — Plan v6/v7 Task N: the `expRho`-FREE / `hReach`-FREE weld — the forward SECOND jet
  joint continuity `hFwd2` and the chart-Hessian base continuity it discharges, UNCONDITIONALLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.  NO `expRho`, NO `hReach`.

  ── THE ELIMINATION OF `hReach`.  `Hfwd2Weld.uniformFlowExp_forward2_continuousOn_of_reach` (J4-484)
  carried the K-uniform reachability `hReach : ∀ q ∈ K, uniformFlowRadius ≤ expRho q` for exactly ONE
  purpose: to convert `‖v‖ < uniformFlowRadius` into `‖v‖ < expRho q` so that the two `expRho`-gated
  slots (`Flow3Regularity.forward2_velocitySlot`, `HbaseJ2Assembly.uniformFlowExp_fderiv2_base_modulus`)
  applied.  `Flow3RegularityUniform` (Task N) re-anchored BOTH slots on the UNCONDITIONAL C⁴
  (`ExpMap.contDiffAt4_uniformFlowExp`, Task M), so they now hold from `‖v‖ < uniformFlowRadius` ALONE.
  Hence the weld needs NO `hReach`: the `expRho` guards vanished at the source.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`, NO `hReach`; NOT `a₁ = R/6`).
    * `uniformFlowExp_forward2_continuousOn` — ★★ THE WELD → `hFwd2`, UNCONDITIONAL.  The joint-in-`(z,v)`
      continuity of the forward SECOND jet `(z,v) ↦ fderiv² (uniformFlowExp … z) v` on
      `K ×ˢ ball 0 (uniformFlowRadius)`.  Exact mirror of
      `Hfwd2Weld.uniformFlowExp_forward2_continuousOn_of_reach`, using the `expRho`-free slots
      (`forward2_velocitySlot'`, `uniformFlowExp_fderiv2_base_modulus'`), `hReach` dropped.
    * `chartSecondJet_continuousOn` — ★★★ THE CHART HESSIAN BASE CONTINUITY, hFwd2-discharged,
      UNCONDITIONAL.  Feeds the welded `hFwd2` into `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`.
      Exact mirror of `Hfwd2Weld.chartSecondJet_continuousOn_of_reach`, `hReach` dropped; only the standing
      geometric carries `hW0`/`horigin`/`hunit`/`hid2` (the reduction's own) remain.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Flow3RegularityUniform
import QIQTH.ChartSecondJet

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.Flow3RegularityUniform
open scoped Topology

namespace QIQTH.Hfwd2WeldUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-! ###############################################################################
    ### ★★ THE WELD — the joint forward SECOND jet `hFwd2`, UNCONDITIONAL.
    ############################################################################### -/

/-- **★★ `uniformFlowExp_forward2_continuousOn` — THE WELD → `hFwd2`, UNCONDITIONAL.**  The joint-in-`(z,v)`
    continuity of the forward-flow SECOND jet `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v` on
    `K ×ˢ ball 0 (uniformFlowRadius)`.  The `z₀`-anchored triangle of
    `JacobiCLMExposure.forwardFlowJet_continuousOn` ONE DERIVATIVE UP: the VELOCITY slot
    (`Flow3RegularityUniform.forward2_velocitySlot'`, needing only `‖v‖ < uniformFlowRadius`) gives the
    fixed-base tendsto; the BASE modulus (`Flow3RegularityUniform.uniformFlowExp_fderiv2_base_modulus'`,
    needing only `‖v‖ < uniformFlowRadius`) squeezes the base-difference to `0`; their sum, `abel`'d, is
    the joint tendsto.  NO `expRho`, NO `hReach`.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_forward2_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  classical
  haveI hCA : ContinuousAdd (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    (inferInstance :
      IsTopologicalAddGroup (Point n →L[ℝ] Point n →L[ℝ] Point n)).toContinuousAdd
  obtain ⟨Λ, hΛ0, hmod⟩ := uniformFlowExp_fderiv2_base_modulus' g gi hC hK
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hw₀ : ‖p.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hp2
  -- VELOCITY slot at the fixed base `p.1`.
  have hvel : ContinuousAt
      (fun w : Point n => fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) w) p.2 :=
    forward2_velocitySlot' g gi hC hK p.1 hp1 p.2 hw₀
  have hfst : Tendsto (fun x : Point n × Point n => x.1)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.1) :=
    (continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds
  have hsndp : Tendsto (fun x : Point n × Point n => x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p)
      (𝓝 (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) p.2)) :=
    hvel.tendsto.comp hsndp
  have htend : Tendsto (fun x : Point n × Point n => Λ * ‖x.1 - p.1‖)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    have hc : Continuous (fun z : Point n => Λ * ‖z - p.1‖) := by fun_prop
    have h := (hc.tendsto p.1).comp hfst
    simpa using h
  -- BASE modulus squeezes the base-difference to `0` (only `‖v‖ < uniformFlowRadius` needed).
  have hdiff : Tendsto (fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    have hbound : ∀ᶠ x : Point n × Point n in
        𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p,
        ‖fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
            - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2‖
          ≤ Λ * ‖x.1 - p.1‖ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx2' : ‖x.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hx2
      exact hmod x.1 hx1 p.1 hp1 x.2 hx2'
    exact squeeze_zero_norm'
      (f := fun x : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK x.1)) x.2
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) x.2)
      hbound htend
  have hcomb := hdiff.add hsnd
  simp only [zero_add] at hcomb
  exact Filter.Tendsto.congr (fun x => by abel) hcomb

/-! ###############################################################################
    ### ★★★ THE CHART HESSIAN BASE CONTINUITY — hFwd2 discharged, UNCONDITIONAL.
    ############################################################################### -/

/-- **★★★ `chartSecondJet_continuousOn` — THE CHART HESSIAN BASE CONTINUITY, hFwd2-discharged,
    UNCONDITIONAL.**  Feeds the welded `hFwd2` (`uniformFlowExp_forward2_continuousOn`) into the J4-479
    reduction `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`.  For `U ⊆ K` with the banked
    origin section `hW0`, origin smallness `horigin`, nondegeneracy `hunit`, and the per-`z` 2nd-jet IFT
    identity `hid2` (all supplied by `ChartSecondJet`), the chart SECOND field-jet at the field centre
        `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0`
    is base-continuous on `U` — with the `hFwd2` atom DISCHARGED and NO `hReach` replacement.  NOT
    `a₁ = R/6`. -/
theorem chartSecondJet_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hid2 : ∀ z ∈ U,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0))))) :
    ContinuousOn
      (fun z : Point n => fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0) U :=
  ChartSecondJet.chartSecondJet_continuousOn_of_forward2 g gi hC hK hUK hW0 horigin hunit
    (uniformFlowExp_forward2_continuousOn g gi hC hK) hid2

end QIQTH.Hfwd2WeldUniform

section AxiomChecks
open QIQTH.Hfwd2WeldUniform
#print axioms uniformFlowExp_forward2_continuousOn
#print axioms chartSecondJet_continuousOn
end AxiomChecks
