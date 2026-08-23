/-
  HDConvBoundDHpardiffAnySConstGateHKmDischarged — J4-1117: separate discharge of J4-1116's `hKm`
  carry (`MeasurableSet K`), attempted per this dispatch's mandate to try `hKm`/`hSm0` SEPARATELY
  (not via the pre-intersected `ConcreteGateInstantiation.hKSmeas_concrete`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FIND.  `hKm : MeasurableSet K` is TRIVIALLY dischargeable: `K` is compact (`hK : IsCompact K`,
  a standing hypothesis of the whole theorem), and in a metric / T2 space `IsCompact K → IsClosed K`
  (`IsCompact.isClosed`), and every closed set is measurable (`IsClosed.measurableSet`).  So
  `hK.isClosed.measurableSet : MeasurableSet K` closes `hKm` with NO further input, NO gate-specific
  geometry, and NO use of `constGate`/`uniformFlowExp` at all.

  ## `hSm0` REMAINS OPEN (attempted, genuinely blocked — reported, not silently dropped).  `hSm0`'s set
  `{z : Point n | 0 ∈ constGate g gi hC hK cR z}` ranges over ALL `z : Point n`, NOT restricted to
  `z ∈ K`.  The only banked measurability lever for the gate
  (`ConcreteGateInstantiation.hKSmeas_concrete`, via Lusin–Souslin on the flow-graph map) proves joint
  measurability of `{(p,q) | q ∈ K ∧ p ∈ S q}` — continuity/injectivity of `uniformFlowExp` is proven
  ONLY on `K ×ˢ Metric.ball 0 ρ_K` (`FlowJointContinuity.uniformFlowExp_joint_continuousWithinAt`
  explicitly requires `q₀ ∈ K`).  Off `K`, `uniformFlowExp`'s underlying `uniformFlowTube` is built via
  `(uniformFlow_tube_exists g gi hC hK q w).choose`, and `uniformFlow_tube_exists`'s existential body is
  `q ∈ K → ‖w‖ ≤ ρ_K → (…)` — for `q ∉ K` this antecedent is FALSE, so the existential is satisfied
  VACUOUSLY by literally ANY `Y : ℝ → Point n × Point n`; `Classical.choice` need not pick the specific
  witness `fun _ => (q,w)` supplied in the existence PROOF (that witness only establishes existence, it
  is not what `.choose` is thereby forced to return).  So off `K`, `uniformFlowTube`/`uniformFlowExp`
  have NO pinned-down value, let alone continuity or measurability — `gpt-5.6-sol` (high) confirmed:
  NO-GO on a separate `hSm0` discharge today; "measurability of that arbitrary choice cannot be
  inferred from mere existence or retroactively supplied by measurable selection" (no Mathlib
  measurable-selection theorem applies retroactively to an ALREADY-FIXED, unconstrained `Classical.choose`
  selector).  `hSm0` is reported as a genuine, currently-open carry — NOT discharged here, NOT silently
  dropped, NOT weakened.

  ## NET EFFECT.  J4-1116's five-carry set `{hKm, hSm0, hIn, hInDeriv, hFslice}` REDUCES to the FOUR-carry
  set `{hSm0, hIn, hInDeriv, hFslice}` (`hKm` discharged unconditionally from `hK` alone).  `hFdom`/`hbase`
  unchanged.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.InverseChartNormalJets
open QIQTH.GatedTauDerivRep QIQTH.OnGateJets
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open QIQTH.DerivDomLowerCapped
open QIQTH.CensusAmplitudeSupDischarge QIQTH.CensusTauDerivGateSplit
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.CensusAnySEnvelopeRethread
open QIQTH.A1R6CoreAtGate QIQTH.HsuppConstGateGrounded
open QIQTH.HDConvBoundDHpardiffAnySConstGateFullDischarge
open QIQTH.HDuhamelCensusVanishingDischarged
open QIQTH.HDConvBoundDHpardiffAnySConstGateHFzeroDischarge
open QIQTH.HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvBoundDHpardiffAnySConstGateHKmDischarged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1117 — `hDConv_boundD_hpardiff_anyS_constGate_hkm_discharged`.**  J4-1116's
    `hDConv_boundD_hpardiff_anyS_constGate_ameas_dmeas_wired`, with the `hKm : MeasurableSet K` carry
    DISCHARGED internally (from `hK.isClosed.measurableSet`, needing nothing else).  Every other carry
    (`hSm0, hIn, hInDeriv, hFslice, hFdom, hbase`) UNCHANGED.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_boundD_hpardiff_anyS_constGate_hkm_discharged (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (cR : ℝ) (hcR : 0 < cR)
    (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ constGate g gi hC hK cR z})
    (hIn : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK) τ (0 : Point n) z)
      (volume : Measure (Point n)))
    (hInDeriv : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => deriv (fun r => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK) r (0 : Point n) z) τ)
      (volume : Measure (Point n)))
    (hFslice : ∀ s : ℝ, AEStronglyMeasurable
      (fun z => leviSeries (heatOp g gi
        (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z 0)
      (volume : Measure (Point n)))
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |leviSeries (heatOp g gi
          (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hbase : ∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b (c - s) 0 z
          * leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z 0)
        volume) :
    ∃ rAmp : ℝ, 0 < rAmp ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧
      (D.r ≤ rAmp → cR ≤ ρ₀ → cR * (1 + C_D * cR) ≤ D.r →
    ∃ boundD : ℕ → ℝ → ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b r 0 z)
            (c - s)
          * leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z 0‖
          ≤ boundD m u s) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b
            (c - s) 0 z
          * leviSeries (heatOp g gi
              (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z 0)
          (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b r 0 z)
              (c - s)
            * leviSeries (heatOp g gi
                (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z 0) c)) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  exact hDConv_boundD_hpardiff_anyS_constGate_ameas_dmeas_wired hn g gi hC hK cR hcR a b D T hT U hUT
    h0Kmem hg hg0 hu C_L hC_L hKm hSm0 hIn hInDeriv hFslice hFdom hbase

end QIQTH.HDConvBoundDHpardiffAnySConstGateHKmDischarged

section AxiomChecks
open QIQTH.HDConvBoundDHpardiffAnySConstGateHKmDischarged
#print axioms hDConv_boundD_hpardiff_anyS_constGate_hkm_discharged
end AxiomChecks
