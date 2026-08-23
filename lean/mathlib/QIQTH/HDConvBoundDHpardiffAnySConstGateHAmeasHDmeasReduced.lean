/-
  HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced — J4-1116: FURTHER shrinking J4-1115's carry
  set by REPLACING the two entangled product-measurability carries `{hAmeas, hDmeas}` with the FIVE
  lighter, non-entangled carries `{hKm, hSm0, hIn, hInDeriv, hFslice}` — `hAmeas` via the ALREADY-BANKED
  `HFmeasGFromFieldSlice.hFmeasG_of_field_slice` (J4-973), `hDmeas` via the NEW
  `HDmeasGFromFieldSliceTimeDeriv.hDmeasG_of_field_slice` (this dispatch's own §C, built alongside).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE COMPOSITION.  J4-1115's `hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired` carries `hAmeas` and
  `hDmeas` as raw product-measurability hypotheses about the concrete `S := constGate g gi hC hK cR`,
  `F := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b))` (fixed
  via `hFeq`).  Both are DROP-IN instances of the `_anyS`/generic-S product-measurability reducers:
    • `hAmeas` — EXACTLY `HFmeasGFromFieldSlice.hFmeasG_of_field_slice`'s conclusion (J4-973, already
      banked) at `S := constGate g gi hC hK cR`, `cutA := a`, `cutB := b`, from `{hKm, hSm0, hIn, hFslice}`.
    • `hDmeas` — EXACTLY `HDmeasGFromFieldSliceTimeDeriv.hDmeasG_of_field_slice`'s conclusion (this
      dispatch, new) at the same specialization, from `{hKm, hSm0, hInDeriv, hFslice}` (`hKm`/`hSm0`/
      `hFslice` SHARED with the `hAmeas` reduction; `hIn`/`hInDeriv` are the (un-differentiated /
      τ-differentiated) inner-kernel z-slice measurability carries, genuinely different from each other —
      `gpt-5.6-sol` (high) confirmed `hInDeriv` is neither implied by `hIn` alone nor a logical weakening of
      `hDmeas`, but a strictly lighter, honest, non-entangled carry).  Neither `hgate` nor `Cfield` is
      present anywhere in this chain (the `_anyS`/`constGate` family), so no J4-1104-style vacuity risk.

  ## NET EFFECT.  `{hAmeas, hDmeas}` (2 entangled witness·F product carries) REPLACED by
  `{hKm, hSm0, hIn, hInDeriv, hFslice}` (5 honest, non-entangled, lighter carries) inside J4-1115's own
  theorem — a genuine carrier-complexity reduction (relocating, not eliminating, the analytic content;
  `hIn`/`hInDeriv` remain carried, satisfiable, non-vacuous, never the conclusion), NOT a full discharge.
  `hFdom`/`hbase` remain UNCHANGED, untouched.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDConvBoundDHpardiffAnySConstGateHFzeroDischarge
import QIQTH.HFmeasGFromFieldSlice
import QIQTH.HDmeasGFromFieldSliceTimeDeriv

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
open QIQTH.HFmeasGFromFieldSlice
open QIQTH.HDmeasGFromFieldSliceTimeDeriv
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1116 — `hDConv_boundD_hpardiff_anyS_constGate_ameas_dmeas_wired`.**  J4-1115's
    `hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired`, with `hAmeas`/`hDmeas` REPLACED by
    `{hKm, hSm0, hIn, hInDeriv, hFslice}` — `hAmeas` derived via `HFmeasGFromFieldSlice
    .hFmeasG_of_field_slice` (J4-973), `hDmeas` derived via `HDmeasGFromFieldSliceTimeDeriv
    .hDmeasG_of_field_slice` (this dispatch).  Every other carry (`hFdom`, `hbase`, standard geometry)
    UNCHANGED.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_boundD_hpardiff_anyS_constGate_ameas_dmeas_wired (hn : 0 < n)
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
    (hKm : MeasurableSet K)
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
  have hAmeas := hFmeasG_of_field_slice g gi hC hK (constGate g gi hC hK cR) a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)))
    hKm hSm0 hIn hFslice
  have hDmeas := hDmeasG_of_field_slice g gi hC hK (constGate g gi hC hK cR) a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)))
    hKm hSm0 hInDeriv hFslice
  exact hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired hn g gi hC hK cR hcR a b D _ rfl T hT U hUT
    h0Kmem hg hg0 hu C_L hC_L hFdom hAmeas hDmeas hbase

end QIQTH.HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced

section AxiomChecks
open QIQTH.HDConvBoundDHpardiffAnySConstGateHAmeasHDmeasReduced
#print axioms hDConv_boundD_hpardiff_anyS_constGate_ameas_dmeas_wired
end AxiomChecks
