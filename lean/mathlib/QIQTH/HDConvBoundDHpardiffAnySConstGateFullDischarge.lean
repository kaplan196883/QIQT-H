/-
  HDConvBoundDHpardiffAnySConstGateFullDischarge — J4-1114: the FULL COMBINED closure of the `hgate`-FREE
  `boundD`/`hpardiff` census consumers at the concrete flow-ball gate `S := constGate g gi hC hK cR` —
  discharging `{hAmp0, hCfield}` INTERNALLY (J4-1112's mechanism, `CensusAmplitudeSupDischarge.
  census_amplitude_supBounds`, `S`-INDEPENDENT) TOGETHER WITH `hSupp` INTERNALLY (J4-1113's mechanism,
  `HsuppConstGateGrounded.hsupp_for_constGate`) in ONE theorem, exactly the combination J4-1113 flagged as
  its own natural next step.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS COMBINATION IS SAFE (no `hgate`/`S=univ` risk).  Both discharge mechanisms target the SAME
  `hgate`-FREE base consumers `CensusAnySEnvelopeRethread.witnessBoundD_wired_anyS` /
  `witnessHpardiff_wired_anyS` (J4-951), whose carried bundle is EXACTLY `{hAmp0, hCfield, hSupp}` — no
  `hgate`, no abstract `Cfield` field.  `census_amplitude_supBounds` (discharging `hAmp0`/`hCfield`) is
  provably `S`-INDEPENDENT (it never mentions the gate `S` at all — only `g,gi,hC,hK,a,b` and the standard
  geometry carries `{h0Kmem,hg,hg0,hu}`).  `hsupp_for_constGate` (discharging `hSupp`) is provably
  `{hAmp0,hCfield}`-INDEPENDENT (pure forward quadratic-displacement geometry).  Neither mechanism's proof
  touches the other's hypotheses or conclusion, so there is NO shared-variable conflict and NO hidden
  vacuity coupling between the two discharges — confirmed by direct audit of both source files
  (`CensusAmplitudeSupDischarge.lean`, `HsuppConstGateGrounded.lean`) AND by `gpt-5.6-sol` (high),
  consulted 2026-08-24 with the exact combined theorem shape BEFORE construction: (1) sound/non-circular
  (both producers are independent banked constants, no mutual dependency); (2) no interface incompatibility
  — `census_amplitude_supBounds`'s bound is genuinely `S`-independent, `hsupp_for_constGate`'s discharge
  needs neither `hAmp0` nor `hCfield`; (3) the nested `∃rAmp, ∃ρ₀, ∃C_D, (3 implications → …)` shape
  correctly combines J4-1112's `∃rAmp` wrapping with J4-1113's `∃ρ₀,∃C_D` wrapping, obtain order immaterial,
  no binder-name clash (`M`,`M'` kept fully internal, never exposed); (4) NOT an `S=univ`-style structural
  contradiction — the three antecedents (`D.r≤rAmp`, `cR≤ρ₀`, `cR·(1+C_D·cR)≤D.r`) are a genuine
  satisfiable coupling window for any `D.r>0`, mirroring the already-banked
  `hsupp_constGate_coupling_satisfiable` (the conditional CAN be vacuous for a badly-chosen fixed `D`/`cR`
  pair, exactly like any ordinary "small enough" real-analysis hypothesis — NOT a structural/definitional
  impossibility of the J4-1104 `hgate`⟹`S=univ` kind, since this family carries no `hgate` at all).

  ## THE COMBINED DISCHARGE.  `census_amplitude_supBounds g gi hC hK a b (T+1) … h0Kmem hg hg0 hu` supplies
  `rAmp>0, M,M'≥0` with the sup-bounds on `ball 0 rAmp`; under `D.r ≤ rAmp`, radius monotonicity gives
  `hAmp0`/`hCfield` in their EXACT `witnessBoundD_wired_anyS`/`witnessHpardiff_wired_anyS` shapes (no
  linking carry needed — unlike J4-1112's `hDConv_derivSide_census_ampzero_reduced`, THIS family's
  `hCfield` is already stated directly on `censusAmpTauDeriv`, no abstract `Cfield` field / `hCfieldEq` to
  bridge).  `hsupp_for_constGate g gi hC hK` supplies `ρ₀>0, C_D≥0`; under `cR≤ρ₀` and the coupling
  `cR·(1+C_D·cR)≤D.r`, `hsupp_disch D hcR hcρ hcoup` gives `hSupp` at `S := constGate g gi hC hK cR`.  All
  three discharged facts feed `witnessBoundD_wired_anyS`/`witnessHpardiff_wired_anyS` (J4-951) alongside the
  SMALLEST remaining carries `{hFzero, hFdom, hAmeas, hDmeas, hbase}` (plus `C_L,hC_L` and the standard
  geometry carries `{h0Kmem,hg,hg0,hu}` themselves).  Pure find-and-wire composition, zero new analytic
  content, at the concrete `constGate` gate, in the `hgate`-free sibling family.

  ⚠  STILL NOT `a₁ = R/6`.  `hFzero`/`hFdom`/`hAmeas`/`hDmeas`/`hbase` remain carried, UNDISCHARGED, exactly
  as in `witnessBoundD_wired_anyS`/`witnessHpardiff_wired_anyS` themselves.  The `hgate`-CARRYING family
  (`HDConvGateCensusDerivWired`/`HDConvGateAmpZeroFurtherReduced`) remains untouched/unaffected by this
  file — the `hgate` `S=univ`-forcing wall (J4-1104) is STILL open for THAT family specifically; this file
  continues to sidestep it via the parallel `hgate`-free `CensusAnySEnvelopeRethread` family.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.CensusAnySEnvelopeRethread
import QIQTH.CensusAmplitudeSupDischarge
import QIQTH.HsuppConstGateGrounded

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
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvBoundDHpardiffAnySConstGateFullDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1114 — `hDConv_boundD_hpardiff_anyS_constGate_full_wired`.**  The `hgate`-FREE `boundD`/
    `hpardiff` census consumers (`CensusAnySEnvelopeRethread.witnessBoundD_wired_anyS` /
    `witnessHpardiff_wired_anyS`, J4-951) at the concrete flow-ball gate `S := constGate g gi hC hK cR`,
    with `{hAmp0, hCfield}` DISCHARGED INTERNALLY via `CensusAmplitudeSupDischarge.census_amplitude_
    supBounds` (J4-1112's mechanism, `S`-independent) AND `hSupp` DISCHARGED INTERNALLY via
    `HsuppConstGateGrounded.hsupp_for_constGate` (J4-1113's mechanism) — ALL THREE combined in ONE
    theorem, modulo the explicit, satisfiable radius couplings `D.r ≤ rAmp`, `0 < cR ≤ ρ₀`,
    `cR·(1 + C_D·cR) ≤ D.r`.  `hFzero`/`hFdom`/`hAmeas`/`hDmeas`/`hbase` remain ordinary caller-supplied
    hypotheses, UNCHANGED — the smallest remaining carry set.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_boundD_hpardiff_anyS_constGate_full_wired (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (cR : ℝ) (hcR : 0 < cR)
    (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAmeas : ∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b (u' - s) 0 z * F s z 0)
        volume)
    (hDmeas : ∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b r 0 z)
            (c - s) * F s z 0)
        volume)
    (hbase : ∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b (c - s) 0 z * F s z 0)
        volume) :
    ∃ rAmp : ℝ, 0 < rAmp ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧
      (D.r ≤ rAmp → cR ≤ ρ₀ → cR * (1 + C_D * cR) ≤ D.r →
    ∃ boundD : ℕ → ℝ → ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b r 0 z)
            (c - s) * F s z 0‖
          ≤ boundD m u s) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b (c - s)
            0 z * F s z 0)
          (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b r 0 z)
            (c - s) * F s z 0) c)) := by
  classical
  obtain ⟨rAmp, hrAmp, M, M', hM, hM', hampBnd, hcfBnd⟩ :=
    census_amplitude_supBounds g gi hC hK a b (T + 1) (by linarith) h0Kmem hg hg0 hu
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hsupp_disch⟩ := hsupp_for_constGate g gi hC hK
  refine ⟨rAmp, hrAmp, ρ₀, hρ₀, C_D, hCD0, fun hDr hcρ hcoup => ?_⟩
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK a b τ z 0| ≤ M := by
    intro τ hτ hτ0 z _ hzr
    exact hampBnd τ hτ hτ0 z (lt_of_lt_of_le hzr hDr)
  have hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M' := by
    intro z _ hzr
    exact hcfBnd z (lt_of_lt_of_le hzr hDr)
  have hSupp : ∀ z ∈ K, (0 : Point n) ∈ constGate g gi hC hK cR z → ‖z‖ < D.r :=
    hsupp_disch D hcR hcρ hcoup
  obtain ⟨boundD, hbdd_d, hbound_d⟩ :=
    witnessBoundD_wired_anyS hn g gi hC hK (constGate g gi hC hK cR) a b D F T hT U hUT
      M M' C_L hM hM' hC_L hAmp0 hCfield hSupp hFzero hFdom
  have hpardiff :=
    witnessHpardiff_wired_anyS hn g gi hC hK (constGate g gi hC hK cR) a b D F T hT U hUT
      M M' C_L hM hM' hC_L hAmp0 hCfield hSupp hFzero hFdom hAmeas hDmeas hbase
  exact ⟨boundD, hbdd_d, hbound_d, hpardiff⟩

end QIQTH.HDConvBoundDHpardiffAnySConstGateFullDischarge

section AxiomChecks
open QIQTH.HDConvBoundDHpardiffAnySConstGateFullDischarge
#print axioms hDConv_boundD_hpardiff_anyS_constGate_full_wired
end AxiomChecks
