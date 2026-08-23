/-
  HDConvBoundDHpardiffAnySConstGateHsupp — J4-1113: `hSupp`'s OWN SEPARATE constGate discharge (the
  `hDConv`-side `boundD`/`hpardiff` census consumers, on the `hgate`-FREE any-`S` supplier family), via
  the already-banked `HsuppConstGateGrounded.hsupp_for_constGate` (J4-1112 found `hSupp` dischargeable at
  `S := constGate` but deliberately did NOT wire it in, to avoid mixing an abstract-`S` reduction with a
  `constGate`-specific one in ONE theorem; this file is that deliberately-deferred separate brick).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / gate-specialization brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY *NOT* `HDConvGateAmpZeroFurtherReduced.hDConv_derivSide_census_ampzero_reduced` DIRECTLY.
  J4-1112's own theorem still carries the mild carry `hgate : ∀ w, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2
  ∧ HasDerivAt …` VERBATIM, UNCHANGED (per its own header, deliberately, per J4-1104's earlier finding
  that `hgate`'s first conjunct universally quantifies the FIELD point `w.2.1` over ALL of `Point n`,
  forcing `S q = Set.univ` for every `q ∈ K`).  If `S` were specialized to the FINITE-RADIUS
  `constGate g gi hC hK cR` in THAT theorem while `hgate` is carried forward literally, the resulting
  hypothesis bundle would be — for any NONEMPTY `K` (forced by `h0Kmem : K ∈ 𝓝 0`) — jointly
  UNSATISFIABLE (`constGate … cR z ≠ Set.univ` for a finite ball-image, yet `hgate` demands exactly
  that), i.e. a VACUOUS antecedent trap of EXACTLY the kind J4-1104 already flagged and J4-1103
  deliberately avoided by never combining a `constGate` specialization with an `hgate`-carrying theorem.
  `gpt-5.6-sol` (high) consulted 2026-08-24, confirmed this concern precisely (independent of the
  `hSupp`-discharge mechanism itself, which is sound) and flagged it as the decisive reason NOT to
  specialize J4-1112's literal theorem at `constGate`.

  ## THE FIX — target the `hgate`-FREE sibling family instead.  `CensusAnySEnvelopeRethread`
  (J4-951, already banked) supplies `witnessBoundD_wired_anyS` / `witnessHpardiff_wired_anyS` — the
  IDENTICAL `boundD`/`hpardiff` census consumers J4-1112 itself assembles internally (via the OLD
  `witnessBoundD_wired`/`witnessHpardiff_wired`), but built on the any-`S` supplier
  `witnessTimeDeriv_domination_global_anyS` (J4-950), whose carried bundle is `{hAmp0, hCfield, hSupp}`
  — `hgate` and the `Cfield` field are ALREADY GONE from this sibling family (J4-951's own header:
  "NO `hgate`, NO `Cfield` field, for ANY `S`").  So specializing `S := constGate g gi hC hK cR` here
  carries NO `hgate`-vacuity risk whatsoever — the only gate-related carry left is `hSupp` itself, which
  THIS file discharges via `hsupp_for_constGate`.

  ## THE DISCHARGE.  `hsupp_for_constGate` supplies flow constants `ρ₀ > 0`, `C_D ≥ 0` (pure geometry,
  from the banked forward quadratic-displacement bound) such that, for `0 < cR ≤ ρ₀` and the radius
  coupling `cR·(1 + C_D·cR) ≤ D.r`, `hSupp : ∀ z ∈ K, 0 ∈ constGate g gi hC hK cR z → ‖z‖ < D.r` holds.
  Feeding this into `witnessBoundD_wired_anyS`/`witnessHpardiff_wired_anyS` (with `hAmp0`/`hCfield`
  carried as ordinary caller-supplied hypotheses, EXACTLY as those two base theorems themselves require
  — no additional reduction attempted here, keeping this brick focused SOLELY on `hSupp`) discharges
  BOTH consumers at the concrete `constGate` gate.  Mirrors the `HsuppConstGateGrounded`/`hsupp_for_
  constGate_satisfiable` non-vacuity pattern: the coupling window `(1+C_D)·cR ≤ D.r` (via
  `hsupp_constGate_coupling_satisfiable`, already banked) is genuinely non-empty for any `D.r > 0`.

  ⚠  STILL NOT `a₁ = R/6`.  `hFzero`/`hFdom`/`hAmeas`/`hDmeas`/`hbase`/`hAmp0`/`hCfield` remain carried,
  UNDISCHARGED, exactly as in `witnessBoundD_wired_anyS`/`witnessHpardiff_wired_anyS` themselves.
  `hgate`'s literal `S=univ`-forcing wall (J4-1104) is UNTOUCHED and remains open FOR THE `hgate`-CARRYING
  family specifically (`HDConvGateCensusDerivWired`/`HDConvGateAmpZeroFurtherReduced`) — this file does
  NOT close it, it SIDESTEPS it by working in the parallel `hgate`-free `CensusAnySEnvelopeRethread`
  family instead.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.CensusAnySEnvelopeRethread
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

namespace QIQTH.HDConvBoundDHpardiffAnySConstGateHsupp

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1113 — `hDConv_boundD_hpardiff_anyS_constGate_hsupp_wired`.**  The `hgate`-FREE
    `boundD`/`hpardiff` census consumers (`CensusAnySEnvelopeRethread.witnessBoundD_wired_anyS` /
    `witnessHpardiff_wired_anyS`, J4-951) at the concrete flow-ball gate `S := constGate g gi hC hK cR`,
    with `hSupp` DISCHARGED INTERNALLY via `HsuppConstGateGrounded.hsupp_for_constGate` (modulo the
    explicit, satisfiable radius coupling `0 < cR ≤ ρ₀`, `cR·(1 + C_D·cR) ≤ D.r`).  `hAmp0`/`hCfield`/
    `hFzero`/`hFdom`/`hAmeas`/`hDmeas`/`hbase` remain ordinary caller-supplied hypotheses, UNCHANGED —
    this brick discharges ONLY `hSupp`.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_boundD_hpardiff_anyS_constGate_hsupp_wired (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (cR : ℝ) (hcR : 0 < cR)
    (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (M M' C_L : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hC_L : 0 ≤ C_L)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M')
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
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_D : ℝ, 0 ≤ C_D ∧ (cR ≤ ρ₀ → cR * (1 + C_D * cR) ≤ D.r →
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
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hsupp_disch⟩ := hsupp_for_constGate g gi hC hK
  refine ⟨ρ₀, hρ₀, C_D, hCD0, fun hcρ hcoup => ?_⟩
  have hSupp : ∀ z ∈ K, (0 : Point n) ∈ constGate g gi hC hK cR z → ‖z‖ < D.r :=
    hsupp_disch D hcR hcρ hcoup
  obtain ⟨boundD, hbdd_d, hbound_d⟩ :=
    witnessBoundD_wired_anyS hn g gi hC hK (constGate g gi hC hK cR) a b D F T hT U hUT
      M M' C_L hM hM' hC_L hAmp0 hCfield hSupp hFzero hFdom
  have hpardiff :=
    witnessHpardiff_wired_anyS hn g gi hC hK (constGate g gi hC hK cR) a b D F T hT U hUT
      M M' C_L hM hM' hC_L hAmp0 hCfield hSupp hFzero hFdom hAmeas hDmeas hbase
  exact ⟨boundD, hbdd_d, hbound_d, hpardiff⟩

end QIQTH.HDConvBoundDHpardiffAnySConstGateHsupp

section AxiomChecks
open QIQTH.HDConvBoundDHpardiffAnySConstGateHsupp
#print axioms hDConv_boundD_hpardiff_anyS_constGate_hsupp_wired
end AxiomChecks
