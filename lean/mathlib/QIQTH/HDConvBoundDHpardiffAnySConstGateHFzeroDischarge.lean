/-
  HDConvBoundDHpardiffAnySConstGateHFzeroDischarge — J4-1115: FURTHER closing J4-1114's `hgate`-FREE
  `{hAmp0, hCfield, hSupp}`-discharged `constGate` theorem by ALSO discharging `hFzero` entirely — via
  the ALREADY-BANKED `HDuhamelCensusVanishingDischarged.hFzero_live` (J4-1112's mechanism, confirmed
  genuinely `S`-INDEPENDENT: it is proved for an ARBITRARY gate function `S`, never mentions `hgate`,
  `constGate`, or any vacuity risk), transferred DIRECTLY into the `anyS`/`constGate` family.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TRANSFER (mechanism).  J4-1114's `hDConv_boundD_hpardiff_anyS_constGate_full_wired` carries
  `F : ℝ → Point n → Point n → ℝ` FULLY ABSTRACT (no `hFeq` pinning it to a concrete formula), with
  `hFzero : ∀ s, s ≤ 0 → ∀ z y, F s z y = 0` a caller-supplied hypothesis about that abstract `F`.
  `HDuhamelCensusVanishingDischarged.hFzero_live (g gi hChr hK S a b hn)` proves EXACTLY this shape —
  `∀ s ≤ 0, ∀ z y, leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0` — for
  ANY gate function `S : Point n → Set (Point n)` (the proof never inspects `S`'s definition beyond
  generic geometry), so instantiating `S := constGate g gi hC hK cR` discharges `hFzero` for ANY `cR`.
  To USE it we must first fix `F` to that concrete formula via a new hypothesis
  `hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b))`,
  `subst`, then apply `hFzero_live … hn` (`hn : 0 < n` is defeq to `1 ≤ n` for `n : ℕ`, since
  `Nat.lt a b` unfolds to `Nat.le (a+1) b`). Under `subst`, `hFdom`/`hAmeas`/`hDmeas`/`hbase` (which also
  mention `F` in their own statements) become statements about the concrete formula instead of the
  abstract `F` — still ordinary caller-supplied hypotheses, UNCHANGED in analytic content, merely
  re-typed by the substitution — EXACTLY mirroring how J4-1112 already performed this identical trick in
  the `hgate`-CARRYING sibling family (`HDConvGateAmpZeroFurtherReduced`). Net effect: `hFzero` genuinely
  CLOSED (zero new *analytic* carries; one new *interface* carry `hFeq` fixing `F`'s identity, which is
  NOT itself an unproven analytic obligation — it is a definitional choice available to any caller who
  already intends to instantiate `F` concretely, exactly as `HDConvGateThreading.hDConv_AT_GATE` itself
  carries BOTH `F` and `hFeq` as a matter of course).

  `gpt-5.6-sol` (high) consulted 2026-08-24 with the exact literal types before construction: confirmed
  (1) the transfer is sound and non-circular — ordinary equality elimination, no hidden issue with fixing
  `F` via `hFeq` inside the `_anyS` family (neither `witnessBoundD_wired_anyS` nor
  `witnessHpardiff_wired_anyS` requires `F` to remain abstract; both consume `F` only via the carried
  hypotheses and the conclusion, all of which survive `subst` fine); (2) recommended `subst F` (via
  `hFeq`) exactly as J4-1112 already does; (3) separately assessed the `hFdom` cap-mismatch (T-vs-(T+1)
  is trivially fixable by instantiating the discharge theorem's own `T` argument as `T+1`, but the DEEPER
  mismatch — `cR`/`a`/`b` FREE in this family vs `(a,b,c)` being INTERNAL EXISTENTIAL OUTPUTS of
  `HFdomVanVleckHEmeasDischarged.hFdom_vanVleck_hEmeas_discharged`'s own `constRadius_package_and_S1`
  chain, which ALSO needs ~7 extra geometry carries not currently present here — `{hg,hgnd,hgsymm,
  hinvF,hframeK,hw,hdg0}` beyond the already-present `{hgiC,hgpos,hu,hgiMeas,hchr}`) is GENUINELY
  nontrivial, requiring either re-existentializing `cR,a,b` together with the produced `(a,b,c)` triple
  or a not-currently-banked transport/comparison lemma between an arbitrary `cR` and the produced `c`
  (mere set-inclusion is insufficient since changing the gate changes the witness `F` itself) — confirmed
  NOT a same-dispatch item, deferred to a future dedicated dispatch. Recommended scope for TODAY: the
  `hFzero` transfer ONLY.

  ⚠  STILL NOT `a₁ = R/6`.  `hFdom`/`hAmeas`/`hDmeas`/`hbase` remain carried, UNDISCHARGED (now stated
  about the concrete `F` formula rather than an abstract one, per the `hFeq` substitution — no analytic
  content changed). `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.HDConvBoundDHpardiffAnySConstGateFullDischarge
import QIQTH.HDuhamelCensusVanishingDischarged

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
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvBoundDHpardiffAnySConstGateHFzeroDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1115 — `hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired`.**  J4-1114's
    `hDConv_boundD_hpardiff_anyS_constGate_full_wired`, with the abstract `F`/`hFzero` pair REPLACED by
    `hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b))`
    — `hFzero` DERIVED internally via `HDuhamelCensusVanishingDischarged.hFzero_live` (zero new analytic
    carries). `{hAmp0,hCfield,hSupp}` remain discharged internally exactly as in J4-1114.
    `hFdom`/`hAmeas`/`hDmeas`/`hbase` UNCHANGED in analytic content (now typed on the concrete `F`).
    ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (cR : ℝ) (hcR : 0 < cR)
    (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi
        (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
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
  subst hFeq
  have hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK (constGate g gi hC hK cR) a b)) s z y
        = 0 :=
    hFzero_live g gi hC hK (constGate g gi hC hK cR) a b hn
  exact hDConv_boundD_hpardiff_anyS_constGate_full_wired hn g gi hC hK cR hcR a b D _ T hT U hUT
    h0Kmem hg hg0 hu C_L hC_L hFzero hFdom hAmeas hDmeas hbase

end QIQTH.HDConvBoundDHpardiffAnySConstGateHFzeroDischarge

section AxiomChecks
open QIQTH.HDConvBoundDHpardiffAnySConstGateHFzeroDischarge
#print axioms hDConv_boundD_hpardiff_anyS_constGate_hfzero_wired
end AxiomChecks
