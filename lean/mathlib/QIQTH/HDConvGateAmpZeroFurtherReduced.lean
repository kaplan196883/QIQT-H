/-
  HDConvGateAmpZeroFurtherReduced — J4-1112: FURTHER reducing TWO of J4-1102's `hDConv_derivSide_
  census_wired` mild carries — `hAmp0`/`hCfield` (traded for standard geometry carries via the
  ALREADY-BANKED `CensusAmplitudeSupDischarge.census_amplitude_supBounds`) and `hFzero` (CLOSED
  entirely, zero new carries, via the ALREADY-BANKED `HDuhamelCensusVanishingDischarged.hFzero_live`)
  — an under-crediting catch, mirroring the J4-1101/1102/1105/1109/1110/1111 sibling-cross-wiring
  pattern, INDEPENDENT of the `hgate` blockage J4-1104 confirmed genuine (this file does NOT touch
  `hgate`, `hSupp`, `hFdom`, `hAmeas`, `hDmeas`, or `hbase`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## `hAmp0`/`hCfield` (mechanism).  `CensusAmplitudeSupDischarge.census_amplitude_supBounds` proves,
  UNCONDITIONALLY ON `S` (it never mentions the gate at all — `chartFieldAmp`/`censusAmpTauDeriv` only
  depend on `g,gi,hC,hK,a,b`), from ONLY the standard geometry carries `{h0Kmem : K ∈ 𝓝 0, hg, hg0, hu}`
  and a time cap `τ₀ > 0`: `∃ rAmp>0, ∃ M M'≥0, (∀τ,0<τ→τ≤τ₀→∀z,‖z‖<rAmp→|chartFieldAmp…τ z 0|≤M) ∧
  (∀z,‖z‖<rAmp→|censusAmpTauDeriv…z|≤M')`.  Instantiating `τ₀ := T+1` (J4-1102's own cap-shift) and
  threading the benign per-`D` radius compat `D.r ≤ rAmp` (EXACTLY as `CensusAmplitudeSupDischarge`'s
  own `censusBound_of_geometry_gate_supp_F_ballRate` proof already does) converts this into `hAmp0`'s
  and (modulo one honest compatibility carry `hCfieldEq : ∀ z, Cfield z 0 = censusAmpTauDeriv … z`,
  linking the caller's general-field-point `Cfield` — the SAME `Cfield` `hgate`'s untouched `HasDerivAt`
  clause needs — to the census slope AT FIELD POINT `0`) `hCfield`'s literal shape.  `M`/`M'` become
  INTERNAL (produced, not carried).

  ## `hFzero` (mechanism).  J4-1102's `hFzero` is stated for an ABSTRACT `F` (no `hFeq` binder in that
  file).  To discharge it we must ALSO fix `F` to the concrete `leviSeries (heatOp g gi
  (vanVleckGatedWitness g gi hC hK S a b))` via an explicit `hFeq` hypothesis (mirroring J4-1109's
  `subst hFeq` pattern for `hQ1`, and matching how `HDConvGateThreading.hDConv_AT_GATE` itself carries
  BOTH `F` and `hFeq`).  Under `hFeq`, `HDuhamelCensusVanishingDischarged.hFzero_live` — banked for the
  `hDuhamel`-side capstone, documented "shared … AND `hDConv`" but never re-wired here, the SAME
  under-crediting gap J4-1101–1111 corrected repeatedly — supplies `hFzero`'s EXACT shape from PURE
  geometry (`g,gi,hC,hK,S,a,b,hn`) alone: ZERO new analytic carries (only `hn`, already present).

  `gpt-5.6-sol` (high) consulted 2026-08-24 with the exact literal types before construction: confirmed
  (a) `census_amplitude_supBounds` is genuinely `S`-independent and sound; (b) the `D.r ≤ rAmp` radius
  compat must be threaded honestly as a real antecedent (not hidden), mirroring the source theorem's own
  `∃ rAmp, 0<rAmp ∧ (D.r≤rAmp → …)` wrapping; (c) `hCfieldEq` is a genuine, non-circular linking carry
  (NOT a disguised `hCfield`/`hAmp0` restatement — it constrains `Cfield` only AT FIELD POINT `0`,
  strictly weaker than the full `hgate` derivative clause); (d) `hFzero_live`'s reuse is sound (does not
  depend on `hDConv_AT_GATE` or reuse `hFzero`/`hAmp0`/`hCfield` as inputs); (e) confirmed keeping `hgate`
  literally UNCHANGED (still the genuinely-blocked `∀ p` shape, per J4-1104) is the correct scope for
  this dispatch — recommended building exactly this reduction TODAY as self-contained, low-risk.

  ⚠  STILL NOT `a₁ = R/6`.  `hgate` (the genuine `S = Set.univ`-forcing blockage, J4-1104), `hSupp`
  (dischargeable ONLY at `constGate`, `HsuppConstGateGrounded`, untouched here), `hFdom` (cap-mismatched
  T-vs-(T+1) reductions exist, J4-1105–1107, untouched here), and `hAmeas`/`hDmeas`/`hbase` (measurability
  combinators exist — `WitnessMeasDeriv`/`WitnessDerivMeasurability` — but NO banked single-call producer
  of the actual `Integrable (…)` conclusion `hbase` needs; genuine new synthesis, NOT attempted here) all
  remain fully open, untouched carries.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import Mathlib
import QIQTH.HDConvGateCensusDerivWired
import QIQTH.CensusAmplitudeSupDischarge
import QIQTH.HDuhamelCensusVanishingDischarged

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.InverseChartNormalJets
open QIQTH.GatedTauDerivRep QIQTH.OnGateJets
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open QIQTH.DerivDomLowerCapped QIQTH.WitnessBoundDHpardiffWired
open QIQTH.CensusAmplitudeSupDischarge QIQTH.CensusTauDerivGateSplit
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.HDuhamelCensusVanishingDischarged
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvGateAmpZeroFurtherReduced

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1112 — `hDConv_derivSide_census_ampzero_reduced`.**  `HDConvGateCensusDerivWired.
    hDConv_derivSide_census_wired`'s IDENTICAL conclusion, with `hAmp0`/`hCfield`/`M`/`M'`/`hM`/`hM'`
    REPLACED by the standard geometry carries `{h0Kmem, hg, hg0, hu}` + the benign radius compat
    `D.r ≤ rAmp` + the field-point-`0` linking carry `hCfieldEq`, and `hFzero` REPLACED by `hFeq`
    (fixing the abstract `F` to the concrete `leviSeries (heatOp g gi (vanVleckGatedWitness … S a b))`,
    exactly as `HDConvGateThreading.hDConv_AT_GATE` itself carries `F`+`hFeq`) — DERIVED internally, zero
    new carries beyond `hFeq`.  `hgate`/`hSupp`/`hFdom`/`hAmeas`/`hDmeas`/`hbase` UNCHANGED, forwarded
    verbatim.  ⚠ NOT `a₁ = R/6`. -/
theorem hDConv_derivSide_census_ampzero_reduced (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hCfieldEq : ∀ z, Cfield z 0 = censusAmpTauDeriv g gi hC hK a b z)
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAmeas : ∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (u' - s) 0 z * F s z 0) volume)
    (hDmeas : ∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
        volume)
    (hbase : ∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) :
    ∃ rAmp : ℝ, 0 < rAmp ∧ (D.r ≤ rAmp →
    ∃ (nb : ℕ → ℝ → Set ℝ) (boundD : ℕ → ℝ → ℝ → ℝ),
      (∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u) ∧
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0‖
          ≤ boundD m u s) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
        HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0)
          (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0) c)) := by
  classical
  obtain ⟨rAmp, hrAmp, M, M', hM, hM', hampBnd, hcfBnd⟩ :=
    census_amplitude_supBounds g gi hC hK a b (T + 1) (by linarith) h0Kmem hg hg0 hu
  refine ⟨rAmp, hrAmp, fun hDr => ?_⟩
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK a b τ z 0| ≤ M := by
    intro τ hτ hτ0 z _ hzr
    exact hampBnd τ hτ hτ0 z (lt_of_lt_of_le hzr hDr)
  have hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M' := by
    intro z _ hzr
    rw [hCfieldEq z]
    exact hcfBnd z (lt_of_lt_of_le hzr hDr)
  have hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0 := by
    subst hFeq
    exact hFzero_live g gi hC hK S a b hn
  obtain ⟨boundD, hbdd_d, hbound_d⟩ := witnessBoundD_wired hn g gi hC hK S a b D F T hT U hUT
    M M' C_L hM hM' hC_L Cfield hgate hAmp0 hCfield hSupp hFzero hFdom
  have hpardiff := witnessHpardiff_wired hn g gi hC hK S a b D F T hT U hUT
    M M' C_L hM hM' hC_L Cfield hgate hAmp0 hCfield hSupp hFzero hFdom hAmeas hDmeas hbase
  exact ⟨derivDomNb, boundD, fun m u _ => derivDomNb_mem_nhds m u, hbdd_d, hbound_d, hpardiff⟩

end QIQTH.HDConvGateAmpZeroFurtherReduced

section AxiomChecks
open QIQTH.HDConvGateAmpZeroFurtherReduced
#print axioms hDConv_derivSide_census_ampzero_reduced
end AxiomChecks
