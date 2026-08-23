/-
  HDConvAtGateConstGateHUfloor — J4-1108: `hUfloor` DROPPED from J4-1103's `hDConv_AT_GATE_constGate`
  (the `constGate` gate specialization) via J4-1101's gate-agnostic `hUfloor_of_windowFloor` reduction —
  a genuine consolidation of TWO previously-separate census-reduction techniques onto the SAME concrete
  `S := constGate g gi hChr hK c` gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS DISPATCH.  This session's census-consolidation sweep (following J4-1102/1103/1106/1107)
  found that `hDConv_AT_GATE_constGate` (`HDConvAtGateConstGateHAdom.lean`, J4-1103) — which specializes
  `HDConvGateThreading.hDConv_AT_GATE`'s abstract `S` to the concrete flow-ball gate
  `constGate g gi hChr hK c` and discharges `hAdom`/`hWDom` (12 binders) — still carries `hUfloor` as an
  UNTOUCHED explicit hypothesis, even though `HDConvGateCensusReduce.hDConv_AT_GATE_censusReduced`
  (J4-1101) already showed `hUfloor` is GATE-AGNOSTIC: it re-derives purely from the `aT`/`haT`/`hUlb`
  data `hDConv_AT_GATE` already carries for the unrelated `hDaLimLU_concrete` leg, via
  `HDuhamelBoundaryModulusUniform.hUfloor_of_windowFloor`, with NO reference to `S` anywhere in the
  proof (`⟨aT, haT, hUlb⟩` — a bare `Exists.intro`). Since that derivation never touches `S`, it applies
  literally verbatim at `S := constGate g gi hChr hK c` too — this file wires that composition in,
  landing `hUfloor` as a THIRD member discharged at the SAME concrete gate J4-1103/J4-1107 already used
  (alongside `hAdom`/`hWDom` and, separately, `hFdom`-with-`hEmeas`).

  Pure find-and-wire composition (identical pattern to J4-1101/1103/1107); no new analytic content, no
  new rate/asymptotic claim, so no fresh sympy check is needed per the standing rule's scope.

  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`. Pure
  COMPOSITION / census-shrink brick. No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ⚠  STILL NOT MERGED WITH `hFdom` (J4-1107).  `hDConv_AT_GATE_constGate` (and hence this file) still
  carries `hFdom` as an EXPLICIT hypothesis, for ARBITRARY `a b : ℝ` and ARBITRARY `c` below
  `flowBallRadiusThreshold g gi hChr hK`. `HFdomVanVleckHEmeasDischarged.hFdom_vanVleck_hEmeas_discharged`
  (J4-1107) discharges `hFdom` unconditionally, but at its OWN existentially-produced `a, b, c, δ₀`
  (from `ConstRadiusGateExport.constRadius_package_and_S1`), where `δ₀` is a function of
  `(hn, g, gi, hC, hK, a, b)` alone (`tripleHEmeas_flowball_geometry`) while `flowBallRadiusThreshold` is
  a function of `(g, gi, hChr, hK)` alone (`GateSqControlFromFlowBall.gateSqControl_constGate`) — TWO
  INDEPENDENTLY-CONSTRUCTED positive-radius thresholds with NO known comparison lemma between them, and
  no known lemma lower-bounding `δ₀(a,b)` below `b` for small `a,b`. Merging `hFdom`'s discharge into
  `hDConv_AT_GATE_constGate` at ONE SHARED `(a,b,c)` would require EITHER such a comparison lemma OR a
  fresh, `a,b`-generic reproof of `tripleHEmeas_flowball_geometry`'s reach bound in terms of
  `flowBallRadiusThreshold` directly — genuinely open, NOT attempted this dispatch (flagged, matching the
  J4-1104 "blocked without a reprove" pattern, not a presentation mismatch).

  ⚠  Remaining ~24 `hDConv_AT_GATE` census members (`hEdom`, `hLapFull`, `hII_lo/hi`, the `hFII`
  family beyond `hMeasFII`/`hInnerCont`, `hQ1`, `hFmeas`/`hFint`/`hF'meas` (+ `_d` variants),
  `boundD`/`hbdd_d`/`hbound_d`/`hpardiff`, `L`/`hLnn`/`hCross`) remain FULLY OPEN and UNCHECKED against
  this gate. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.HDConvAtGateConstGateHAdom
import QIQTH.HDuhamelBoundaryModulusUniform

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.HDConvGateThreading QIQTH.GateSqControlFromFlowBall QIQTH.A1R6CoreAtGate
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HAdomHWDomFromConcreteDominations QIQTH.ResidueBound
open QIQTH.HDConvAtGateConstGateHAdom
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.HDConvAtGateConstGateHUfloor

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-1108 — `hDConv_AT_GATE_constGate_hUfloor`.** `HDConvAtGateConstGateHAdom.
    hDConv_AT_GATE_constGate` (J4-1103, `hAdom`/`hWDom` already discharged at `S := constGate g gi hChr
    hK c`) with `hUfloor` DROPPED, re-derived internally from the SAME `aT`/`haT`/`hUlb` data via
    `HDuhamelBoundaryModulusUniform.hUfloor_of_windowFloor` (J4-1101's gate-agnostic reduction). Same
    conclusion, same remaining binders minus `hUfloor`, at the SAME concrete constant-radius gate. ⚠ NOT
    `a₁ = R/6`. -/
theorem hDConv_AT_GATE_constGate_hUfloor (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (hc : 0 < c)
    (hcle : c ≤ flowBallRadiusThreshold g gi hChr hK)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k : Point n → ℝ))
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c)
        a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F
            u (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i
              (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_lo : MemAdjLo F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_hi : MemAdjHi F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
            (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
        * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
        * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r
          0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z)
          (cc - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
          (cc - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z)
          (cc - s) * F s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F (u + h)
          (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F (u + h)
              (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F u
              (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) F u
              (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ Cf Cmass : ℝ) (ta tb : ℝ) (hρ : 0 < ρ)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z)
        volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b
        (epsSeq m) (0 : Point n) z| ≤ Cmass)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m)
            (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t := by
  have hUfloor : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ u ∈ U, c₁ ≤ u :=
    QIQTH.HDuhamelBoundaryModulusUniform.hUfloor_of_windowFloor aT haT hUlb
  exact QIQTH.HDConvAtGateConstGateHAdom.hDConv_AT_GATE_constGate g gi hChr hK c hc hcle a b ha hab hw
    F hFeq t T hT U hUopen htU hUT hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi hEcomb
    hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff
    L hLnn hCross
    ρ Cf Cmass ta tb hρ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hmass hmassone hmod hsup hUsub

end QIQTH.HDConvAtGateConstGateHUfloor

section AxiomChecks
open QIQTH.HDConvAtGateConstGateHUfloor
#print axioms hDConv_AT_GATE_constGate_hUfloor
end AxiomChecks
