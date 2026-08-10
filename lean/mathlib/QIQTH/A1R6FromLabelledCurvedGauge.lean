/-
  A1R6FromLabelledCurvedGauge — J4-520: the CURVED-VALID hframeK-channel rewire of the a₁ capstone,
  built ON TOP of J4-519's `A1R6FromLabelledCurved.a1_R6_from_labelled_curved` (which already removed the
  flat-only LINEAR `hraw` label via the quadratic `hgate`).  This file removes the SECOND flat-only
  binder, the neighbourhood frame condition
      `hframeK : ∀ q ∈ K, g q = δ`
  which forces `∂²g = 0` on `K` (⟹ Riemann = 0 ⟹ Ric(0) = 0) — FLAT-ONLY.  It is consumed INSIDE
  `LabelledRethreadV2.hDaLimLU_from_labelled_v2` at EXACTLY ONE place, the gauge sub-assembly
      `obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0`
  where (per the J4-512 audit) `hframeK` is used ONLY as `hframeK 0 hK0`, i.e. to extract the 0-jet
  VALUE `g(0) = δ`.  We swap that call for the banked curved-valid
      `DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0`
  which rebuilds BOTH gauge census members from the pointwise RNC jet `{hg0 (value), hdg0 (1-jet),
  hinvF}` — with `hframeK`/`hK0` GONE — leaving `∂²g(0)` free (curved-satisfiable; J4-512's `confMetric`
  witness has `∂²g₀₀(0) = 2 ≠ 0` while satisfying all three).

  DELIVERABLES:
  •  `hDaLimLU_from_labelled_v2_gauge` — R1 (LabelledRethreadV2) with `{hK0, hframeK}` swapped for the
     pointwise value gauge `hg0`, gauge line routed through `gauge_from_pointwise`.
  •  `hDaLimLU_from_hgate_gauge` — R3 with the same `{hK0, hframeK} → hg0` swap, forwarding to the above.
  •  `a1_R6_from_labelled_curved_gauge` ★ — the capstone: a verbatim copy of `a1_R6_from_labelled_curved`
     with the `hframeK` binder REMOVED (the capstone already carried `hg0`), routing `hDa` through
     `hDaLimLU_from_hgate_gauge`.  BOTH flat-only capstone binders (`hraw` via J4-519, `hframeK` here)
     now removed — 2 of 3.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  Removing `hframeK` (+ the already-removed
  `hraw`) makes the capstone curved-SATISFIABLE through those two channels (coefficient-neutral — the
  R/6 lives solely in `transportCoeff`/`htr`, untouched).  It does NOT derive curved `a₁`: the remaining
  pending items (`hBoundaryLim`; the iterE/htr/hGauss curved bridges; a genuine RNC curved witness for
  the full census) stay.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, no existing
  file edited, nothing committed.
-/
import Mathlib
import QIQTH.A1R6FromLabelled
import QIQTH.LabelledRethreadV2
import QIQTH.DaLimCurvedGauge

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.LabelledRethreadV2 QIQTH.A1R6FromLabelled
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromLabelledCurvedGauge

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ###############################################################################
    ### (R1-gauge) — `hDaLimLU_from_labelled_v2_gauge`: R1 with `{hK0, hframeK} → hg0`.
    ############################################################################### -/

/-- **★ (R1-gauge) — `hDaLimLU_from_labelled_v2_gauge`.**  VERBATIM copy of
    `LabelledRethreadV2.hDaLimLU_from_labelled_v2` with the flat-only geometry pair `{hK0, hframeK}`
    (neighbourhood frame `g = δ` on `K`, curved-UNSATISFIABLE) REPLACED by the pointwise RNC value gauge
    `hg0 : g(0) = δ`, and the gauge sub-assembly line
        `obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0`
    routed through the banked curved-valid `DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0`
    (J4-512).  Every other binder + brick is byte-identical.  Same conclusion
    `DaLimLUGoal g gi (vanVleckGatedWitness …) (leviSeries …) U`.  `hg0`/`hinvF`/`hdg0` are
    curved-inhabited (J4-512 `confMetric`), so the antecedent is genuinely curved-satisfiable — no flat
    neighbourhood forced.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_labelled_v2_gauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs (pointwise RNC jet — NO neighbourhood frame `hframeK`):
    (hg0 : ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities:
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ the labelled residual width-3/2 `hEdom` existential (from `HrawPreCollapse`):
    (hEdomEx : ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U := by
  -- (i) gauge — CURVED-VALID: rebuilt from the pointwise RNC jet, `hframeK`/`hK0` GONE.
  obtain ⟨hgi, hΓ⟩ := QIQTH.DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0
  -- (ii) the frozen-side interchange member (from the W2 family) — reused for `hLapFull`.
  have hInter :
      MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    QIQTH.SecondOrderInterchangeConcrete.witness_MemInterchange g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (0 : ℝ) U
      V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
  -- (iii)/(iv) source envelope: width-2 `hFdom`, `hFzero`, and the derived width-2 `hFdomW`.
  obtain ⟨⟨C_L, hCL0, hFdom⟩, hFzero⟩ :=
    source_from_leviData g gi hChr hK S a b T C hn dataLevi
  have hFzero0 : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => hFzero s hs z 0
  have hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ C_L * gaussDdim (2 * s) z := by
    intro s hs hsT z
    have h := hFdom s hs hsT z 0
    rwa [sub_zero] at h
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  -- (v) integrability legs.
  obtain ⟨hIlo, hIhi, hII_lo, hII_hi⟩ :=
    integrability_from_dominations g gi hChr hK S a b U T wA CA wA2 CA2 2 C_L
      hwA hCA hwA2 hCA2 (by norm_num) hCL0 hUpos hUTle hAdomHeat hAdom2 hFdomW hFzero0
      hmeasLo hmeasHi hmeas2Lo hmeas2Hi
  -- (vi) sliver amplitudes.
  obtain ⟨D0, D1, hD0, hD1, hbnd⟩ :=
    sliver_from_ampData g gi hChr hK S a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U T τ₀ aa haa
      dataAmp hau hUTle hεaa hετ₀
  -- (vii) ★ residual width-3/2 domination — DIRECTLY from the labelled `hEdom` existential.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ := hEdomEx
  -- (viii) ★ untruncated interchange (`hLapFull`) from the labelled atomic carrier.
  have hLapFull :
      MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    memLapFull_from_labelled g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      hgi hΓ hInter hII_lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  -- (ix) E-combination.
  have hEcomb :
      MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) :=
    eCombine_from_data g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      hDa hLap hLapZ hEZ hLapS hES
  -- ★★★ thread every discharged binder into the concrete-gate Da-limit.
  exact QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) T U hUopen hn
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aa hE₀ hE₁ hCL0 haa hau hUTle hEdom hFdom hFzero hIlo hIhi hEcomb

/-! ###############################################################################
    ### (R3-gauge) — `hDaLimLU_from_hgate_gauge`: R3 with `{hK0, hframeK} → hg0`.
    ############################################################################### -/

/-- **★★★ (R3-gauge) — `hDaLimLU_from_hgate_gauge`.**  The complete one-theorem `Da`-limit assembly
    with BOTH the flat-only LINEAR `hraw` (already the `hgate` quadratic here) AND the flat-only
    neighbourhood frame `{hK0, hframeK}` removed: the geometry group is the pointwise RNC value gauge
    `hg0` only, threaded through `hDaLimLU_from_labelled_v2_gauge` with the honest width-4/3 QUADRATIC
    carry `hgate` bridged to the width-3/2 `hEdom` existential by `LabelledRethreadV2.
    hEdom_vanVleck_of_hgate`.  Same conclusion.  Curved-satisfiable.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_from_hgate_gauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs (pointwise RNC value gauge — NO neighbourhood frame):
    (hg0 : ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp g gi H_G)`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w)
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities:
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ THE HONEST on-gate width-4/3 QUADRATIC carry (replaces the width-1 LINEAR `hraw` label):
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U :=
  hDaLimLU_from_labelled_v2_gauge g gi hChr hK S a b T U hUopen hn
    hg0 hinvF hdg0
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2
    hmeasLo hmeasHi hmeas2Lo hmeas2Hi
    τ₀ dataAmp hεaa hετ₀
    (QIQTH.LabelledRethreadV2.hEdom_vanVleck_of_hgate g gi hChr hK S a b P hP hgate)
    hPd2conv hDa hLap hLapZ hEZ hLapS hES

/-! ###############################################################################
    ### (CAPSTONE) — `a1_R6_from_labelled_curved_gauge`: hframeK + linear-hraw BOTH removed.
    ############################################################################### -/

/-- **J4-520 — `a1_R6_from_labelled_curved_gauge` — THE hframeK-FREE CURVED FACADE.**  Identical to
    `A1R6FromLabelledCurved.a1_R6_from_labelled_curved` (which already removed the flat-only LINEAR
    `hraw` via the quadratic `hgate`) with the SECOND flat-only binder — the neighbourhood frame
    `hframeK : ∀ q ∈ K, g q = δ` — REMOVED: the capstone already carried the pointwise value gauge
    `hg0 : g(0) = δ`, so `hDa` is routed through `hDaLimLU_from_hgate_gauge` (which rebuilds the gauge
    census from `{hg0, hinvF, hdg0}` via `DaLimCurvedGauge.gauge_from_pointwise`).  Same conclusion (the
    a₁ two-jet at the constant-radius gate).  BOTH flat-only capstone binders now removed (2 of 3);
    `{hg0, hinvF, hdg0}` are curved-inhabited (J4-512 `confMetric`, `∂²g₀₀(0)=2≠0`).  ⚠ NOT `a₁ = R/6`
    (still CONDITIONAL; `hBoundaryLim`, iterE/htr/hGauss curved bridges, and a full RNC curved witness
    remain — see file header). -/
theorem a1_R6_from_labelled_curved_gauge
    -- ═══ SECTION A — base geometry, gate, window, and window parameters (shared everywhere) ═══
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (hn : 1 ≤ n)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ═══ SECTION B — gauge / smoothness (core + `htr_adapter`); `hGauss` is LABELLED ═══
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))  -- ★ LABELLED
    -- ═══ SECTION C — the constant-radius package facts (satisfiable via `constRadius_package_and_S1`) ═══
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
    -- ═══ SECTION D — the geometry-raw gauge facts for `hDaLimLU_from_hgate_gauge` (hframeK REMOVED) ═══
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    -- ═══ SECTION E — the W2 differentiation-under-∫ family (SHARED: labelled-Da AND Duhamel-FULL) ═══
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hFmeas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
            ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) w)
    -- ═══ SECTION F — residual window floor (SHARED: `hDaLimLU_from_hgate_gauge` `aa` + `…_FULL` `aT`) ═══
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u)
    -- ═══ SECTION G — `hDaLimLU_from_hgate_gauge` analytic piles (Levi source, dominations, sliver) ═══
    (CLevi : ℝ) (dataLevi : QIQTH.LeviSeriesLocalData.LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) CLevi T)
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (τ0A : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK (constGate g gi hChr hK c) a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) i T τ0A)  -- ★ hard field = hD2Hexpand (LABELLED)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ0A : ∀ m : ℕ, epsSeq m ≤ τ0A)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))  -- ★ CURVED-VALID quadratic width-4/3 gate carry
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) i y) i 0)))  -- ★ LABELLED
    (hDaEq : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    -- ═══ SECTION H — `truncatedDuhamelCore_AT_GATE_FULL` specific census ═══
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0)))
    (hgiMem : MemGaugeGi (n := n) gi) (hΓMem : MemGaugeGamma (n := n) g gi)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))))
    -- ═══ SECTION I — the F2 / `hDConv` regularity family (SHARED: `…_FULL` AND `a1_R6_slots_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ SECTION J — frozen/moving envelope list (SHARED: `…_FULL` AND `hbdryLU_CONCRETE`) ═══
    (ρ lam CW Cf τ0fr : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ0fr : 0 < τ0fr)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop,
        ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ═══ SECTION K — the `hCConv` sliver census for `a1_R6_slots_AT_GATE` ═══
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK (constGate g gi hChr hK c) a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- ── brick 2: the `htr` binder at `Ric := fun cc d => ricci g gi cc d 0`, from the labelled `hGauss`.
  have htr := htr_adapter g gi hg hgsymm hgiC hgi hdg0 hGauss
  -- ── J4-520: the loc-unif `Da`-limit from the labelled census, at `S := constGate g gi hChr hK c`,
  --    with `hframeK` REMOVED — routed through the pointwise-value-gauge `hDaLimLU_from_hgate_gauge`.
  have hDa :
      DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U :=
    hDaLimLU_from_hgate_gauge g gi hChr hK (constGate g gi hChr hK c) a b T U hUopen hn
      hg0 hinvF hdg0
      V hVopen hV0 snb hsnb hQ1 hFmeas_W2 hFint_W2 hF'meas_W2 bnd hbdd_W2 hbound_W2 hdiff
      aa haa hau hUT
      CLevi dataLevi
      wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2 hmeasLo hmeasHi hmeas2Lo hmeas2Hi
      τ0A dataAmp hεaa hετ0A
      P hP hgate
      hPd2conv
      hDaEq hLap hLapZ hEZ hLapS hES
  -- ── J4-311: the truncated-Duhamel core at the gate, from its FULL concrete census.
  have core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t :=
    truncatedDuhamelCore_AT_GATE_FULL g gi hChr hK (constGate g gi hChr hK c) a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) rfl
      t T hT U hUopen htU hUT hn
      hBoundaryLim
      hgiMem hΓMem V hVopen hV0 snb hsnb hQ1 hFmeas_W2 hFint_W2 hF'meas_W2 bnd hbdd_W2 hbound_W2 hdiff
      hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
      E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb
      A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
      nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
      ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
      hWDom hmass hmassone hmod hsup hUsub
  -- ── J4-310: the W1-free boundary loc-unif slot, from the frozen/moving lists.
  have hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U :=
    hbdryLU_CONCRETE (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
      ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr
      hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub
  -- ── brick 4: the three per-gate analytic slots.
  have slots := a1_R6_slots_AT_GATE g gi hChr hK c a b t T hT U hUopen htU hUpos hUT
    (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) rfl rfl
    core
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    hDa hbdry
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont
  -- ── brick 1: the pre-∃ core, at `Ric := fun cc d => ricci g gi cc d 0`.
  exact wide_a1_R6_core_AT_CONSTRADIUS g gi (fun cc d => ricci g gi cc d 0) t ht hn
    hChr hK hK0 hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    htr hpkgBound hmemS0 hopenS0 hS1
    slots.hDuhamel slots.hDConv slots.hCConv

end QIQTH.A1R6FromLabelledCurvedGauge

/-! ## Axiom check -- the hframeK-free curved facade is std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6FromLabelledCurvedGauge
#print axioms hDaLimLU_from_labelled_v2_gauge
#print axioms hDaLimLU_from_hgate_gauge
#print axioms a1_R6_from_labelled_curved_gauge
end AxiomChecks
