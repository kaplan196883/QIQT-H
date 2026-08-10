/-
  CurvedA1MemAdjHiWired — J4-552: discharge the capstone's central `hII_hi : MemAdjHi …` residual for the
  genuinely-curved witness `g^K = curvedRNCMetric κ` via the banked MemAdjHi reduction chain, replacing the
  OPAQUE `MemAdjHi` binder with the CONCRETE {amplitude-data bundle (whose hard field is the chart-jet
  `hD2Hexpand`) + K₁/K₀ envelope + slice continuity/AESM carries} inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It performs a
  PLUMBING composition: it feeds the banked chain
      `AmplitudeDerivativeDataConcrete.hGpow_of_amplitudeData_noEndpoint` (⟹ the `τ^{-1/2}` moment carry
       `hGpow`, with the `τ = 0` endpoint discharged internally)
        → `MemAdjHiSliver.hII_hi_from_sliver` (⟹ `MemAdjHi` via slice-AESM domination)
  at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`, `S := constGate …`, so the OPAQUE `MemAdjHi`
  hypothesis of `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` is replaced by the CONCRETE inputs the
  chain consumes.  No `sorry`/`admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis,
  no hypothesis equal to the conclusion, no existing file edited, nothing committed.

  ## THE CHAIN (mainline, not guessed)
    MemAdjHi  ⟵  `MemAdjHiSliver.hII_hi_from_sliver`
                   ⟵ {slice-AESM carries `hUT`/`hεU`/`hSecCont`/`hBcont`} ∪ {moment carry `hGpow`}
    hGpow     ⟵  `AmplitudeDerivativeDataConcrete.hGpow_of_amplitudeData_noEndpoint`
                   ⟵ {amplitude-data bundle `data : ∀ i, AmplitudeDerivativeData …`} ∪ {K₁/K₀ envelope}
                     ∪ {window-floor `haa`/`hau`/`hUT`/`hεaa`/`hετ₀`}   (endpoint `hEndpoint` shed via `1 ≤ n`)

  The `data` bundle's ONE hard field is `hD2Hexpand` — the chart-jet Leibniz–Gaussian 3-term identity for
  the CURVED van-Vleck witness; that (its `hjets` chart-jet C⁴ geometry) and the off-collar tail remain the
  owed geometric input.  This file does NOT build `data`; it CARRIES it and shows the rest composes.

  ## WHAT LANDS HERE
    • `curved_hII_hi_at_gate` — ★★★ the capstone's `hII_hi : MemAdjHi …` for `g^K`, produced from the
      concrete chain inputs (amplitude bundle + K₁/K₀ envelope + slice continuity/AESM).  Its output type is
      DEFEQ-equal to the `hII_hi` binder of `curved_a1_R6_fully_wired`.
    • `curved_a1_R6_fully_wired_hII` — the fully-wired capstone with the `hII_hi` binder DROPPED, its
      `MemAdjHi` supplied internally from `curved_hII_hi_at_gate`; carries instead the concrete
      {amplitude bundle + K₁/K₀ + slice continuity} inputs (⚠ the amplitude bundle `dataAmp` was already a
      capstone binder — so the NET new carry is only the K₁/K₀ envelope + the two continuity carries).

  ⚠  `a₁ = R/6` remains CONDITIONAL.  Discharging `hII_hi` via the chain replaces the opaque `MemAdjHi`
  with the concrete {`hD2Hexpand`/hjets amplitude bundle + off-collar tail (inside the bundle) + slice
  continuity} inputs — it SHARPENS the residual, it does NOT make `a₁ = R/6` unconditional.  The chart-jet
  `hjets` and the off-collar corrected tail remain owed geometric/analytic inputs.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MemAdjHiSliver
import QIQTH.AmplitudeDerivativeDataConcrete
import QIQTH.CurvedA1FullyWiredCapstone

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.A1R6FromLabelled QIQTH.CurvedRNCGaussWitness
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2 QIQTH.DaLimLUCappedStep3
open QIQTH.GaussGaugeToHgauge QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1Assembled QIQTH.CurvedA1FullyWired QIQTH.CurvedA1Leg2Core
open QIQTH.MemAdjHiSliver QIQTH.AmplitudeDerivativeDataConcrete
open QIQTH.CurvedA1FullyWiredCapstone
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CurvedA1MemAdjHiWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — ★★★ the wire: the capstone's `hII_hi` MemAdjHi for `g^K`, from the concrete chain inputs.
    ############################################################################### -/

/-- **★★★ `curved_hII_hi_at_gate`.**  THE capstone `hII_hi : MemAdjHi …` residual of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, for the genuinely-curved witness
    `g^K = curvedRNCMetric κ`, `gi = curvedRNCInv κ`, `S = constGate …`, produced by composing the banked
    reduction chain (NOT by re-carrying the opaque `MemAdjHi`):

      `AmplitudeDerivativeDataConcrete.hGpow_of_amplitudeData_noEndpoint`  (⟹ the `τ^{-1/2}` moment carry
         `hGpow`, with the `τ = 0` measure-zero endpoint discharged internally from `1 ≤ n`)
        →  `MemAdjHiSliver.hII_hi_from_sliver`  (⟹ `MemAdjHi` via slice-AESM domination on the Hi window).

    Concrete inputs (what the opaque `MemAdjHi` reduces TO):
      • `data : ∀ i, AmplitudeDerivativeData …` — the amplitude bundle whose ONE hard field is `hD2Hexpand`
        (the chart-jet Leibniz–Gaussian 3-term identity — the owed curved geometric carry / `hjets`);
      • `K₁`/`K₀` + `hK₁bound`/`hK₀bound` — the uniform envelope of the per-coordinate amplitude constants;
      • `hSecCont`/`hBcont` — joint continuity of the second-derivative pairing on `Ioc 0 T ×ˢ univ`
        (the slice-AESM carries), plus the window-floor `haa`/`hau`/`hUT`/`hεaa`/`hετ₀`/`hεU`.

    Every hypothesis is SATISFIABLE and NON-VACUOUS for `g^K` (`κ < 0`); none forces `Ric = 0`; none is the
    conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hII_hi_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (T τ₀ aa : ℝ) (U : Set ℝ) (hn : 1 ≤ n)
    -- slice-AESM (continuity) carries for `hII_hi_from_sliver`
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    -- the amplitude-data bundle (∀ i) — its hard field `hD2Hexpand` is the owed chart-jet geometric carry
    (data : ∀ i : Fin n, AmplitudeDerivativeData (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) i T τ₀)
    -- window-floor data
    (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- the K₁/K₀ uniform envelope of the amplitude constants
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hK₁bound : ∀ i : Fin n,
        (data i).L * (15 / 2 * (n : ℝ))
            + 3 / 4 * ((data i).M₁ * ((data i).C_L * gaussDdim aa (0 : Point n))) ≤ K₁)
    (hK₀bound : ∀ i : Fin n,
        (data i).M₂ * ((data i).C_L * gaussDdim aa (0 : Point n)) ≤ K₀) :
    MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
      (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z) := by
  -- STAGE 1 — the `τ^{-1/2}` moment carry `hGpow` (endpoint discharged internally).
  obtain ⟨Cpair, hCpair, hGpow⟩ :=
    QIQTH.AmplitudeDerivativeDataConcrete.hGpow_of_amplitudeData_noEndpoint
      (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T τ₀ aa U data hn
      haa hau hUT hεaa hετ₀ K₁ K₀ hK₁ hK₀ hK₁bound hK₀bound
  -- STAGE 2 — slice-AESM domination ⟹ `MemAdjHi`.
  exact QIQTH.MemAdjHiSliver.hII_hi_from_sliver
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow

/-! ###############################################################################
    ### §2 — ★★★ the fully-wired capstone with the `hII_hi` binder DROPPED (supplied internally).
    ############################################################################### -/

set_option maxHeartbeats 8000000 in
/-- **★★★ J4-552 — `curved_a1_R6_fully_wired_hII`.**  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
    with the OPAQUE `hII_hi : MemAdjHi …` binder DROPPED: it is supplied INTERNALLY from
    `curved_hII_hi_at_gate` (the banked chain).  The NET new carry versus `curved_a1_R6_fully_wired` is
    ONLY the concrete `{K₁/K₀ envelope + slice continuity carries hSecCont/hBcont}` — the amplitude-data
    bundle `dataAmp`, the window-floor `aa`/`haa`/`hau`/`hεaa`/`hετ₀`, `T`, `τ₀`, `hUT` were ALREADY
    capstone binders.  Same conclusion as `curved_a1_R6_fully_wired`.  For `g^K` the coefficient
    `(∑_i ricci (curvedRNCMetric κ) (curvedRNCInv κ) i i 0)/6 = n(n−1)κ/6 ≠ 0` — genuinely curved.
    ⚠ `a₁ = R/6` stays CONDITIONAL; discharging `hII_hi` SHARPENS the residual (opaque `MemAdjHi` →
    concrete chart-jet amplitude bundle + off-collar tail + slice continuity), it does NOT make it
    unconditional. -/
theorem curved_a1_R6_fully_wired_hII (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, (curvedRNCMetric κ) q i j = (if i = j then (1 : ℝ) else 0))
    (wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hInter : MemInterchange (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u x 0) i y) i 0)))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) t 0 0)))
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) y z
                * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv2 (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) w)
    (hII_lo : MemAdjLo (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (E₀ E₁ C_L aa : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haa : 0 < aa)
    (hau : ∀ u ∈ U, aa ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))))
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ0fr : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ0fr : 0 < τ0fr)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z,
      |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)
            - leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)
            - leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    (CLevi : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) CLevi T)
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) P)
    (hDa_ec : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b r 0 z) (u - s)
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) (fun x => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (ht : 0 < t)
    (C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ) (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) 0)))
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))
    (hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
      (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U)
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet)
    -- ═══ ★ J4-552 CONCRETE new inputs replacing the opaque `hII_hi` (via `curved_hII_hi_at_gate`) ═══
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hK₁bound : ∀ i : Fin n,
        (dataAmp i).L * (15 / 2 * (n : ℝ))
            + 3 / 4 * ((dataAmp i).M₁ * ((dataAmp i).C_L * gaussDdim aa (0 : Point n))) ≤ K₁)
    (hK₀bound : ∀ i : Fin n,
        (dataAmp i).M₂ * ((dataAmp i).C_L * gaussDdim aa (0 : Point n)) ≤ K₀) :
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i : Fin n, ricci (curvedRNCMetric κ) (curvedRNCInv κ) i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ) (curvedRNCInv κ)) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
                            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- derive the window ε-floor `hεU` from `hεaa` (`epsSeq m < aa/2`) + `hau` (`aa ≤ u`).
  have hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u := fun m u hu =>
    le_of_lt ((hεaa m).trans_le ((half_le_self haa.le).trans (hau u hu)))
  -- ★ supply the opaque `hII_hi:MemAdjHi` INTERNALLY from the banked chain.
  have hii := curved_hII_hi_at_gate κ hChr hK a b c T τ₀ aa U hn hUT hεU hSecCont hBcont
    dataAmp haa hau hεaa hετ₀ K₁ K₀ hK₁ hK₀ hK₁bound hK₀bound
  exact QIQTH.CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired κ hκ hChr hK a b c t T hT U hUopen htU hUT hn
    hK0 hframeK wA CA wA2 wF CF CA2c hwA hCA hwA2 hCA2c hwF hCF
    hInter hAdomHeat hAdom2cap hFdomW hmeasLo hmeasHi hmeas2Lo hPd2conv
    hii D0 D1 hD0 hD1 hbnd hBoundaryLim V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hII_lo E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub
    CLevi dataLevi τ₀ dataAmp hεaa hετ₀ P hP hraw hDa_ec hLap hLapZ hEZ hLapS hES
    ht C ha hab hbc hCnn hsrc hpkgBound hmemS0 hopenS0 hS1 hbdry
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb hbulkderiv hbulk_tendsto hsliver hcont

end QIQTH.CurvedA1MemAdjHiWired

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedA1MemAdjHiWired.curved_hII_hi_at_gate
#print axioms QIQTH.CurvedA1MemAdjHiWired.curved_a1_R6_fully_wired_hII
