/-
  CurvedA1FullyWiredCenter — J4-587.  THE CULMINATING curved-capstone rethread: the CENTER-GAUGE
  variant chain up to `curved_a1_R6_fully_wired_center`, producing a NON-VACUOUS curved a₁=R/6 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  This file RE-ESTABLISHES the curved a₁ two-jet capstone NON-VACUOUSLY (weakened
  center-only gauge, contrast the J4-582 vacuity of the shipped `curved_a1_R6_fully_wired`) — MODULO
  `hmassone` (the ∫z → 1 base-mass limit), which remains a CARRIED analytic input even in the weakened
  capstone.  `a₁ = R/6` was previously established non-vacuously only for the FLAT tower; this brick makes
  the CURVED capstone non-vacuous too — but the coefficient stays CONDITIONAL on the carried residuals.

  ## WHAT THIS FILE DOES.
  J4-582 proved the shipped curved capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` VACUOUS
  at the curved witness: its neighbourhood frame `hframeK : ∀ q ∈ K, curvedRNCMetric κ q = δ` together
  with `hK0 : 0 ∈ K` FORCES `K = {0}` (only the CENTER value of a curved metric is `δ`), collapsing the
  gated source support to a null singleton, hence killing `hmassone` (`hmassone_unsatisfiable`).  J4-583/
  584 certified the fix: weaken `hframeK` to the CENTER-ONLY pointwise value gauge
  `hg0 : ∀ i j, g 0 i j = δ_{ij}` (which `curvedRNCMetric` satisfies via `curvedRNCMetric_zero`, curved or
  flat, WITHOUT collapsing `K`) and route the gauge line through the banked curved-compatible drop-in
  `DaLimCurvedGauge.gauge_from_pointwise` instead of `gauge_from_geometry`.  J4-585/586 built the two leg
  gauge sites' center variants (`hDaLimLU_from_labelled_capped_center`, `curved_leg2_hLapFull_center`).

  This file threads the center gauge UP through the capstone chain:
    • `curved_hDa_at_gate_center`   — LEG 1, `{hK0, hframeK} → hg0`, calling `_center` leg-1;
    • `curved_core_at_gate_center`  — LEG 2, `{hK0, hframeK} → hg0`, calling `_center` leg-2 AND swapping
                                      its OWN `gauge_from_geometry → gauge_from_pointwise` site;
    • `curved_a1_R6_fully_wired_center` — the FULL capstone: `hframeK → hg0` (KEEPING `hK0`, which the
      intermediate `curved_a1_R6_geomWired` genuinely needs and which is harmless / satisfiable), feeding
      the two `_center` legs.  Reuses `curved_a1_R6_geomWired` UNCHANGED (it never consumed `hframeK`).
    • `curved_a1_R6_center_nonvacuous` — THE VACUITY GUARD (anti-J4-582 for the REAL capstone): the
      weakened capstone's antecedent bundle `{hg0, 0 ∈ K, ∃q≠0∈K, gauge members, Ric(0) ≠ 0, ¬hframeK}`
      is JOINTLY SATISFIABLE at a genuinely-curved witness (`κ < 0`, `n ≥ 2`) on a GENUINE `K` (the closed
      unit ball, NOT the J4-582 collapsed `{0}`).  Reuses J4-584's
      `curved_center_antecedents_nonvacuous` and adds the concrete `hg0 = curvedRNCMetric_zero`.

  Every variant's CONCLUSION is IDENTICAL to the original's (the same a₁ two-jet R/6 identity, not
  weakened).  `hg0` is discharged for the concrete curved metric by `curvedRNCMetric_zero`.  NO `hframeK`/
  `hK0`-collapse is reintroduced.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, no
  hypothesis equal to the conclusion, no existing file edited, nothing committed.

  ⚠ HONEST a₁ FRAMING.  `hmassone` (the base-mass ∫z → 1 limit) is STILL a carried analytic input in the
  weakened capstone — the vacuity guard shows the STRUCTURAL obstruction is gone (K is genuine, not `{0}`,
  so `hmassone` is no longer forced to `∫ = 0 ≠ 1`), NOT that `hmassone` is proven.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedA1FullyWired
import QIQTH.CurvedA1Leg2Core
import QIQTH.CurvedA1FullyWiredCapstone
import QIQTH.DaLimLUCappedStep3Center
import QIQTH.Leg2HLapFullCenter
import QIQTH.CurvedA1CenterGauge
import QIQTH.DaLimCurvedGauge
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.GaussGaugeToHgauge
import QIQTH.HDuhamelExportRethread

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2 QIQTH.DaLimLUCappedStep3
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.GaussGaugeToHgauge
open QIQTH.TruncatedDuhamelData QIQTH.HDuhamelExportRethread
open QIQTH.HEmeasRecon QIQTH.CConvV2DerivRep QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.NCRiemannTwoJet
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.A1R6FromLabelled QIQTH.CurvedRNCPosDef QIQTH.CurvedA1Assembled
open QIQTH.CurvedA1FullyWired QIQTH.CurvedA1Leg2Core QIQTH.CurvedA1FullyWiredCapstone
open QIQTH.DaLimLUCappedStep3Center QIQTH.Leg2HLapFullCenter QIQTH.CurvedA1CenterGauge
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CurvedA1FullyWiredCenter

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **★★★ J4-587 — `curved_hDa_at_gate_center` — LEG 1, center-gauge variant.**  IDENTICAL conclusion to
    `CurvedA1FullyWired.curved_hDa_at_gate` (the complete `DaLimLUGoal` Da-limit output at the curved
    witness `g^K`) except the two geometry binders `{hK0, hframeK}` are REPLACED by the single center-only
    pointwise value gauge `hg0 : ∀ i j, g^K 0 i j = δ`, and the leg-1 capstone call is routed through
    `DaLimLUCappedStep3Center.hDaLimLU_from_labelled_capped_center` (J4-585, which uses
    `gauge_from_pointwise`) instead of `hDaLimLU_from_labelled_capped`.  `hg0` is satisfied by
    `curvedRNCMetric` via `curvedRNCMetric_zero`, so the J4-582 `K = {0}` vacuity is removed.  ⚠ NOT
    `a₁ = R/6`. -/
theorem curved_hDa_at_gate_center (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw input (★ CENTER-ONLY value gauge `hg0`, no `hK0`/`hframeK`):
    (hg0 : ∀ i j, (curvedRNCMetric κ) (0 : Point n) i j = (if i = j then (1 : ℝ) else 0))
    -- (ii) the W2 differentiation-under-∫ family (at `F := leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) H_G)`):
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
    -- (iii) the residual-domination time floor / window:
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUTle : ∀ u ∈ U, u ≤ T)
    -- (iv) the Levi source envelope package:
    (C : ℝ) (dataLevi : LeviSeriesLocalData
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) C T)
    -- (v) the integrability Gaussian dominations + measurabilities (★ CAPPED: `hAdom2cap` + residual):
    (wA CA wA2 : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
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
    -- (v-residual) ★ THE MATCHED-SLIVER HI-LEG RESIDUAL — CARRIED, NOT from any pointwise domination:
    (hII_hi_res : MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    -- (vi) the √ε sliver amplitude bundle:
    (τ₀ : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
        (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) i T τ₀)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    -- (vii) ★ the labelled residual gated raw bound:
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : GlobalGatedRawBound (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) P)
    -- (viii) ★ the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) u x 0) i y) i 0)))
    -- (ix) the E-combination carries:
    (hDa : ∀ (m : ℕ) (u : ℝ),
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
        volume 0 (u - epsSeq m)) :
    DaLimLUGoal (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
      (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U :=
  QIQTH.DaLimLUCappedStep3Center.hDaLimLU_from_labelled_capped_center (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUopen hn
    hg0
    (fun y c d => curvedRNCMetric_hinvF κ (le_of_lt hκ) y c d)
    (fun c d e => curvedRNCMetric_pd_zero κ c d e)
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2c hwA hCA hwA2 hCA2c hAdomHeat hAdom2cap hmeasLo hmeasHi hmeas2Lo
    hII_hi_res τ₀ dataAmp hεaa hετ₀ P hP hraw hPd2conv
    hDa hLap hLapZ hEZ hLapS hES

/-- **★★★ J4-587 — `curved_core_at_gate_center` — LEG 2, center-gauge variant.**  IDENTICAL conclusion to
    `CurvedA1Leg2Core.curved_core_at_gate` (the complete `TruncatedDuhamelCore` at the curved witness
    `g^K`) except the two geometry binders `{hK0, hframeK}` are REPLACED by the single center-only value
    gauge `hg0 : ∀ i j, g^K 0 i j = δ`.  BOTH gauge sites are swapped: the leg's OWN `gauge_from_geometry`
    → `DaLimCurvedGauge.gauge_from_pointwise`, AND the leg-2 `MemLapFull` supplier
    `curved_leg2_hLapFull` → `Leg2HLapFullCenter.curved_leg2_hLapFull_center` (J4-586).  `hg0` is satisfied
    by `curvedRNCMetric` via `curvedRNCMetric_zero`, so the J4-582 `K = {0}` vacuity is removed.  ⚠ NOT
    `a₁ = R/6`. -/
theorem curved_core_at_gate_center (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ═══ gauge FROM CENTER-ONLY VALUE (★ replaces `{hK0, hframeK}`; feeds both the outer gauge and leg-2) ═══
    (hg0 : ∀ i j, (curvedRNCMetric κ) (0 : Point n) i j = (if i = j then (1 : ℝ) else 0))
    -- ═══ LEG-2 numeric parameters (for `curved_leg2_hLapFull_center`) ═══
    (wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    -- ═══ LEG-2 analytic residuals (frozen-side interchange + strip/LO dominations + Pd2 carrier) ═══
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
    -- ═══ SHARED (leg-2 ∧ FULL): the matched-sliver `MemAdjHi` residual + the √ε sliver amplitude bundle ═══
    (hII_hi : MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- ═══ FULL-only: the W1-free boundary slot ═══
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) t 0 0)))
    -- ═══ FULL-only: the W2 differentiation-under-∫ family ═══
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
    -- ═══ FULL-only: the LO adjacency member + Gaussian dominations + strip integrabilities + E-combine ═══
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
    -- ═══ FULL-only: the F2 regularity pile + hFII tail-integrability pile (for `hDerivConv_AT_GATE`) ═══
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
    -- ═══ FULL-only: the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ═══
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
    (hUsub : U ⊆ Set.Icc ta tb) :
    TruncatedDuhamelCore (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b) t := by
  -- ── the two global geometric inputs, discharged from the curved gauge lemmas (mirror of J4-549).
  have hinvF := fun (y : Point n) (c d : Fin n) => curvedRNCMetric_hinvF κ (le_of_lt hκ) y c d
  have hdg0 := fun (c d e : Fin n) => curvedRNCMetric_pd_zero κ (n := n) c d e
  -- ── the two gauge census binders, discharged via `gauge_from_pointwise` (★ CENTER-ONLY, no `hframeK`).
  obtain ⟨hgi, hΓ⟩ := QIQTH.DaLimCurvedGauge.gauge_from_pointwise (curvedRNCMetric κ) (curvedRNCInv κ) hg0 hinvF hdg0
  -- ── window positivity, from the residual-domination time floor.
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  -- ── LEG-2 `MemLapFull`, from J4-586's CENTER variant (its own gauge from `gauge_from_pointwise`).
  have hLapFull := QIQTH.Leg2HLapFullCenter.curved_leg2_hLapFull_center (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c a b
    U T wA CA wA2 wF CF CA2c hwA hCA hwA2 hCA2c hwF hCF hUpos hUT hg0 hinvF hdg0
    hInter hAdomHeat hAdom2cap hFdomW (fun s hs z => hFzero s hs z 0)
    hmeasLo hmeasHi hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  -- ── the truncated-Duhamel core at the gate, from its FULL concrete census.
  exact truncatedDuhamelCore_AT_GATE_FULL (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
    (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) rfl
    t T hT U hUopen htU hUT hn
    hBoundaryLim
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub

/-- **★★★ J4-587 — `curved_a1_R6_fully_wired_center` — THE FULLY-WIRED curved a₁ TWO-JET CAPSTONE at
    `g^K`, NON-VACUOUS.**  IDENTICAL conclusion to `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`
    (the a₁ two-jet R/6 identity, coefficient `(∑_i ricci … i i 0)/6 = n(n−1)κ/6 ≠ 0`) except the
    neighbourhood frame `hframeK` is REPLACED by the center-only value gauge `hg0 : ∀ i j, g^K 0 i j = δ`.
    `hK0 : 0 ∈ K` is KEPT (the intermediate `curved_a1_R6_geomWired` genuinely needs it, and it is harmless
    / satisfiable — it does NOT force the collapse; only `hframeK` did).  LEG 1 `hDa` is fed by
    `curved_hDa_at_gate_center`, LEG 2 `core` by `curved_core_at_gate_center` (both center variants); the
    intermediate `curved_a1_R6_geomWired` is REUSED UNCHANGED (it never consumed `hframeK`).  `hg0` is
    satisfied by `curvedRNCMetric` via `curvedRNCMetric_zero` — see the vacuity guard
    `curved_a1_R6_center_nonvacuous`; the J4-582 `K = {0}` vacuity is removed.  ⚠ `a₁ = R/6` stays
    CONDITIONAL (the carried analytic residuals, incl. `hmassone`, are still owed).  NOT `a₁ = R/6`. -/
theorem curved_a1_R6_fully_wired_center (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ═══ gauge: `hK0` KEPT (geomWired needs it), `hframeK` REPLACED by center-only `hg0` ═══
    (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, (curvedRNCMetric κ) (0 : Point n) i j = (if i = j then (1 : ℝ) else 0))
    -- ═══ LEG-2 numeric parameters (for `curved_leg2_hLapFull_center`) ═══
    (wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    -- ═══ LEG-2 analytic residuals (frozen-side interchange + strip/LO dominations + Pd2 carrier) ═══
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
    -- ═══ SHARED (leg-2 ∧ FULL): the matched-sliver `MemAdjHi` residual + the √ε sliver amplitude bundle ═══
    (hII_hi : MemAdjHi (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- ═══ FULL-only: the W1-free boundary slot ═══
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) t 0 0)))
    -- ═══ FULL-only: the W2 differentiation-under-∫ family ═══
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
    -- ═══ FULL-only: the LO adjacency member + Gaussian dominations + strip integrabilities + E-combine ═══
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
    -- ═══ FULL-only: the F2 regularity pile + hFII tail-integrability pile (for `hDerivConv_AT_GATE`) ═══
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
    -- ═══ FULL-only: the frozen/moving satisfiable lists (for `hbdryLU_CONCRETE`) ═══
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
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
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
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  refine curved_a1_R6_geomWired κ hκ hChr hK hK0 t T ht hT hn U hUopen htU hUpos hUT a b c C ha hab hbc hCnn hsrc hpkgBound hmemS0 hopenS0 hS1 ?_ ?_ hbdry
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb hbulkderiv hbulk_tendsto hsliver hcont
  · exact curved_hDa_at_gate_center κ hκ hChr hK a b c T U hUopen hn hg0 V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff aa haa hau hUT CLevi dataLevi wA CA wA2 CA2c hwA hCA hwA2 hCA2c hAdomHeat hAdom2cap hmeasLo hmeasHi hmeas2Lo hII_hi τ₀ dataAmp hεaa hετ₀ P hP hraw hPd2conv hDa_ec hLap hLapZ hEZ hLapS hES
  · exact curved_core_at_gate_center κ hκ hChr hK a b c t T hT U hUopen htU hUT hn hg0 wA CA wA2 wF CF CA2c hwA hCA hwA2 hCA2c hwF hCF hInter hAdomHeat hAdom2cap hFdomW hmeasLo hmeasHi hmeas2Lo hPd2conv hII_hi D0 D1 hD0 hD1 hbnd hBoundaryLim V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff hII_lo E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub

/-- **★★★ J4-587 — `curved_a1_R6_center_nonvacuous` — THE VACUITY GUARD (anti-J4-582 for the REAL
    capstone).**  The WEAKENED (center-only gauge) fully-wired capstone
    `curved_a1_R6_fully_wired_center`'s geometry antecedent bundle
      `{ hg0 : ∀ i j, g^K 0 i j = δ,  hK0 : 0 ∈ K,  ∃q∈K, q≠0,  MemGaugeGi ∧ MemGaugeGamma,  Ric(0) ≠ 0,
         ¬(∀q∈K, g^K q = δ) }`
    is JOINTLY SATISFIABLE at a genuinely-curved witness (`κ < 0`, `n ≥ 2`) on a GENUINE compact `K` (the
    closed unit ball, which CONTAINS a nonzero point — NOT the J4-582 collapsed `{0}`).  Reuses J4-584's
    `CurvedA1CenterGauge.curved_center_antecedents_nonvacuous` and adds the concrete center gauge
    `hg0 = curvedRNCMetric_zero`.  Contrast `CurvedA1FarConsumeCheck.hmassone_unsatisfiable`: there the
    shipped `{hframeK, hK0}` FORCED `K = {0}` and killed `hmassone`; here the weakened center-only gauge
    places NO constraint on `K`, so a genuine `K` (positive-measure source support) is admissible and the
    structural collapse is GONE.

    ⚠ HONEST SCOPE.  This certifies the STRUCTURAL obstruction (the `K = {0}` collapse) is removed — `K` is
    genuine, so `hmassone` is no longer forced to `∫ = 0 ≠ 1`.  It does NOT prove `hmassone` (the ∫z → 1
    base-mass limit), which remains a CARRIED analytic input of `curved_a1_R6_fully_wired_center`.  So
    `a₁ = R/6` stays CONDITIONAL even in the weakened capstone.  NOT `a₁ = R/6`. -/
theorem curved_a1_R6_center_nonvacuous (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) (c : Fin n) :
    ∃ K : Set (Point n),
      IsCompact K
      ∧ (0 : Point n) ∈ K
      ∧ (∃ q, q ∈ K ∧ q ≠ (0 : Point n))
      -- the concrete center gauge `hg0` that `curved_a1_R6_fully_wired_center` binds:
      ∧ (∀ i j, curvedRNCMetric κ (0 : Point n) i j = (if i = j then (1 : ℝ) else 0))
      -- the two gauge census members it derives from `hg0`:
      ∧ (MemGaugeGi (n := n) (curvedRNCInv κ)
          ∧ MemGaugeGamma (n := n) (curvedRNCMetric κ) (curvedRNCInv κ))
      -- genuinely curved: the `Ric(0)` proxy (diagonal metric-Hessian trace) ≠ 0:
      ∧ pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0
      -- the over-strong flat frame `hframeK` PROVABLY FAILS on this genuine `K` (not the J4-582 collapse):
      ∧ ¬ (∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) := by
  obtain ⟨K, hKc, hK0, hgenuine, hgauge, hRic, hframeFails⟩ :=
    QIQTH.CurvedA1CenterGauge.curved_center_antecedents_nonvacuous κ hκ hn c
  exact ⟨K, hKc, hK0, hgenuine, fun i j => curvedRNCMetric_zero κ i j, hgauge, hRic, hframeFails⟩

end QIQTH.CurvedA1FullyWiredCenter

section AxiomChecks
open QIQTH.CurvedA1FullyWiredCenter
#print axioms curved_hDa_at_gate_center
#print axioms curved_core_at_gate_center
#print axioms curved_a1_R6_fully_wired_center
#print axioms curved_a1_R6_center_nonvacuous
end AxiomChecks
