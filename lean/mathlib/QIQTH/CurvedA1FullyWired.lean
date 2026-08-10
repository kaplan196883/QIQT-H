/-
  CurvedA1FullyWired — J4-549.  Wiring the a₁ two-jet capstone legs at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`).

  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file discharges the geometric-gauge legs of the capstone
  suppliers at the curved metric and re-exposes LEG 1 (`DaLimLUGoal`) / LEG 2 (`TruncatedDuhamelCore`)
  at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`, `S := constGate …`.  Every analytic domination,
  the matched-sliver `MemAdjHi` moment residual, the convergence trio, the SDW wiring, and the
  measurability/window carries all remain honest binders.  `a₁ = R/6` stays CONDITIONAL.
-/
import Mathlib
import QIQTH.DaLimLUCappedStep3
import QIQTH.Leg2HLapFull
import QIQTH.CurvedA1Assembled
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2 QIQTH.DaLimLUCappedStep3
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.GaussGaugeToHgauge
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FullyWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-549 — `curved_hDa_at_gate` — LEG 1 wired at the curved witness `g^K`.**  The complete
    `DaLimLUGoal` Da-limit output at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
    `S := constGate …` (`κ < 0`), obtained from `DaLimLUCappedStep3.hDaLimLU_from_labelled_capped`
    (J4-541) with the two GLOBAL gauge inputs (`hinvF`, `hdg0`) DISCHARGED from the curved gauge lemmas
    (`curvedRNCMetric_hinvF`, `curvedRNCMetric_pd_zero`).  Every analytic domination, the CAPPED
    second-derivative family, the matched-sliver `MemAdjHi` residual, and the convergence carries remain
    honest binders.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hDa_at_gate (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (hn : 1 ≤ n)
    -- (i) geometry / gauge raw inputs:
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, (curvedRNCMetric κ) q i j = (if i = j then (1 : ℝ) else 0))
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
  hDaLimLU_from_labelled_capped (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b T U hUopen hn
    hK0 hframeK
    (fun y c d => curvedRNCMetric_hinvF κ (le_of_lt hκ) y c d)
    (fun c d e => curvedRNCMetric_pd_zero κ c d e)
    V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    aa haa hau hUTle C dataLevi
    wA CA wA2 CA2c hwA hCA hwA2 hCA2c hAdomHeat hAdom2cap hmeasLo hmeasHi hmeas2Lo
    hII_hi_res τ₀ dataAmp hεaa hετ₀ P hP hraw hPd2conv
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.CurvedA1FullyWired

section AxiomChecks
open QIQTH.CurvedA1FullyWired
#print axioms curved_hDa_at_gate
end AxiomChecks
