/-
  CurvedA1Leg2Core — J4-550.  The symmetric LEG-2 adapter: wiring the `a₁` two-jet capstone's
  `core : TruncatedDuhamelCore` binder at the genuinely-curved witness `g^K = curvedRNCMetric κ`
  (`κ < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file discharges the geometric-gauge legs of the LEG-2
  Duhamel-core supplier at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`, `S := constGate …` and
  re-exposes LEG 2 (`TruncatedDuhamelCore`) — EXACTLY the `core` binder of
  `CurvedA1Assembled.curved_a1_R6_assembled`.  It feeds J4-547's leg-2 `MemLapFull`
  (`Leg2HLapFull.curved_leg2_hLapFull`) into `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`,
  with:
    • the two gauge binders `hgi`/`hΓ` DISCHARGED via `gauge_from_geometry` (the `MemLapFull`'s own gauge
      is discharged inside `curved_leg2_hLapFull` the same way);
    • the two GLOBAL geometric inputs `hinvF`/`hdg0` DISCHARGED from the curved gauge lemmas
      (`curvedRNCMetric_hinvF`, `curvedRNCMetric_pd_zero`) — the exact mirror of leg-1's J4-549.

  Every analytic domination (leg-2's `hInter`/`hAdomHeat`/CAPPED `hAdom2cap`/`hFdomW`/measurabilities/
  the matched-sliver `hII_hi : MemAdjHi` moment residual/the √ε sliver bundle/`hPd2conv`, and the
  FULL-census `hII_lo`/`hEdom`/`hFdom`/`hIlo`/`hIhi`/`hEcomb`/the F2 pile/the frozen–moving lists/
  `hBoundaryLim`) remains an honest binder.  NONE is the conclusion; NONE is vacuous or `:= True`.

  ⚠  `a₁ = R/6` stays CONDITIONAL.  Wiring leg-2 at `g^K` shrinks the leg-2 gauge surface (removes
  `hgi`/`hΓ`/`hinvF`/`hdg0` as binders) but does NOT make `a₁ = R/6` unconditional: the remaining leg-2
  residuals (the `MemAdjHi`/matched-sliver moment, the convergence trio, the measurability carries) plus
  the Seeley–DeWitt geometric wiring are still owed.  NOT `a₁ = R/6`. -/
import Mathlib
import QIQTH.HDuhamelExportRethread
import QIQTH.Leg2HLapFull
import QIQTH.CurvedA1Assembled
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.GaussGaugeToHgauge

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.GaussGaugeToHgauge
open QIQTH.TruncatedDuhamelData QIQTH.HDuhamelExportRethread
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1Leg2Core

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-550 — `curved_core_at_gate` — LEG 2 wired at the curved witness `g^K`.**  The complete
    `TruncatedDuhamelCore` Duhamel-core output at `g := curvedRNCMetric κ`, `gi := curvedRNCInv κ`,
    `S := constGate …` (`κ < 0`) — EXACTLY the `core` binder of `curved_a1_R6_assembled` — obtained by
    feeding J4-547's leg-2 `MemLapFull` (`curved_leg2_hLapFull`) into `truncatedDuhamelCore_AT_GATE_FULL`.
    The two gauge binders `hgi`/`hΓ` are DISCHARGED via `gauge_from_geometry`; the two global geometric
    inputs `hinvF`/`hdg0` are DISCHARGED from the curved gauge lemmas (`curvedRNCMetric_hinvF`,
    `curvedRNCMetric_pd_zero`).  Every analytic domination, the CAPPED second-derivative family, the
    matched-sliver `MemAdjHi` residual, the FULL-census residuals, the F2 pile, the frozen/moving lists,
    and the convergence carries remain honest binders.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_core_at_gate (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    -- ═══ gauge FROM GEOMETRY raw inputs (feed both the outer `hgi`/`hΓ` and `curved_leg2_hLapFull`) ═══
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, (curvedRNCMetric κ) q i j = (if i = j then (1 : ℝ) else 0))
    -- ═══ LEG-2 numeric parameters (for `curved_leg2_hLapFull`) ═══
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
  -- ── the two gauge census binders, discharged via `gauge_from_geometry`.
  obtain ⟨hgi, hΓ⟩ := gauge_from_geometry (curvedRNCMetric κ) (curvedRNCInv κ) hK0 hframeK hinvF hdg0
  -- ── window positivity, from the residual-domination time floor.
  have hUpos : ∀ u ∈ U, 0 < u := fun u hu => lt_of_lt_of_le haa (hau u hu)
  -- ── LEG-2 `MemLapFull`, from J4-547 (its own gauge discharged from the same geometric inputs).
  have hLapFull := QIQTH.Leg2HLapFull.curved_leg2_hLapFull (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c a b
    U T wA CA wA2 wF CF CA2c hwA hCA hwA2 hCA2c hwF hCF hUpos hUT hK0 hframeK hinvF hdg0
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

/-- **★ J4-550 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The metric underlying the leg-2
    core producer is genuinely curved: for `K ≠ 0` and `n ≥ 2` the diagonal metric-Hessian trace
    (`Ric(0)`) of `g^K = curvedRNCMetric K` is nonzero.  So `curved_core_at_gate` re-exposes the
    capstone's `core` binder inhabited by a genuinely curved metric, NOT the flat `δ`.  NOT `a₁ = R/6`. -/
theorem curved_core_at_gate_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.CurvedA1Leg2Core

section AxiomChecks
open QIQTH.CurvedA1Leg2Core
#print axioms curved_core_at_gate
#print axioms curved_core_at_gate_curved_satisfiable
end AxiomChecks
