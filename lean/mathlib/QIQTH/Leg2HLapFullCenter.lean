/-
  Leg2HLapFullCenter — J4-586.  The CENTER-GAUGE VARIANT of the CURVED LEG-2 external `hLapFull`
  producer `Leg2HLapFull.curved_leg2_hLapFull` (J4-547).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is step 2
  of applying the certified center-only-gauge fix (J4-583/584) that re-establishes the CURVED a₁=R/6
  chain NON-VACUOUSLY (step 1 = leg-1's `DaLimLUCappedStep3Center.hDaLimLU_from_labelled_capped_center`,
  J4-585).  `a₁ = R/6` remains established non-vacuously only for the FLAT tower until the full rethread
  (both legs + up through the curved capstone) lands.

  ## WHAT THIS FILE DOES.
  The original leg-2 producer `curved_leg2_hLapFull` carries the two geometry binders
      `(hK0 : 0 ∈ K)` and `(hframeK : ∀ q ∈ K, ∀ i j, g q i j = δ_{ij})`
  used at EXACTLY ONE site — the gauge sub-assembly `gauge_from_geometry g gi hK0 hframeK hinvF hdg0`
  (body line ~151), whose ONLY downstream products are the two gauge census members `hgi`/`hΓ`
  (`MemGaugeGi gi`, `MemGaugeGamma g gi`).  `hframeK` is a NEIGHBOURHOOD frame — for a curved metric it
  forces `K = {0}` (via `curvedRNCMetric_zero` only the CENTER value holds), which makes the mass-one
  gate unsatisfiable ⟹ VACUITY (J4-582).

  This variant REPLACES `{hK0, hframeK}` by the single CENTER-ONLY pointwise value gauge
      `(hg0 : ∀ i j, g 0 i j = if i = j then 1 else 0)`
  and routes the gauge line through the banked curved-compatible drop-in
  `DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0`, which produces the IDENTICAL two gauge
  census members (`MemGaugeGi gi ∧ MemGaugeGamma g gi`) from the 0-jet value + 1-jet only — WITHOUT
  `hframeK`, WITHOUT collapsing `K`.  `curvedRNCMetric κ` satisfies `hg0` via `curvedRNCMetric_zero`, so
  the antecedent is genuinely curved-satisfiable and the vacuity is removed.  `K`/`hK` are RETAINED (the
  gated witness `vanVleckGatedWitness g gi hChr hK S a b` uses them pervasively); only `hK0`/`hframeK`
  are dropped.

  The CONCLUSION is IDENTICAL to the original `curved_leg2_hLapFull`: the SAME `MemLapFull` object at the
  SAME constant-radius flow-ball gate `S := constGate g gi hChr hK c`.  Every other binder (the frozen
  interchange member `hInter`, the width-`wA` heat Gaussian bound `hAdomHeat`, the per-`m` CAPPED
  second-`x`-derivative family `hAdom2cap`, the Levi source envelope `hFdomW`/`hFzero`, the census
  measurabilities, the MATCHED-SLIVER HI-leg residual `hII_hi : MemAdjHi`, the √ε sliver bundle, the
  atomic interchange carrier `hPd2conv`) is verbatim the original.  The proof body differs from the
  original in ONE line (the gauge call).  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis,
  no hypothesis equal to the conclusion, no existing file edited, nothing committed.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUCappedStep2
import QIQTH.GlobalRawBoundFacade
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.A1R6CoreAtGate
import QIQTH.DaLimCurvedGauge

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2
open QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Interval Topology BigOperators

namespace QIQTH.Leg2HLapFullCenter

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-586 — `curved_leg2_hLapFull_center`.**  THE CENTER-GAUGE variant of the curved leg-2
    external `hLapFull` producer `Leg2HLapFull.curved_leg2_hLapFull`: the full capped-census `MemLapFull`
    binder at the constant-radius flow-ball gate `S := constGate g gi hChr hK c` — EXACTLY the leg-2
    (Duhamel-core) `hLapFull` binder the curved `a₁` two-jet capstones consume.  IDENTICAL to
    `curved_leg2_hLapFull` except the two geometry binders `{hK0, hframeK}` are REPLACED by the single
    center-only pointwise value gauge `hg0 : ∀ i j, g 0 i j = δ_{ij}` and the gauge line is routed through
    the curved-compatible `DaLimCurvedGauge.gauge_from_pointwise` instead of `gauge_from_geometry`.  `hg0`
    is satisfied by `curvedRNCMetric` via `curvedRNCMetric_zero` (no `K = {0}` collapse), so the
    antecedent is curved-satisfiable and the J4-582 vacuity is removed.  The conclusion is the SAME
    `MemLapFull`, not weakened.  NOT `a₁ = R/6`. -/
theorem curved_leg2_hLapFull_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (a b : ℝ)
    (U : Set ℝ) (T wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- gauge FROM POINTWISE CENTER VALUE (★ replaces the `hK0`/`hframeK` binders of J4-547):
    (hg0 : ∀ i j, g (0 : Point n) i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- the frozen-side interchange member (from the W2 family):
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    -- (strip legs) the uncapped heat-operator Gaussian bound (no `τ⁻¹` blow-up):
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    -- (LO leg) the PER-`m` CAPPED second-derivative family — NO uncapped whole-time `hAdom2`:
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z|
          ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0 = 0)
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
    -- (HI leg) ★ THE MATCHED-SLIVER RESIDUAL — CARRIED, NOT from any pointwise 2nd-derivative domination:
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    -- the √ε sliver amplitude bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z) := by
  -- gauge from POINTWISE CENTER VALUE (★ curved-compatible drop-in, no `hframeK`/`hK0`).
  obtain ⟨hgi, hΓ⟩ := QIQTH.DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0
  -- thread into J4-540's capped `MemLapFull` producer at `S := constGate g gi hChr hK c`.
  exact memLapFull_from_labelled_capped g gi hChr hK (constGate g gi hChr hK c) a b U T wA CA wA2 wF CF CA2c
    hwA hCA hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter hAdomHeat hAdom2cap hFdomW hFzero
    hmeasLo hmeasHi hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv

end QIQTH.Leg2HLapFullCenter

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.Leg2HLapFullCenter.curved_leg2_hLapFull_center
