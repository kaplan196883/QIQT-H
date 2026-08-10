/-
  DaLimLUCappedStep2 — J4-540.  The LEG-1 (Da-limit) LO-CAPPED **`MemLapFull`** splice — one step past
  J4-539's `integrability_from_dominations_capped`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It advances
  the LEG-1 capped chain by exactly ONE thin splice: it feeds J4-539's drop-in capped integrability brick
  `DaLimLUCapped.integrability_from_dominations_capped` into its IMMEDIATE downstream consumer in the
  leg-1 capstone body (`GlobalRawBoundFacade.hDaLimLU_from_labelled`, line ~512),
  `GlobalRawBoundFacade.memLapFull_from_labelled`, producing the `MemLapFull` census binder WITHOUT ever
  asserting the FALSE uncapped whole-time second-derivative domination `hAdom2`.  No `sorry` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SPLICE (J4-540).

  The leg-1 capstone `hDaLimLU_from_labelled` consumes the false uncapped `hAdom2` at EXACTLY ONE site —
  the census assembly `integrability_from_dominations`, whose four-output tuple
  `⟨hIlo, hIhi, hII_lo, hII_hi⟩` then flows (line ~512 of that capstone) into `memLapFull_from_labelled`
  (which uses only `hII_lo`/`hII_hi`) and (line ~524) into `hDaLimLU_concrete`.  J4-539 built the drop-in
  capped replacement `integrability_from_dominations_capped`: an IDENTICAL four-output tuple, but with
  `MemAdjLo` (= `hII_lo`) built INTERNALLY from the per-`m` CAPPED family `hAdom2cap` (via
  `CappedAdom2Audit.hII_lo_from_capped`) and `MemAdjHi` (= `hII_hi`) CARRIED verbatim as the labelled
  matched-sliver residual.

  This file, `memLapFull_from_labelled_capped`, routes that capped four-tuple ONE step onward:
    •  obtains `⟨_hIlo, _hIhi, hII_lo, hII_hi'⟩` from `integrability_from_dominations_capped`;
    •  threads `hII_lo` (capped-built) and `hII_hi'` (carried residual) into
       `GlobalRawBoundFacade.memLapFull_from_labelled`, alongside the gauge (`hgi`/`hΓ`), the frozen-side
       interchange `hInter`, the √ε sliver bundle (`D0`/`D1`/`hbnd`), and `hPd2conv`;
    •  yields `MemLapFull` — the untruncated Laplacian-comparison census binder — with **NO uncapped
       whole-time `hAdom2` anywhere on the path**.

  This is the leg-1 mirror of leg-2's `CappedAdom2Audit.memLapFull_from_pairing_dominations`, but wired
  THROUGH the J4-539 integrability brick (so the strip legs `hIlo`/`hIhi` are produced and discarded here
  too — genuine, independently satisfiable heat-operator Gaussian-bound inputs, per Sol consult, high).
  The irreducible leg-1 residue remains exactly `MemAdjHi` (Hi-leg integrability, `∫₀^{ε_m} τ⁻¹ = +∞`),
  the honest target of the moment-aware / matched-sliver campaign, CARRIED as `hII_hi`.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Advancing the leg-1 capped chain by this
  one splice does NOT derive the coefficient: the full capped leg-1 capstone (`hDaLimLU_from_labelled`
  still consumes the uncapped `hAdom2`; this file discharges only its `hLapFull` sub-goal from the capped
  family), the externally-supplied capped leg-2 `hLapFull`, the carried `MemAdjHi` residuals (both legs),
  the convergence trio, and the Seeley–DeWitt geometric wiring all remain.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUCapped
import QIQTH.GlobalRawBoundFacade

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimLUCappedStep2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-540 — `memLapFull_from_labelled_capped`.**  THE LEG-1 LO-CAPPED `MemLapFull` splice: the
    full `MemLapFull` census binder at the endgame gate `H_G := vanVleckGatedWitness …`,
    `E := heatOp g gi H_G`, `F := leviSeries E`, `pdpdH := witnessSecondXDeriv …`, produced by routing
    J4-539's drop-in capped integrability brick `DaLimLUCapped.integrability_from_dominations_capped`
    into its immediate downstream consumer `GlobalRawBoundFacade.memLapFull_from_labelled`.

      •  the LO adjacency leg (`hII_lo : MemAdjLo`) is obtained from the four-output capped tuple, whose
         `MemAdjLo` is built INTERNALLY from the per-`m` CAPPED second-derivative family `hAdom2cap`;
         **NO uncapped whole-time `hAdom2` appears**;
      •  the HI adjacency leg (`hII_hi : MemAdjHi`) is CARRIED verbatim as the labelled matched-sliver
         residual — NOT dischargeable from any pointwise second-derivative Gaussian domination
         (`∫₀^{ε_m} τ⁻¹ = +∞`);
      •  the two STRIP legs (`_hIlo`/`_hIhi`) are produced by the capped brick from the uncapped
         heat-operator Gaussian bound `hAdomHeat` (no `τ⁻¹` blow-up) and DISCARDED here — memLapFull needs
         only the adjacency legs;
      •  the gauge (`hgi`/`hΓ`), the frozen-side interchange `hInter`, the √ε sliver bundle
         (`D0`/`D1`/`hbnd`), and the labelled atomic carrier `hPd2conv` are threaded verbatim.

    Every hypothesis is SATISFIABLE and NON-VACUOUS; NONE is the conclusion.  The strip-leg inputs
    (`hAdomHeat`, `hmeasLo`, `hmeasHi`) are genuine independently-satisfiable heat-operator facts, not
    disguised assumptions of `MemLapFull`.  For the curved instantiation `g = g^K` (constant curvature),
    `hAdom2cap` is TRUE per J4-537, so this stays non-vacuous off the flat metric.  NOT `a₁ = R/6`. -/
theorem memLapFull_from_labelled_capped (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- gauge:
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    -- the frozen-side interchange member (from the W2 family):
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- (strip legs) the uncapped heat-operator Gaussian bound (no `τ⁻¹` blow-up):
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    -- (LO leg) the PER-`m` CAPPED second-derivative family — NO uncapped whole-time `hAdom2`:
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
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
    -- (HI leg) ★ THE MATCHED-SLIVER RESIDUAL — CARRIED, NOT from any pointwise 2nd-derivative domination:
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- the √ε sliver amplitude bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  -- (v-capped) obtain the four-output census from J4-539's drop-in capped integrability brick.
  obtain ⟨_hIlo, _hIhi, hII_lo, hII_hi'⟩ :=
    QIQTH.DaLimLUCapped.integrability_from_dominations_capped g gi hChr hK S a b U T wA CA wA2 wF CF CA2c
      hwA hCA hwA2 hCA2c hwF hCF hUpos hUT hAdomHeat hAdom2cap hFdomW hFzero hmeasLo hmeasHi hmeas2Lo hII_hi
  -- thread the capped-built LO leg + carried HI residual into the banked facade capstone.
  exact QIQTH.GlobalRawBoundFacade.memLapFull_from_labelled g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
    (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    hgi hΓ hInter hII_lo hII_hi' D0 D1 hD0 hD1 hbnd hPd2conv

end QIQTH.DaLimLUCappedStep2

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUCappedStep2.memLapFull_from_labelled_capped
