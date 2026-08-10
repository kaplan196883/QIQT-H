/-
  DaLimLUCapped — J4-539.  The LEG-1 (Da-limit) LO-CAPPED integrability sub-assembly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  LEG-1 mirror of the leg-2 capped audit `CappedAdom2Audit.memLapFull_from_pairing_dominations`: a PURE
  INTERFACE RE-PLUMBING that replaces the census `integrability_from_dominations`' FALSE uncapped
  whole-time second-derivative domination `hAdom2` with {the per-`m` capped `hAdom2cap`} ∪ {the labelled
  `hII_hi : MemAdjHi` residual}.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited, nothing committed.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio
  + geometric-wiring stack, and — with LEG-1 still to be re-threaded through its ~45–180-binder capstone
  `hDaLimLU_from_labelled` — effectively FLAT-ONLY at 2nd-derivative order until that rewiring lands.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE LEG-1 SCOPE VERDICT (J4-539 — confirmed by Sol consult, high).

  Leg-1's capstone `GlobalRawBoundFacade.hDaLimLU_from_labelled` (producing `DaLimLUGoal`) consumes the
  uncapped `hAdom2` at EXACTLY ONE site — it feeds `GlobalRawBoundFacade.integrability_from_dominations`,
  which threads `hAdom2` into EXACTLY the two adjacency legs
    •  `DaLimEasyTranche.hII_lo_concrete` ⟹ `MemAdjLo` on `[0, u−ε_m]`  (`τ = u − s ∈ [ε_m, u)`, BOUNDED
       BELOW), and
    •  `DaLimEasyTranche.hII_hi_concrete` ⟹ `MemAdjHi` on `[u−ε_m, u]`  (`τ = u − s → 0`, NOT bounded),
  BOTH through the SAME generic engine `DaLimEasyTranche.pairing_intervalIntegrable` that leg-2 uses.  The
  two STRIP legs (`hIlo_concrete`/`hIhi_concrete`) ride on `hAdomHeat` (the heat operator itself, width
  `wA`, NO `τ⁻¹` blow-up), NOT on `hAdom2`, so they need NO capping — `hIhi` reaching `τ → 0` is harmless
  because it dominates the heat operator, not its singular second derivative.  Past
  `integrability_from_dominations`, `hAdom2` itself NEVER appears again — the downstream consumers
  (`memLapFull_from_labelled` and `hDaLimLU_concrete`) take only the `MemAdjLo`/`MemAdjHi` census binders,
  never the pointwise domination.  There is no pointwise limit, no `τ → 0` evaluation, and no non-integral
  estimate reaching for the uniform bound.

  ⟹  **LEG-1 FACTORS IDENTICALLY TO LEG-2.**  The LO leg is cappable (per-`m` constant `CA2c m`, via
  `CappedAdom2Audit.hII_lo_from_capped` ⟶ `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`);
  the HI leg (`∫₀^{ε_m} τ⁻¹ = +∞`) is NOT dischargeable from any pointwise second-derivative Gaussian
  domination and is CARRIED as the labelled `MemAdjHi` residual — the SAME moment-aware / matched-sliver
  integrability target that leg-2 carries.

  ## THE BRICK — `integrability_from_dominations_capped`.

  A drop-in replacement for `GlobalRawBoundFacade.integrability_from_dominations` producing the identical
  four-output census tuple (`hIlo`, `hIhi`, `MemAdjLo`, `MemAdjHi`), but:
    •  the two STRIP legs stay on the uncapped `hAdomHeat` (heat operator — no blow-up), unchanged;
    •  `MemAdjLo` is built INTERNALLY from the per-`m` CAPPED `hAdom2cap` via `hII_lo_from_capped`;
       **NO uncapped whole-time `hAdom2` appears**;
    •  `MemAdjHi` is CARRIED verbatim as the labelled residual `hII_hi`.
  This is the minimal honest leg-1 mirror of leg-2's `memLapFull_from_pairing_dominations`, and a drop-in
  substitute for the `integrability_from_dominations` call at line 495 of the eventual capped capstone
  `hDaLimLU_from_labelled_capped` (J4-540, the ~45–180-binder monolith, deferred).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CappedAdom2Audit
import QIQTH.GlobalRawBoundFacade

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimLUCapped

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-539 — `integrability_from_dominations_capped`.**  THE LEG-1 LO-CAPPED integrability
    sub-assembly.  Produces the SAME four-output census tuple as
    `GlobalRawBoundFacade.integrability_from_dominations` — the two strip interval-integrabilities
    (`hIlo`/`hIhi`, `A := heatOp g gi H_G`) plus `MemAdjLo` and `MemAdjHi` (`A := witnessSecondXDeriv`) —
    but the false uncapped whole-time second-derivative domination `hAdom2` is REPLACED by:
      •  the PER-`m` CAPPED second-derivative family `hAdom2cap` (per-`m` constant `CA2c m`), from which
         `MemAdjLo` (the LO leg `[0, u−ε_m]`, `τ = u − s ∈ [ε_m, u)` bounded below) is built INTERNALLY via
         `CappedAdom2Audit.hII_lo_from_capped`;  **NO uncapped `hAdom2` appears**;
      •  the LABELLED RESIDUAL `hII_hi : MemAdjHi` (the HI leg `[u−ε_m, u]`, `τ = u − s → 0`), CARRIED
         verbatim — NOT dischargeable from any pointwise second-derivative Gaussian domination
         (`∫₀^{ε_m} τ⁻¹ = +∞`), so it is the honest moment-aware / matched-sliver integrability target.
    The two STRIP legs ride on the uncapped `hAdomHeat` (the heat operator itself, width `wA`, no `τ⁻¹`
    blow-up), so they need NO capping.  Drop-in for `integrability_from_dominations` in the eventual
    capped capstone.  Every hypothesis is SATISFIABLE and NON-VACUOUS; none is the conclusion.  NOT
    `a₁ = R/6`. -/
theorem integrability_from_dominations_capped (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
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
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)) :
    (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
      ∧ (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume (u - epsSeq m) u)
      ∧ MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      ∧ MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
  ⟨QIQTH.DaLimEasyTranche.hIlo_concrete g gi hChr hK S a b U T wA CA wF CF
      hwA hCA hwF hCF hUpos hUT hAdomHeat hFdomW hFzero hmeasLo,
   QIQTH.DaLimEasyTranche.hIhi_concrete g gi hChr hK S a b U T wA CA wF CF
      hwA hCA hwF hCF hUpos hUT hAdomHeat hFdomW hFzero hmeasHi,
   -- ★ the LO leg from the CAPPED family — the uncapped `hAdom2` is never used:
   QIQTH.CappedAdom2Audit.hII_lo_from_capped g gi hChr hK S a b
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 wF CF CA2c
      hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdomW hFzero hmeas2Lo,
   -- ★ the HI leg carried verbatim as the labelled residual:
   hII_hi⟩

end QIQTH.DaLimLUCapped

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUCapped.integrability_from_dominations_capped
