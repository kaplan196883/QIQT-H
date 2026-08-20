/-
  InterchangeBundlesFromExisting — J4-898 (find-and-wire, mirroring J4-896/897).

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The LIVE order-1 capstone `HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`
  (carried by `HDuhamelLiveGateWired`, shared by `hDuhamel` AND `hDConv` via its `hDaLimLU` data
  census) carries FOUR "interchange-bundle" census binders as RAW hypotheses (source line numbers
  293-317):

    • `hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
                    (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)`
    • `hII_lo   : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)`
    • `hII_hi   : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)`
    • `hEcomb   : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F`

  where the capstone's own `F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))`
  (via its `hFeq`, a genuine defining equation, satisfiable by `rfl`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE FIND.  Each of the four binders ALREADY has a GENERIC-IN-ABSTRACT-`g` discharge, banked in an
  earlier session, that produces the EXACT census output type (its `pdpdH` is the verbatim
  `fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z`, and its `F` is the concrete
  `leviSeries (heatOp g gi (vanVleckGatedWitness …))`) — but NONE was ever wired to the abstract-`F`
  live-capstone binder shape (the only gap being the `hFeq` reconciliation `F = leviSeries …`):

    • `MemAdjHi`   ⟵ `MemAdjHiSliver.hII_hi_from_sliver`               (J4-392, moment-aware carry)
    • `MemAdjLo`   ⟵ `CappedAdom2Audit.hII_lo_from_capped`            (per-`m` capped domination)
    • `MemLapFull` ⟵ `CappedAdom2Audit.memLapFull_from_pairing_dominations`  (wall-A assembly)
    • `MemECombine`⟵ `DaLimCensusRecon.memECombine_of_data`          (per-`(m,u)` Fubini split)

  THIS FILE threads them into the abstract-`F` (`+ hFeq`) LIVE-capstone binder shape.  Object match is
  by `subst hFeq` (the `F = leviSeries …` reconciliation is `rfl`-satisfiable per the capstone's own
  `hFeq`); the substituted goal is then LITERALLY the banked brick's conclusion — verified by the file
  compiling.  Every carried hypothesis is the brick's OWN satisfiable, non-vacuous named carry; NONE is
  the conclusion; no `hAnear`, no uncapped `hAdom2`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CappedAdom2Audit
import QIQTH.MemAdjHiSliver
import QIQTH.DaLimCensusRecon

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.InterchangeBundlesFromExisting

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — `MemAdjHi` census binder from `MemAdjHiSliver.hII_hi_from_sliver`.
    ############################################################################### -/

/-- **★ `memAdjHi_live`.**  The live capstone's `hII_hi` census binder
    `MemAdjHi F U (fun i τ z => witnessSecondXDeriv …)` (at `F = leviSeries (heatOp g gi H_G)` via
    `hFeq`) DISCHARGED to the named satisfiable carries of the banked
    `MemAdjHiSliver.hII_hi_from_sliver`: the s-slice AEStronglyMeasurability inputs
    (`hUT`/`hεU`/`hSecCont`/`hBcont`) and the moment-improved `τ^{-1/2}` pairing bound `hGpow` (with a
    single `m`-uniform `Cpair ≥ 0`).  The opaque census binder is replaced by these — NONE the
    conclusion, all satisfiable / non-vacuous.  NOT `a₁ = R/6`. -/
theorem memAdjHi_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ) (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2)) :
    MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  subst hFeq
  exact QIQTH.MemAdjHiSliver.hII_hi_from_sliver g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow

/-! ###############################################################################
    ### §2 — `MemAdjLo` census binder from `CappedAdom2Audit.hII_lo_from_capped`.
    ############################################################################### -/

/-- **★ `memAdjLo_live`.**  The live capstone's `hII_lo` census binder
    `MemAdjLo F U (fun i τ z => witnessSecondXDeriv …)` (at `F = leviSeries (heatOp g gi H_G)` via
    `hFeq`) DISCHARGED to the named satisfiable carries of the banked
    `CappedAdom2Audit.hII_lo_from_capped`: the PER-`m` CAPPED second-derivative family `hAdom2cap`
    (NO uncapped whole-time `hAdom2`), the Levi source domination `hFdom`/vanishing `hFzero`, and the
    slice measurability `hmeas`.  NONE the conclusion; all satisfiable / non-vacuous.  NOT
    `a₁ = R/6`. -/
theorem memAdjLo_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  subst hFeq
  exact QIQTH.CappedAdom2Audit.hII_lo_from_capped g gi hChr hK S a b
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 wF CF CA2c
    hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdom hFzero hmeas

/-! ###############################################################################
    ### §3 — `MemLapFull` census binder from `CappedAdom2Audit.memLapFull_from_pairing_dominations`.
    ############################################################################### -/

/-- **★★ `memLapFull_live`.**  The live capstone's `hLapFull` census binder
    `MemLapFull g gi H_G F U (fun i τ z => witnessSecondXDeriv …)` (at `F = leviSeries (heatOp g gi H_G)`
    via `hFeq`) DISCHARGED to the named carries of the banked wall-A assembly
    `CappedAdom2Audit.memLapFull_from_pairing_dominations`: gauge (`hgi`/`hΓ`), the frozen-side
    interchange `hInter : MemInterchange`, the PER-`m` capped family `hAdom2cap` (NO uncapped
    `hAdom2`), the Levi source `hFdom`/`hFzero`, slice measurability `hmeas2Lo`, the √ε sliver bundle
    (`D0`/`D1`/`hbnd`), the atomic pd∘pd convergence carrier `hPd2conv`, and the labelled residual
    `hII_hi : MemAdjHi`.  NONE the conclusion; all satisfiable / non-vacuous.  NOT `a₁ = R/6`. -/
theorem memLapFull_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  subst hFeq
  exact QIQTH.CappedAdom2Audit.memLapFull_from_pairing_dominations g gi hChr hK S a b
    U T wA2 wF CF CA2c hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter hAdom2cap hFdom hFzero
    hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv

/-! ###############################################################################
    ### §4 — `MemECombine` census binder from `DaLimCensusRecon.memECombine_of_data`.
    ############################################################################### -/

/-- **★ `memECombine_live`.**  The live capstone's `hEcomb` census binder
    `MemECombine g gi H_G F` (at `F = leviSeries (heatOp g gi H_G)` via `hFeq`) DISCHARGED to the six
    per-`(m,u)` representation/integrability sub-facts of the banked
    `DaLimCensusRecon.memECombine_of_data` (the two `Da`/`Lap` representations, two fibrewise
    `Integrable`s, two `IntervalIntegrable`s).  NONE the conclusion; all satisfiable / non-vacuous.
    NOT `a₁ = R/6`. -/
theorem memECombine_live (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
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
        (fun z => laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F := by
  subst hFeq
  exact QIQTH.DaLimCensusRecon.memECombine_of_data g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    hDa hLap hLapZ hEZ hLapS hES

end QIQTH.InterchangeBundlesFromExisting

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.InterchangeBundlesFromExisting.memAdjHi_live
#print axioms QIQTH.InterchangeBundlesFromExisting.memAdjLo_live
#print axioms QIQTH.InterchangeBundlesFromExisting.memLapFull_live
#print axioms QIQTH.InterchangeBundlesFromExisting.memECombine_live
