/-
  InterchangeBundlesDeeperWired — deeper find-and-wire on top of J4-898
  `InterchangeBundlesFromExisting`.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-898 `InterchangeBundlesFromExisting` reduced the four LIVE-capstone interchange-bundle
  census binders (`MemAdjHi`/`MemAdjLo`/`MemLapFull`/`MemECombine`) to explicit underlying hypothesis
  lists (`memAdjHi_live`/`memAdjLo_live`/`memLapFull_live`/`memECombine_live`).  Several of THOSE
  underlying hypotheses are themselves ASSEMBLED objects (Gaussian dominations, RNC gauges) that have
  their OWN banked providers in terms of STRICTLY MORE PRIMITIVE carries.  This file threads those
  providers into the `memAdjLo_live`/`memLapFull_live` binder shapes, producing DEEPER-reduced variants
  whose carries are the primitive crude second-derivative envelope, the RNC first-derivative gauge, and
  `1 ≤ n` — rather than the assembled capped-family / Christoffel-vanishing packages.

    • `hFzero`     ⟵ `DaLimEasyTranche.hFzero_concrete`                 (structural; needs only `1 ≤ n`)
    • `hAdom2cap`  ⟵ `CappedAdom2Audit.hAdom2_capped_family_of_crude`  (from the crude `τ⁻¹` envelope)
    • `hΓ`         ⟵ `DaLimCensusRecon.memGaugeGamma_of_hdg0`          (from the RNC gauge `∂g(0)=0`)

  DELIBERATELY NOT wired: `hgi ⟵ memGaugeGi_of_geometry` — its `hframeK` (flat-metric-on-`K`) is the
  known flat-on-`K` vacuity landmine once `hmassone` re-enters downstream, so `hgi` is kept as an
  honest carry (gpt-5.6-sol go/no-go, high, this session).  Likewise `hII_hi` is kept as an honest
  carry (NOT recursed into `memAdjHi_live`), so this file does NOT drag in §1's `hGpow`/`hSecCont`.

  The genuinely-hard residuals stay VISIBLE as named carries: `hGpow` (moment-aware `τ⁻¹ᐟ²` pairing),
  `hbnd` (√ε matched-sliver amplitude), `hPd2conv` (atomic `pd∘pd` convergence), `hInter`
  (`MemInterchange`), `hFdom`/`hmeas`.  Every carry here is satisfiable / non-vacuous; NONE is the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterchangeBundlesFromExisting
import QIQTH.DaLimEasyTranche

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.InterchangeBundlesDeeperWired

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — `MemAdjLo` from the PRIMITIVE crude envelope + `1 ≤ n` (drops `hAdom2cap`/`hFzero`).
    ############################################################################### -/

/-- **★ `memAdjLo_live_crude`.**  The live capstone's `hII_lo` census binder
    `MemAdjLo F U (fun i τ z => witnessSecondXDeriv …)` (at `F = leviSeries (heatOp g gi H_G)` via
    `hFeq`) DISCHARGED to STRICTLY MORE PRIMITIVE carries than `memAdjLo_live`: the assembled
    per-`m` capped family `hAdom2cap` is replaced by the single crude `τ⁻¹·gaussDdim` envelope
    `hcrude` (via `CappedAdom2Audit.hAdom2_capped_family_of_crude`, with the canonical constant
    `CA2c m := Ccrude·(epsSeq m)⁻¹`), and the Levi vanishing `hFzero` is replaced by `1 ≤ n` (via
    `DaLimEasyTranche.hFzero_concrete`).  The Levi source domination `hFdom` and slice measurability
    `hmeas` are kept as honest carries.  NONE the conclusion; all satisfiable / non-vacuous.  NOT
    `a₁ = R/6`. -/
theorem memAdjLo_live_crude (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (hn : 1 ≤ n)
    (T wA2 wF CF Ccrude : ℝ)
    (hwA2 : 0 < wA2) (hwF : 0 < wF) (hCF : 0 ≤ CF) (hCcrude : 0 ≤ Ccrude)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  -- canonical capped constant (chosen AFTER `m`; the honest `∀ m ∃ CA2(ε_m)` side).
  have hCA2c : ∀ m, 0 ≤ (fun m => Ccrude * (epsSeq m)⁻¹) m := by
    intro m
    exact mul_nonneg hCcrude (le_of_lt (inv_pos.mpr (epsSeq_pos m)))
  -- the per-`m` capped family from the crude envelope.
  have hAdom2cap := QIQTH.CappedAdom2Audit.hAdom2_capped_family_of_crude
    g gi hChr hK S a b T Ccrude wA2 hCcrude hcrude
  -- the Levi vanishing from `1 ≤ n`.
  have hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => QIQTH.DaLimEasyTranche.hFzero_concrete g gi hChr hK S a b hn s hs z 0
  exact QIQTH.InterchangeBundlesFromExisting.memAdjLo_live g gi hChr hK S a b U F hFeq
    T wA2 wF CF (fun m => Ccrude * (epsSeq m)⁻¹)
    hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdom hFzero hmeas

/-! ###############################################################################
    ### §2 — `MemLapFull` from the PRIMITIVE crude envelope + RNC gauge + `1 ≤ n`.
    ###       (drops `hAdom2cap`/`hFzero`/`hΓ`; keeps `hgi`/`hInter`/`hbnd`/`hPd2conv`/`hII_hi`.)
    ############################################################################### -/

/-- **★★ `memLapFull_live_crude`.**  The live capstone's `hLapFull` census binder DISCHARGED to
    STRICTLY MORE PRIMITIVE carries than `memLapFull_live`: `hAdom2cap ⟵ hcrude` (canonical constant
    `Ccrude·(epsSeq m)⁻¹`), `hFzero ⟵ 1 ≤ n`, and `hΓ (MemGaugeGamma) ⟵ hdg0` (the RNC
    first-derivative gauge `∂g(0)=0`).  `hgi` is KEPT as an honest carry (its `memGaugeGi_of_geometry`
    provider carries the flat-on-`K` vacuity landmine).  The genuinely-hard residuals stay VISIBLE:
    `hInter (MemInterchange)`, `hII_hi (MemAdjHi)`, the √ε sliver `hbnd`, the atomic `hPd2conv`, plus
    `hFdom`/`hmeas2Lo`.  NONE the conclusion; all satisfiable / non-vacuous.  NOT `a₁ = R/6`. -/
theorem memLapFull_live_crude (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (hn : 1 ≤ n)
    (T wA2 wF CF Ccrude : ℝ)
    (hwA2 : 0 < wA2) (hwF : 0 < wF) (hCF : 0 ≤ CF) (hCcrude : 0 ≤ Ccrude)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hgi : MemGaugeGi (n := n) gi)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
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
  have hCA2c : ∀ m, 0 ≤ (fun m => Ccrude * (epsSeq m)⁻¹) m := by
    intro m
    exact mul_nonneg hCcrude (le_of_lt (inv_pos.mpr (epsSeq_pos m)))
  have hAdom2cap := QIQTH.CappedAdom2Audit.hAdom2_capped_family_of_crude
    g gi hChr hK S a b T Ccrude wA2 hCcrude hcrude
  have hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0 :=
    fun s hs z => QIQTH.DaLimEasyTranche.hFzero_concrete g gi hChr hK S a b hn s hs z 0
  have hΓ : MemGaugeGamma (n := n) g gi :=
    QIQTH.DaLimCensusRecon.memGaugeGamma_of_hdg0 g gi hdg0
  exact QIQTH.InterchangeBundlesFromExisting.memLapFull_live g gi hChr hK S a b U F hFeq
    T wA2 wF CF (fun m => Ccrude * (epsSeq m)⁻¹)
    hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter hAdom2cap hFdom hFzero hmeas2Lo hII_hi
    D0 D1 hD0 hD1 hbnd hPd2conv

end QIQTH.InterchangeBundlesDeeperWired

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.InterchangeBundlesDeeperWired.memAdjLo_live_crude
#print axioms QIQTH.InterchangeBundlesDeeperWired.memLapFull_live_crude
