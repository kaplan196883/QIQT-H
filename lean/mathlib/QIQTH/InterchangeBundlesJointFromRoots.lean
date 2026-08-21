/-
  InterchangeBundlesJointFromRoots — J4-964: the FULL JOINT COMPOSITION of the four "interchange
  bundle" census dischargers (`MemAdjHi` / `MemAdjLo` / `MemLapFull` / `MemECombine`) at a SINGLE
  SHARED base instantiation, with the genuine internal seam `memAdjHi_live → memLapFull_live`
  (the produced `MemAdjHi` IS `memLapFull_live`'s `hII_hi` input) and the shared dominations
  (`hFzero` / `hFdom` / `hAdom2cap` / `hmeas`) DEDUPLICATED to a single carry each.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / consolidation brick over the ALREADY-BANKED
  `InterchangeBundlesFromExisting.{memAdjHi_live, memAdjLo_live, memLapFull_live, memECombine_live}`
  (J4-898).  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS IS A GENUINE (not cosmetic) JOINT COMPOSITION.

  The four census binders `hLapFull` / `hII_lo` / `hII_hi` / `hEcomb` of the LIVE order-1 capstone
  census (`HDConvLiveGateWired.hDConv_live_gate_wired`, lines 143-146 & 167; identically in
  `HDuhamelLiveGateWired`) were each discharged INDEPENDENTLY by a standalone `*_live` lemma.  Composed
  ONE-AT-A-TIME, they DUPLICATE carriers: each of `memAdjLo_live` / `memLapFull_live` carries its OWN
  `hFdom` / `hFzero` / `hAdom2cap` / slice-measurability; and `memLapFull_live` carries `hII_hi` as an
  ABSTRACT residual.  This brick composes all four at ONE shared `(g, gi, hChr, hK, S, a, b, U, F)` so
  that:

    •  `memAdjHi_live`'s output `MemAdjHi (leviSeries …) U (fun i τ z ↦ witnessSecondXDeriv …)`
       is fed INTERNALLY as `memLapFull_live`'s `hII_hi` argument (a GENUINE seam — `hII_hi` is NO
       LONGER a root of the joint bundle; it is DERIVED from `{hSecCont, hBcont, Cpair, hGpow, hUT,
       hεU}`);
    •  the pairwise-identical dominations `hFdom` / `hFzero` / `hAdom2cap` and the slice-measurability
       `hmeas` (= `memLapFull_live`'s `hmeas2Lo`, the SAME proposition) are each passed to BOTH
       consumers from a SINGLE carry.

  So the joint bundle's residual ROOT set is STRICTLY SMALLER than the disjoint union of the four
  individual signatures: `hII_hi` is eliminated and four domination/measurability carriers are halved.

  ## HONEST NON-COLLAPSE (measured, not assumed).  Even after this consolidation the residual root set
  does NOT collapse to `{hAmp0, hCfield}` or to any "few-wall" set.  It is EXACTLY:
      base geometry `{g, gi, hChr, hK, S, a, b}`, window `{U, T, hUpos, hUT, hεU}`,
      gauge `{hgi : MemGaugeGi, hΓ : MemGaugeGamma}`,
      the capped 2nd-derivative domination `hAdom2cap` (+ its constants `wA2, CA2c`),
      the Levi source domination `hFdom` / vanishing `hFzero` (+ `wF, CF`),
      slice-measurability `hmeas`,
      the frozen-side interchange `hInter : MemInterchange`,
      the √ε sliver bundle `{D0, D1, hD0, hD1, hbnd}`,
      the atomic pd∘pd convergence `hPd2conv`,
      the `MemAdjHi` s-slice inputs `{hSecCont, hBcont}` + moment pairing `{Cpair, hGpow}`,
      and the `MemECombine` representation/integrability sextet `{hDa, hLap, hLapZ, hEZ, hLapS, hES}`.
  These are GENUINELY DISTINCT analytic primitives that do NOT further coalesce among themselves —
  confirming (gpt-5.6-sol high, 2026-08-21) that the "15 dischargers collapse to 5 walls" hypothesis is
  FALSE: the dischargers cover only ~15/40 census binders and reduce each to distinct non-coalescing
  roots.  This brick is the POSITIVE SUFFICIENCY CERTIFICATE for the four-interchange sub-census.

  ## NON-VACUITY.  RELATIVE, identical in status to the four individual banked dischargers it composes
  (whose own non-vacuity is relative to the standing genuine census carriers — the Levi/interchange
  objects of the real heat-kernel analysis).  The joint bundle introduces NO new primitive beyond the
  union of the four, and REMOVES `hII_hi`; it therefore cannot be more vacuous than its parts.  No
  hypothesis is `:= True`, self-referential to the conclusion, or forces a degenerate geometry (unlike
  the retired cp466 `hframeK ⟹ K = {0}` family — none of these carriers pins `K` or `S`).  ⚠ NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterchangeBundlesFromExisting

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.InterchangeBundlesJointFromRoots

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-964 — `interchange_bundles_joint`.**  The FULL JOINT COMPOSITION of the four interchange
    census dischargers at ONE shared base `(g, gi, hChr, hK, S, a, b, U)` and the concrete Levi source
    `F := leviSeries (heatOp g gi (vanVleckGatedWitness …))`.  PRODUCES the four census binders
    `hLapFull ∧ hII_lo ∧ hII_hi ∧ hEcomb` of `hDConv_live_gate_wired` / `hDuhamel_live_gate_wired`
    SIMULTANEOUSLY.

    THE SEAM: the `MemAdjHi` conjunct is produced by `memAdjHi_live` and reused INTERNALLY as
    `memLapFull_live`'s `hII_hi` — so `hII_hi` is DERIVED, not carried.  THE DEDUP: `hFdom` / `hFzero` /
    `hAdom2cap` / `hmeas` are each passed to both `memAdjLo_live` and `memLapFull_live` from a single
    carry.  The residual root set is the (measured) union documented in the file header — genuinely
    distinct primitives that do NOT collapse to a few walls.  ⚠ NOT `a₁ = R/6`. -/
theorem interchange_bundles_joint (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    -- gauge:
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    -- shared dominations (DEDUPLICATED — one carry, both consumers):
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
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- frozen-side interchange:
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- √ε sliver bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- atomic pd∘pd convergence:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    -- MemAdjHi s-slice inputs + moment pairing (these PRODUCE hII_hi, which feeds MemLapFull):
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
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2))
    -- MemECombine representation/integrability sextet:
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
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      ∧ MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      ∧ MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
          (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      ∧ MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) := by
  -- THE SEAM: produce `hII_hi := MemAdjHi …` from `memAdjHi_live`; reuse internally for `memLapFull_live`.
  have hII_hi := QIQTH.InterchangeBundlesFromExisting.memAdjHi_live g gi hChr hK S a b T U
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
    hUT hεU hSecCont hBcont Cpair hCpair hGpow
  -- `MemAdjLo` from the shared dominations.
  have hLo := QIQTH.InterchangeBundlesFromExisting.memAdjLo_live g gi hChr hK S a b U
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
    T wA2 wF CF CA2c hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdom hFzero hmeas
  -- `MemLapFull` — consumes the SAME shared dominations AND the seam `hII_hi`.
  have hMLF := QIQTH.InterchangeBundlesFromExisting.memLapFull_live g gi hChr hK S a b U
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
    T wA2 wF CF CA2c hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter hAdom2cap hFdom hFzero hmeas
    hII_hi D0 D1 hD0 hD1 hbnd hPd2conv
  -- `MemECombine` from the representation/integrability sextet.
  have hEc := QIQTH.InterchangeBundlesFromExisting.memECombine_live g gi hChr hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) rfl
    hDa hLap hLapZ hEZ hLapS hES
  exact ⟨hMLF, hLo, hII_hi, hEc⟩

end QIQTH.InterchangeBundlesJointFromRoots

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.InterchangeBundlesJointFromRoots
#print axioms interchange_bundles_joint
end AxiomChecks
