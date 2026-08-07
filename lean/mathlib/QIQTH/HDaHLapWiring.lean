/-
  HDaHLapWiring — J4-404 (Sol #16 B1+B2): THE CENSUS (ix) `hDa`/`hLap` WIRING.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves
  NOTHING about `R/6`.  `a₁ = R/6` remains CONDITIONAL — on the whole `hDuhamel` /
  convergence-trio + geometric-wiring stack AND on the surviving labelled census carries
  threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Both theorems here are pure SPECIALIZATIONS of the banked W2 representations
  `InterchangeThreading.hDa_threaded` (T1a) and `InterchangeThreading.hLap_threaded` (T1b) at the
  CONCRETE census pair
      `W := vanVleckGatedWitness g gi hChr hK S a b`,   `F := leviSeries (heatOp g gi W)`,
  producing VERBATIM the two census (ix) binders `hDa`/`hLap` exposed by `CensusGeometryThread`
  (`hDaLimLU_from_geometry_census`) and `GlobalRawBoundFacade`.  Per the J4-386 verdict these binders
  are NOT definitional — they are the OUTPUTS of the differentiation-under-∫ / RNC-flat-reduction
  engines, so each carries only genuine, satisfiable, non-vacuous analytic data; NONE is the
  conclusion, NONE is `:= True`, NONE is `a₁ = R/6`.  No `sorry` (header prose excepted), no new
  axioms, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.

  •  (B1) `hDa_census_from_threaded` — the census (ix) `hDa` binder
       `∀ m u, DaTrunc W F m u = ∫ s in 0..(u−εₘ), ∫ z, ∂_r(W · 0 z)(u−s) · F s z 0`,
     obtained by threading `hDa_threaded` (T1a) at every time-base `u`.  The census is `∀ u`, and
     `hDa_threaded` is per-`u`, so the eight C3ε Da-Leibniz families are carried `∀ u` and curried at
     each `u`.  ⟹ carries the TIME-derivative differentiation-under-∫ bundle.

     CARRY ENUMERATION (B1).  The Da leg is the ∂_r (TIME) Leibniz engine; the banked `w2_*` facts
     (`W2Finish.w2_hQ1`/`w2_hdiff`/`w2_hFint`, `W2Package.w2_hFmeas`/`w2_hF'meas`) all live on the
     FIELD (`∂_{xᵢ}`) side feeding `MemInterchange`, hence discharge NONE of the Da-time carriers.
     All eight (`nb`/`hnb`, `hFmeas`, `hFint`, `hF'meas`, `bound`/`hbdd`, `hbound`, `hdiff`) REMAIN
     honest carries — this IS the maximal honest reduction of the `hDa` binder to the T1a engine.

  •  (B2) `hLap_census_from_threaded` — the census (ix) `hLap` binder
       `∀ m u, LapTrunc g gi W F m u = ∫ s in 0..(u−εₘ), ∫ z, Δ_g(fun x ↦ W(u−s) x z)(0) · F s z 0`,
     obtained by threading `hLap_threaded` (T1b) at every `u` with the parameter
     `pdpdH := witnessSecondXDeriv g gi hChr hK S a b`.

     CARRY ENUMERATION (B2).
       – `hpdpdH_slice` — DISCHARGED, DEFINITIONALLY (`rfl`).  With `pdpdH := witnessSecondXDeriv …`,
         `witnessSecondXDeriv … i (u−s) z` unfolds to `pd (fun x ↦ pd (fun x' ↦ W(u−s) x' z) i x) i 0`,
         which is (α-equal to) the required `pd (fun y ↦ pd (fun x ↦ W(u−s) x z) i y) i 0`.
       – `hInterchange` — DISCHARGED on `U` by the banked D package `W2Finish.memInterchange_at_gate`
         (its output is VERBATIM this shape, `pdpdH = witnessSecondXDeriv`, per `u ∈ U`).  Since the
         census binder is `∀ u : ℝ`, the `u ∉ U` tail is NOT covered by that windowed member, so the
         `∀ u` interchange stands as an honest carry (widening the D member off `U`).
       – `hgi`/`hΓ` — the RNC gauge at the centre; discharged from geometry by
         `GlobalRawBoundFacade.gauge_from_geometry`, carried here as the two gauge facts.
       – `hpdpdZ` (`z`-integrability) / `hII_lo` (`s`-interval-integrability) — REMAIN honest carries;
         reducible to the banked Gaussian dominations (cf. `ECombinationDischarge` /
         `integrability_from_dominations`), not manufactured here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE (ix) PILE STATUS after this brick (at the geometry-chosen gate):
    `hDa`  — reduced to the T1a time-Leibniz engine (B1).
    `hLap` — reduced to the T1b RNC/second-order engine (B2); `hpdpdH_slice` definitional, the
             interchange discharged on `U` by `memInterchange_at_gate`.
    `hEZ`/`hLapZ` — banked (`ECombinationDischarge`).
    `hES`/`hLapS` — windowed suppliers banked (`integrability_from_dominations`), `∀u` widening open.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterchangeThreading
import QIQTH.AmplitudePackage

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.HDaHLapWiring

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B1) — the census (ix) `hDa` binder from `hDa_threaded` (T1a).
    ############################################################################### -/

/-- **★ (B1) `hDa_census_from_threaded`.**  The census (ix) `hDa` binder (exposed by
    `CensusGeometryThread.hDaLimLU_from_geometry_census`) at the concrete pair
    `W := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi W)`:
        `∀ m u, DaTrunc W F m u = ∫ s in 0..(u−εₘ), ∫ z, ∂_r(W · 0 z)(u−s) · F s z 0`,
    threaded from `InterchangeThreading.hDa_threaded` (T1a) at every time-base `u` — the census is
    `∀ u`, `hDa_threaded` is per-`u`, so the eight C3ε Da-Leibniz families are carried `∀ u` and
    curried at each `u`.  All carries are the genuine TIME-derivative differentiation-under-∫ inputs
    of the C3ε engine (measurability, base/derivative interval-integrability, the uniform integrable
    derivative bound, the pointwise `HasDerivAt` family); NONE is discharged by the FIELD-side banked
    `w2_*` facts, NONE is the conclusion.  NOT `a₁ = R/6`. -/
theorem hDa_census_from_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    -- the C3ε TIME-derivative (`∂_r`) Da-Leibniz engine families, carried per time-base `u`:
    (nb : ℝ → ℕ → Set ℝ) (hnb : ∀ (u : ℝ) (m : ℕ), nb u m ∈ 𝓝 u)
    (hFmeas : ∀ (u : ℝ) (m : ℕ) (c : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (u : ℝ) (m : ℕ), IntervalIntegrable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (u : ℝ) (m : ℕ), AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℝ → ℕ → ℝ → ℝ)
    (hbdd : ∀ (u : ℝ) (m : ℕ), IntervalIntegrable (bound u m) volume 0 (u - epsSeq m))
    (hbound : ∀ (u : ℝ) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb u m,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s)
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound u m s)
    (hdiff : ∀ (u : ℝ) (m : ℕ), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb u m,
        HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s)
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) c) :
    ∀ (m : ℕ) (u : ℝ),
      DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
      = ∫ s in (0)..(u - epsSeq m), ∫ z,
          deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 :=
  fun m u =>
    hDa_threaded (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
      (nb u) (hnb u) (hFmeas u) (hFint u) (hF'meas u)
      (bound u) (hbdd u) (hbound u) (hdiff u) m

/-! ###############################################################################
    ### (B2) — the census (ix) `hLap` binder from `hLap_threaded` (T1b).
    ############################################################################### -/

/-- **★★ (B2) `hLap_census_from_threaded`.**  The census (ix) `hLap` binder (exposed by
    `CensusGeometryThread.hDaLimLU_from_geometry_census`) at the concrete pair
    `W := vanVleckGatedWitness g gi hChr hK S a b`, `F := leviSeries (heatOp g gi W)`:
        `∀ m u, LapTrunc g gi W F m u = ∫ s in 0..(u−εₘ), ∫ z, Δ_g(fun x ↦ W(u−s) x z)(0) · F s z 0`,
    threaded from `InterchangeThreading.hLap_threaded` (T1b) at every `u`, with the interchange
    parameter FIXED to the concrete second field-partial `pdpdH := witnessSecondXDeriv g gi hChr hK
    S a b`.  With that choice the `hpdpdH_slice` identification is DEFINITIONAL (`rfl`), so it does not
    appear as a carry; the interchange `hInterchange` is the VERBATIM output shape of the banked D
    package `W2Finish.memInterchange_at_gate` (discharged on `U`, carried `∀ u` here); `hgi`/`hΓ` are
    the RNC gauge (from `gauge_from_geometry`); `hpdpdZ`/`hII_lo` are the genuine `z`- and `s`-
    integrability carries (reducible to the banked Gaussian dominations).  NONE is the conclusion.
    NOT `a₁ = R/6`. -/
theorem hLap_census_from_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    -- RNC gauge at the centre (from `gauge_from_geometry`):
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    -- the second-order pd∘pd interchange (VERBATIM `memInterchange_at_gate`, carried `∀ u`):
    (hInterchange : ∀ (u : ℝ) (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n),
              witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    -- `z`-integrability of the interchange integrand:
    (hpdpdZ : ∀ (u : ℝ) (s : ℝ) (i : Fin n),
        Integrable (fun z => witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    -- `s`-interval-integrability of the inner `z`-pairing on the truncated window:
    (hII_lo : ∀ (u : ℝ) (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume 0 (u - epsSeq m)) :
    ∀ (m : ℕ) (u : ℝ),
      LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
      = ∫ s in (0)..(u - epsSeq m), ∫ z,
          laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 :=
  fun m u =>
    hLap_threaded g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u hgi hΓ
      (witnessSecondXDeriv g gi hChr hK S a b)
      (hInterchange u) (fun _ _ _ => rfl) (hpdpdZ u) (hII_lo u) m

end QIQTH.HDaHLapWiring

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HDaHLapWiring.hDa_census_from_threaded
#print axioms QIQTH.HDaHLapWiring.hLap_census_from_threaded
