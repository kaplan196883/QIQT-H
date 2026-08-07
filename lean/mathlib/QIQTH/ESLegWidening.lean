/-
  ESLegWidening — J4-387: THE s-LEG WIDENING of the (ix) E-combination census pile.
  Widening the two `s`-profile interval-integrability carries `hES` / `hLapS` of the (ix)
  E-combination census pile (exposed by `GlobalRawBoundFacade.hDaLimLU_from_labelled`, block (ix))
  from the WINDOWED suppliers (`∀ u ∈ U`, produced by
  `GlobalRawBoundFacade.integrability_from_dominations` via the Gaussian-pairing engine
  `DaLimEasyTranche.pairing_intervalIntegrable`) to the census `∀ u : ℝ` shape.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only WIDENS two cheap census `s`-profile
  interval-integrability carries (`hES`, `hLapS`) from the banked windowed Gaussian-pairing supplier to
  the `∀ u` quantifier of the census — a pure quantifier widening, no new analytic content, and even
  that only as a REDUCTION to an every-ceiling family of the banked Gaussian dominations (the honest
  `hglobal`-style carry, matching the `dataLevi` every-ceiling carry structure).  NO `sorry` (header
  prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to
  (or trivially yielding) the conclusion, NO existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WIDENING ANALYSIS (at `W := vanVleckGatedWitness g gi hChr hK S a b`,
     `F := leviSeries (heatOp g gi W)`).

  The census `hES` / `hLapS` binders quantify over ALL `u : ℝ` (not `u ∈ U`), on the interval
  `0..(u − ε_m)`.  For arbitrary `u : ℝ` and `m : ℕ` there are exactly two cases:

  •  CASE 1 — `u − ε_m ≤ 0` (DEGENERATE interval).  The oriented interval `0..(u − ε_m)` has upper
     endpoint `≤ 0`, so its unordered core `Ι 0 (u − ε_m) = Set.Ioc (u − ε_m) 0 ⊆ {s ≤ 0}`.  On
     `{s ≤ 0}` the Levi source `F s z 0` vanishes (`hFzero`, the banked
     `source_from_leviData`/`hFzero_concrete` output), so the whole `z`-pairing integral is `0`; the
     integrand is `a.e.`-zero and `IntervalIntegrable` follows from `integrable_zero` +
     `Integrable.congr`.  DISCHARGED here unconditionally (`intervalIntegrable_of_deg`).

  •  CASE 2 — `u − ε_m > 0` (⟹ `0 < u`, since `ε_m > 0`).  Feed the Gaussian-pairing engine
     `DaLimEasyTranche.pairing_intervalIntegrable` with CEILING `Tc := u` (so `u ≤ Tc` is `le_rfl` and
     the strip endpoints `0, u − ε_m ≤ u`).  This needs the two Gaussian dominations UP TO the ceiling
     `u` — but `u` is unbounded, whereas the banked dominations `hAdomHeat` / `hFdomW` carry a FIXED
     ceiling `T`.  The honest resolution is the EVERY-CEILING family `hAdomEvery` / `hFdomEvery` /
     `hLapDomEvery`: for each ceiling `Tc` there is SOME width/constant Gaussian bound valid up to `Tc`
     (exactly the banked windowed domination re-issued per ceiling — satisfiable, matching the
     `dataLevi` every-ceiling carry).  With `Tc := u` the engine closes CASE 2.

  ⟹ OUTCOME: CASE 1 closes UNCONDITIONALLY; CASE 2 closes via the EVERY-CEILING carry (the honest
  `hglobal`-style widening of the windowed Gaussian dominations).  The `hmeas` slice measurability is
  also lifted to `∀ u` (a satisfiable carry, true for `F ≡ 0`, matching the windowed `hmeas`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE PROVIDES.
  •  `intervalIntegrable_of_deg` — the degenerate-interval helper (CASE 1), generic in the first
     factor `A`; the Levi-vanishing kills the integrand on `Ι 0 β` when `β ≤ 0`.
  •  `hES_all`  — the census `hES`  `∀ (m u)` shape (`A := heatOp g gi W`).
  •  `hLapS_all` — the census `hLapS` `∀ (m u)` shape
     (`A := fun τ _ z => laplaceBeltrami g gi (fun x => W τ x z) 0`).
  Both are direct instantiations of `pairing_intervalIntegrable` (CASE 2) + `intervalIntegrable_of_deg`
  (CASE 1).  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimEasyTranche
import QIQTH.ECombinationDischarge
import QIQTH.LaplaceBeltrami

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound QIQTH.LaplaceBeltrami
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open scoped Interval Topology BigOperators

namespace QIQTH.ESLegWidening

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (E0) — the DEGENERATE-interval helper (CASE 1 of the widening analysis).
    ############################################################################### -/

/-- **★ (E0) — `intervalIntegrable_of_deg`.**  The degenerate/reversed-interval leg of the widening.
    When the upper endpoint `β ≤ 0`, the oriented interval `0..β` has unordered core
    `Ι 0 β = Set.Ioc β 0 ⊆ {s ≤ 0}`, on which the Levi source `F s z 0` vanishes (`hFzero`), so the
    `z`-pairing integral `∫ z, A (u−s) 0 z · F s z 0 = 0`.  The integrand is thus `a.e.`-zero on
    `Ι 0 β`, and `IntervalIntegrable` follows from `integrable_zero` + `Integrable.congr`.  Generic in
    the first factor `A`; the ONLY hypothesis is the banked source vanishing `hFzero`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem intervalIntegrable_of_deg (A F : ℝ → Point n → Point n → ℝ) (u β : ℝ) (hβ : β ≤ 0)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0) :
    IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * F s z 0) volume 0 β := by
  rw [intervalIntegrable_iff]
  refine Integrable.congr
    (integrable_zero ℝ ℝ ((volume : Measure ℝ).restrict (Set.uIoc 0 β))) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  have hub : s ∈ Set.Ioc (min 0 β) (max 0 β) := hs
  have hs0 : s ≤ 0 := by
    have h2 : s ≤ max 0 β := hub.2
    rwa [max_eq_left hβ] at h2
  have hzeroFun : (fun z => A (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
    funext z; rw [hFzero s hs0 z, mul_zero]
  have hI0 : (∫ z, A (u - s) 0 z * F s z 0) = 0 := by
    rw [hzeroFun]; exact integral_zero (Point n) ℝ
  exact hI0.symm

/-! ###############################################################################
    ### (E1·hES) — the `∀ u` heat-operator strip integrability.
    ############################################################################### -/

/-- **★ (E1·hES) — `hES_all`.**  The census (ix) `hES` binder in its `∀ (m u)` shape:
    interval-integrability of the heat-operator pairing profile `s ↦ ∫ z, heatOp(u−s) 0 z · F s z 0`
    on `0..(u − ε_m)`, for EVERY `u : ℝ` (not just `u ∈ U`).  CASE 1 (`u − ε_m ≤ 0`) is
    `intervalIntegrable_of_deg`; CASE 2 (`u − ε_m > 0`, hence `0 < u`) is
    `DaLimEasyTranche.pairing_intervalIntegrable` at ceiling `Tc := u`, fed by the EVERY-CEILING heat
    domination `hAdomEvery` and the EVERY-CEILING Levi envelope `hFdomEvery` (the honest `hglobal`-style
    carries — the banked windowed Gaussian dominations re-issued per ceiling).  Carries: `hFzero`
    (source vanishing), `hAdomEvery`/`hFdomEvery` (every-ceiling Gaussian dominations), `hmeas` (the
    `∀ u` slice measurability, satisfiable — true for `F ≡ 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem hES_all (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hAdomEvery : ∀ Tc : ℝ, ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
          |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m u
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact intervalIntegrable_of_deg
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wA, CA, hwA, hCA, hAdom⟩ := hAdomEvery u
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact QIQTH.DaLimEasyTranche.pairing_intervalIntegrable
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u u wA CA wF CF hu0 le_rfl hwA hCA hwF hCF hAdom hFdom hFzero
      0 (u - epsSeq m) (le_of_lt hu0) (by linarith) (hmeas m u)

/-! ###############################################################################
    ### (E1·hLapS) — the `∀ u` laplaceBeltrami-slice strip integrability.
    ############################################################################### -/

/-- **★ (E1·hLapS) — `hLapS_all`.**  The census (ix) `hLapS` binder in its `∀ (m u)` shape:
    interval-integrability of the laplaceBeltrami-slice pairing profile
    `s ↦ ∫ z, laplaceBeltrami g gi (fun x => W (u−s) x z) 0 · F s z 0` on `0..(u − ε_m)`, for EVERY
    `u : ℝ`.  Identical widening structure to `hES_all` with the first factor
    `A := fun τ _ z => laplaceBeltrami g gi (fun x => W τ x z) 0` in place of `heatOp g gi W`: CASE 1 is
    `intervalIntegrable_of_deg`; CASE 2 is `pairing_intervalIntegrable` at `Tc := u`, fed by the
    EVERY-CEILING laplaceBeltrami-slice Gaussian domination `hLapDomEvery` (the slice analogue of the
    census `hAdom2` second-`x`-derivative bound, via `laplaceBeltrami_at_rnc_center`) and the
    EVERY-CEILING Levi envelope `hFdomEvery`.  ⚠ NOT `a₁ = R/6`. -/
theorem hLapS_all (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hLapDomEvery : ∀ Tc : ℝ, ∃ wL CL : ℝ, 0 < wL ∧ 0 ≤ CL ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
          |laplaceBeltrami g gi
              (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0|
            ≤ CL * gaussDdim (wL * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m u
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact intervalIntegrable_of_deg
      (fun τ _ z => laplaceBeltrami g gi
        (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wL, CL, hwL, hCL, hLapDom⟩ := hLapDomEvery u
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact QIQTH.DaLimEasyTranche.pairing_intervalIntegrable
      (fun τ _ z => laplaceBeltrami g gi
        (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u u wL CL wF CF hu0 le_rfl hwL hCL hwF hCF hLapDom hFdom hFzero
      0 (u - epsSeq m) (le_of_lt hu0) (by linarith) (hmeas m u)

end QIQTH.ESLegWidening

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.ESLegWidening.intervalIntegrable_of_deg
#print axioms QIQTH.ESLegWidening.hES_all
#print axioms QIQTH.ESLegWidening.hLapS_all
