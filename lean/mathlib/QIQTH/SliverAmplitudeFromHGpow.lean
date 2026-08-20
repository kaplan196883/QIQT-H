/-
  SliverAmplitudeFromHGpow — the √ε matched-sliver amplitude `hbnd` REDUCED to the
  moment-aware τ⁻¹ᐟ² pairing carry `hGpow`.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-914 `InterchangeBundlesDeeperWired` left the live capstone's `memLapFull_live_crude`
  binder carrying TWO genuinely-hard named residuals side by side:
    • `hGpow` — the moment-aware τ⁻¹ᐟ² pairing bound
        `|∫ z, W''(u−s) z · F s z 0| ≤ Cpair · (u−s)^{-1/2}`   (the WideSliverBoundary target), and
    • `hbnd` — the √ε matched-sliver amplitude bound
        `|∫ s in (u−ε_m)..u, ∫ z, W''(u−s) z · F s z 0| ≤ D0 i · (2√ε_m) + D1 i · ε_m`.

  This file DISCHARGES `hbnd` FROM `hGpow`: integrating the pointwise τ⁻¹ᐟ² pairing bound over the
  matched sliver `[u−ε_m, u]` yields EXACTLY the `2√ε_m` amplitude, since
        `∫ s in (u−ε_m)..u, (u−s)^{-1/2} ds = 2√ε_m`.
  So the two named carries COLLAPSE onto the single one (`hGpow`) — a dependency-frontier reduction
  (in the spirit of J4-914), NOT a new analytic result and NOT a logical weakening.  The interval
  integrability of the inner pairing (needed for the integral triangle inequality) is supplied
  INTERNALLY from the SAME `hGpow` + sliver-continuity carries via the banked
  `MemAdjHiSliver.hII_hi_from_sliver` (`MemAdjHi`); so `hbnd_from_hGpow`'s antecedent set is EXACTLY
  `hII_hi_from_sliver`'s.  Every hypothesis is the same satisfiable/non-vacuous sliver data already
  carried by the live capstone; the conclusion is the `hbnd` predicate, NOT `a₁ = R/6`.

  `D0 := fun _ => Cpair`, `D1 := fun _ => 0` are the canonical constants delivered here (the `D1·ε_m`
  slot is genuinely absent — the pure τ⁻¹ᐟ² profile pays no `ε_m` term), giving a drop-in for
  `InterchangeBundlesDeeperWired.memLapFull_live_crude`'s `hbnd`.
-/
import Mathlib
import QIQTH.MemAdjHiSliver

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon
open scoped Interval Topology BigOperators

namespace QIQTH.SliverAmplitudeFromHGpow

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the sliver time integral `∫ (u−s)^{-1/2} ds = 2√ε_m`.
    ############################################################################### -/

/-- **★ `integral_invSqrt_sub_sliver`.**  The exact value of the matched-sliver time integral of the
    moment-improved dominator: `∫ s in (u−ε)..u, (u−s)^{-1/2} ds = 2√ε` (`ε > 0`).  Substituting
    `x = u−s` gives `∫₀^ε x^{-1/2} dx = 2ε^{1/2}`.  Pure Mathlib (`integral_comp_sub_left` +
    `integral_rpow`).  NOT `a₁ = R/6`. -/
theorem integral_invSqrt_sub_sliver (u ε : ℝ) (_hε : 0 < ε) :
    (∫ s in (u - ε)..u, (u - s) ^ (-(1 : ℝ) / 2)) = 2 * Real.sqrt ε := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) u,
      sub_self, sub_sub_cancel,
      integral_rpow (Or.inl (show (-1 : ℝ) < -(1 : ℝ) / 2 by norm_num)),
      Real.zero_rpow (show -(1 : ℝ) / 2 + 1 ≠ 0 by norm_num), sub_zero,
      Real.sqrt_eq_rpow,
      show -(1 : ℝ) / 2 + 1 = 1 / (2 : ℝ) from by norm_num]
  ring

/-! ###############################################################################
    ### §2 — ★★ the amplitude bound: `hbnd` from `hGpow`.
    ############################################################################### -/

/-- **★★ `sliver_amplitude_from_hGpow`.**  THE √ε MATCHED-SLIVER AMPLITUDE, derived from the
    moment-aware τ⁻¹ᐟ² pairing carry `hGpow` (with the SAME sliver-continuity carries
    `hUT`/`hεU`/`hSecCont`/`hBcont` that `MemAdjHiSliver.hII_hi_from_sliver` consumes).  For every
    `i, m` and `u ∈ U`:
        `|∫ s in (u−ε_m)..u, ∫ z, W''(u−s) z · F s z 0| ≤ Cpair · (2√ε_m)`.
    Route: interval integrability of the inner pairing from `hII_hi_from_sliver` (`MemAdjHi`), then
    the integral triangle inequality (`abs_integral_le_integral_abs`) + pointwise `hGpow` domination
    on the sliver (`integral_mono_on_of_le_Ioo`), evaluated by `integral_invSqrt_sub_sliver`.  NONE is
    the conclusion; every hypothesis is the satisfiable sliver data.  NOT `a₁ = R/6`. -/
theorem sliver_amplitude_from_hGpow (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
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
    ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
      |∫ s in (u - epsSeq m)..u, ∫ z,
          witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ Cpair * (2 * Real.sqrt (epsSeq m)) := by
  have hII := QIQTH.MemAdjHiSliver.hII_hi_from_sliver g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow
  intro i m u hu
  have hεpos := epsSeq_pos m
  have hle : u - epsSeq m ≤ u := by linarith
  -- interval integrability of the inner pairing (= the `MemAdjHi` component)
  have hφII : IntervalIntegrable
      (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume (u - epsSeq m) u := hII m i u hu
  -- the interval-integrable majorant
  have hMint : IntervalIntegrable (fun s => Cpair * (u - s) ^ (-(1 : ℝ) / 2))
      volume (u - epsSeq m) u :=
    (QIQTH.MemAdjHiSliver.intervalIntegrable_invSqrt_sub u (epsSeq m) hεpos).const_mul Cpair
  calc |∫ s in (u - epsSeq m)..u, ∫ z,
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
      ≤ ∫ s in (u - epsSeq m)..u, |∫ z,
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ s in (u - epsSeq m)..u, Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hle hφII.abs hMint (fun s hs => ?_)
        have hmem : s ∈ Set.uIoc (u - epsSeq m) u := by
          rw [Set.uIoc_of_le hle]; exact Set.Ioo_subset_Ioc_self hs
        exact hGpow m i u hu s hmem
    _ = Cpair * ∫ s in (u - epsSeq m)..u, (u - s) ^ (-(1 : ℝ) / 2) :=
        intervalIntegral.integral_const_mul _ _
    _ = Cpair * (2 * Real.sqrt (epsSeq m)) := by
        rw [integral_invSqrt_sub_sliver u (epsSeq m) hεpos]

/-- **★★ `hbnd_from_hGpow`.**  The `sliver_amplitude_from_hGpow` bound cast into the EXACT `hbnd`
    census-carry shape of `InterchangeBundlesDeeperWired.memLapFull_live_crude`, with the canonical
    constants `D0 := fun _ => Cpair`, `D1 := fun _ => 0` (the `D1·ε_m` slot is genuinely absent — the
    pure τ⁻¹ᐟ² profile pays no `ε_m` term).  A drop-in for that capstone's `hbnd` argument (feed
    `D0 := fun _ => Cpair`, `D1 := fun _ => 0`, `hD0 := fun _ => hCpair`, `hD1 := fun _ => le_refl 0`).
    NONE the conclusion; NOT `a₁ = R/6`. -/
theorem hbnd_from_hGpow (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
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
    ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
      |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
          witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ (fun _ : Fin n => Cpair) i * (2 * Real.sqrt (epsSeq m))
          + (fun _ : Fin n => (0 : ℝ)) i * epsSeq m := by
  intro i m u hu
  have h := sliver_amplitude_from_hGpow g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow i m u hu
  simpa using h

end QIQTH.SliverAmplitudeFromHGpow

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverAmplitudeFromHGpow.integral_invSqrt_sub_sliver
#print axioms QIQTH.SliverAmplitudeFromHGpow.sliver_amplitude_from_hGpow
#print axioms QIQTH.SliverAmplitudeFromHGpow.hbnd_from_hGpow
