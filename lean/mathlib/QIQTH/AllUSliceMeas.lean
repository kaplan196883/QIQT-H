/-
  AllUSliceMeas — J4-389: THE ∀u SLICE-MEASURABILITY CARRIES of the (ix) E-combination pile.
  Discharging (down to the J4-383/384 machinery + Levi vanishing + honest every-ceiling
  joint-continuity carries) the two `∀u`-quantified s-slice `AEStronglyMeasurable` `hmeas`
  hypotheses consumed by
    • `QIQTH.ESLegWidening.hES_all` / `QIQTH.EveryCeilingFamilies.hES_hypothesis_light`
      (the `heatOp · leviSeries` pairing), and
    • `QIQTH.ESLegWidening.hLapS_all` / `QIQTH.EveryCeilingFamilies.hLapS_all_capped`
      (the `laplaceBeltrami-slice · leviSeries` pairing).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only supplies the two `∀ (m u)` s-slice
  ae-strong-measurability facts as genuine (std-3, axiom-free) theorems, by COMPOSITION of the
  ALREADY-BANKED J4-383 reusable core `QIQTH.SliceMeasurability.sliceMeas_of_jointCont` with the
  banked Levi-source vanishing and honest, satisfiable, per-ceiling joint-continuity carries.  NO
  `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis,
  NONE equal to (or trivially yielding) the conclusion, NO existing file edited, nothing committed,
  nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SHAPE-COMPARISON VERDICT  (J4-383 vs the ESLegWidening / EveryCeilingFamilies `hmeas` carries).

  The ESLegWidening / EveryCeilingFamilies `hmeas` carries ARE instances of the SAME
  `sliceMeas_of_jointCont` machinery, with THREE differences from the J4-383 census facts
  (`hmeasLo_slice` / `hmeas2Lo_slice`):

  •  (a) QUANTIFIER: J4-383 quantifies `∀ u ∈ U` with the carried window bounds
     `hUT : ∀ u ∈ U, u ≤ T` and `hεU : ∀ m u ∈ U, epsSeq m ≤ u`, so `u − εₘ ≥ 0` ALWAYS and the
     window `uIoc 0 (u−εₘ) = Ioc 0 (u−εₘ)` is a genuine forward interval inside a FIXED ceiling `T`.
     The ESLegWidening carries quantify `∀ u : ℝ` with NO bounds, so `u − εₘ` can be `≤ 0` (the
     DEGENERATE regime) and the ceiling `T` is `u` ITSELF (unbounded).  Handled by a
     DICHOTOMY `rcases le_or_gt (u − εₘ) 0`:
        – DEGENERATE (`u − εₘ ≤ 0`): the window `uIoc 0 (u−εₘ) = Ioc (u−εₘ) 0 ⊆ {s ≤ 0}`; on `{s ≤ 0}`
          the Levi factor `leviSeries … s z 0 = 0` (banked `hFzero`), so the whole `z`-pairing is `0`
          and the s-slice map is `a.e.`-CONSTANT `0` — `AEStronglyMeasurable` via
          `aestronglyMeasurable_const.congr`.  (This is the measurability twin of
          `ESLegWidening.intervalIntegrable_of_deg`.)
        – POSITIVE (`u − εₘ > 0`, hence `0 < u`): the window is the forward interval `Ioc 0 (u−εₘ)`
          and the J4-383 core `sliceMeas_of_jointCont` applies DIRECTLY at ceiling `T := u` (the shift
          `s ↦ u − s` sends `s ∈ (0, u−εₘ]` to `τ = u − s ∈ [εₘ, u) ⊆ (0, u]`).

  •  (b) CEILING: since the positive regime uses `T := u` (unbounded), the joint-continuity carries
     must be available at EVERY ceiling.  Rather than a single FIXED-`T` strip datum, this file carries
     the EVERY-CEILING continuity family `∀ Tc, ContinuousOn … (Ioc 0 Tc ×ˢ univ)` — the honest
     every-ceiling analogue of the J4-387/388 `hAdomEvery` pattern, each member satisfiable by the
     J4-384 `JointContinuityAtoms.hHeatCont_of_boxes` / `hSecCont_of_boxes`-style box-glue at ceiling
     `Tc`.  The helper consumes only the `Tc := u` member.

  •  (c) FIRST FACTOR: the `hLapS` first factor is `fun τ z => laplaceBeltrami g gi (fun x => W τ x z) 0`
     — the FULL Laplace–Beltrami slice — which DIFFERS from the J4-383 `hmeas2` first factor
     `witnessSecondXDeriv g gi hChr hK S a b i τ z` (a single second-`x`-derivative component, per
     `i : Fin n`).  But `sliceMeas_of_jointCont` is GENERIC in the first factor `Φ`, so the route is
     identical; only the concrete joint-continuity ATOM differs (a `laplaceBeltrami`-slice continuity
     in place of the `witnessSecondXDeriv`-component continuity).  There is also no `i`-index and only
     the single forward window (no separate `Hi` window), so the `hLapS` carry is strictly simpler than
     the J4-383 `hmeas2Lo`/`hmeas2Hi` pair.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE PROVIDES.
  •  `pairingSlice_aesm` — ★★★ THE DICHOTOMY HELPER (split-and-glue).  For ARBITRARY `u`, the s-slice
     map `s ↦ ∫ z, Φ (u−s) z · Ψ s z` on `uIoc 0 (u−εₘ)` is `AEStronglyMeasurable`, from
     {Levi vanishing `hΨzero`} + {ceiling-`u` joint continuities of `Φ`, `Ψ`}, via the DEGENERATE
     `a.e.`-zero branch + the POSITIVE `sliceMeas_of_jointCont` branch.  Generic in `Φ`, `Ψ`.
  •  `hmeasHeatLevi_allU` — the `hES_all` / `hES_hypothesis_light` `hmeas` carry
     (`Φ := heatOp g gi W`), from `pairingSlice_aesm` + the every-ceiling `hHeatContEvery` / `hBcontEvery`.
  •  `hmeasLapLevi_allU` — the `hLapS_all` / `hLapS_all_capped` `hmeas` carry
     (`Φ := laplaceBeltrami-slice`), from `pairingSlice_aesm` + the every-ceiling `hLapContEvery` /
     `hBcontEvery`.
  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliceMeasurability
import QIQTH.ESLegWidening

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerMeasFubini QIQTH.LaplaceBeltrami
open scoped Interval Topology BigOperators

namespace QIQTH.AllUSliceMeas

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE DICHOTOMY HELPER (split-and-glue) — the arbitrary-`u` s-slice ae-strong-measurability.
    ############################################################################### -/

/-- **★★★ `pairingSlice_aesm` — THE DICHOTOMY HELPER.**  For ARBITRARY `u : ℝ`, the pairing s-slice
    map `s ↦ ∫ z, Φ (u−s) z · Ψ s z` is `AEStronglyMeasurable` on the window `uIoc 0 (u−εₘ)`, from
    the banked Levi-source vanishing `hΨzero` (`Ψ s z = 0` for `s ≤ 0`) and the ceiling-`u` joint
    continuities of `Φ` and `Ψ` on `Ioc 0 u ×ˢ univ`.

    Route — the DICHOTOMY `rcases le_or_gt (u − εₘ) 0`:
    •  DEGENERATE (`u − εₘ ≤ 0`): `uIoc 0 (u−εₘ) = Ioc (u−εₘ) 0 ⊆ {s ≤ 0}`; on `{s ≤ 0}` the factor
       `Ψ s z = 0`, so the whole `z`-integral is `0` — the s-slice map is `a.e.`-CONSTANT `0`,
       `AEStronglyMeasurable` via `aestronglyMeasurable_const.congr`.
    •  POSITIVE (`u − εₘ > 0`, hence `0 < u`): the window is `Ioc 0 (u−εₘ)`; the J4-383 reusable core
       `SliceMeasurability.sliceMeas_of_jointCont` applies at ceiling `T := u` (`hmaps`: for
       `s ∈ (0, u−εₘ]`, `u − s ∈ [εₘ, u) ⊆ (0, u]`; `hsub`: `Ioc 0 (u−εₘ) ⊆ Ioc 0 u`).

    Generic in `Φ`, `Ψ`.  Carries: `hεₘ` (`0 < εₘ`), `hΨzero` (banked Levi vanishing), the two
    ceiling-`u` joint-continuity strips.  ⚠ NOT `a₁ = R/6`. -/
theorem pairingSlice_aesm (Φ Ψ : ℝ → Point n → ℝ) (u εₘ : ℝ) (hεₘ : 0 < εₘ)
    (hΨzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, Ψ s z = 0)
    (hΦcont : ContinuousOn (fun p : ℝ × Point n => Φ p.1 p.2)
      (Set.Ioc 0 u ×ˢ (Set.univ : Set (Point n))))
    (hΨcont : ContinuousOn (fun p : ℝ × Point n => Ψ p.1 p.2)
      (Set.Ioc 0 u ×ˢ (Set.univ : Set (Point n)))) :
    AEStronglyMeasurable (fun s => ∫ z, Φ (u - s) z * Ψ s z)
      ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - εₘ))) := by
  rcases le_or_gt (u - εₘ) 0 with hdeg | hpos
  · -- DEGENERATE branch: window ⊆ {s ≤ 0}, slice map is a.e.-constant 0.
    have h0 : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - εₘ))) := aestronglyMeasurable_const
    refine h0.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hub : s ∈ Set.Ioc (min 0 (u - εₘ)) (max 0 (u - εₘ)) := hs
    have hs0 : s ≤ 0 := by
      have h2 : s ≤ max 0 (u - εₘ) := hub.2
      rwa [max_eq_left hdeg] at h2
    have hzeroFun : (fun z => Φ (u - s) z * Ψ s z) = fun _ => (0 : ℝ) := by
      funext z; rw [hΨzero s hs0 z, mul_zero]
    have hI0 : (∫ z, Φ (u - s) z * Ψ s z) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    exact hI0.symm
  · -- POSITIVE branch: forward window Ioc 0 (u−εₘ), core at ceiling T := u.
    have hu0 : 0 < u := by linarith
    have hIeq : Set.uIoc 0 (u - εₘ) = Set.Ioc 0 (u - εₘ) :=
      Set.uIoc_of_le (le_of_lt hpos)
    rw [hIeq]
    have hmaps : ∀ s ∈ Set.Ioc (0 : ℝ) (u - εₘ), (0 : ℝ) < u - s ∧ u - s ≤ u := by
      intro s hs
      exact ⟨by linarith [hs.2, hεₘ], by linarith [hs.1]⟩
    have hsub : Set.Ioc (0 : ℝ) (u - εₘ) ⊆ Set.Ioc 0 u :=
      Set.Ioc_subset_Ioc_right (by linarith)
    exact QIQTH.SliceMeasurability.sliceMeas_of_jointCont Φ Ψ u u
      (Set.Ioc 0 (u - εₘ)) measurableSet_Ioc hmaps hsub hΦcont hΨcont

/-! ###############################################################################
    ### (E·hES) — the `∀ (m u)` heat-operator · Levi slice measurability carry.
    ############################################################################### -/

/-- **★★ `hmeasHeatLevi_allU` — THE `hES_all` / `hES_hypothesis_light` `hmeas` CARRY.**  The
    `∀ (m u)` s-slice ae-strong-measurability of the `heatOp · leviSeries` pairing on
    `uIoc 0 (u − epsSeq m)`, for EVERY `u : ℝ`, discharged to the J4-383 core + Levi vanishing +
    the every-ceiling joint-continuity families.  A one-line-per-`(m,u)` instantiation of
    `pairingSlice_aesm` at `Φ := heatOp g gi W`, `Ψ := leviSeries (heatOp g gi W)`,
    ceiling member `Tc := u`.

    Honest carries: `hFzero` (banked Levi source vanishing), `hHeatContEvery` (per-ceiling heat-operator
    joint continuity — the J4-384 `hHeatCont_of_boxes` output at each `Tc`), `hBcontEvery` (per-ceiling
    Levi-series joint continuity — the banked `hBcont` at each `Tc`).  ⚠ NOT `a₁ = R/6`. -/
theorem hmeasHeatLevi_allU (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hHeatContEvery : ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n))))
    (hBcontEvery : ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u
  exact pairingSlice_aesm
    (fun τ z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    u (epsSeq m) (epsSeq_pos m) hFzero (hHeatContEvery u) (hBcontEvery u)

/-! ###############################################################################
    ### (E·hLapS) — the `∀ (m u)` laplaceBeltrami-slice · Levi slice measurability carry.
    ############################################################################### -/

/-- **★★ `hmeasLapLevi_allU` — THE `hLapS_all` / `hLapS_all_capped` `hmeas` CARRY.**  The `∀ (m u)`
    s-slice ae-strong-measurability of the `laplaceBeltrami-slice · leviSeries` pairing on
    `uIoc 0 (u − epsSeq m)`, for EVERY `u : ℝ`.  Identical route to `hmeasHeatLevi_allU` with the FULL
    Laplace–Beltrami slice `Φ := fun τ z => laplaceBeltrami g gi (fun x => W τ x z) 0` in place of the
    heat operator (difference (c) of the shape-comparison verdict — a distinct joint-continuity ATOM,
    same generic core).

    Honest carries: `hFzero` (banked Levi source vanishing), `hLapContEvery` (per-ceiling
    laplaceBeltrami-slice joint continuity), `hBcontEvery` (per-ceiling Levi-series joint continuity).
    ⚠ NOT `a₁ = R/6`. -/
theorem hmeasLapLevi_allU (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hLapContEvery : ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n))))
    (hBcontEvery : ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u
  exact pairingSlice_aesm
    (fun τ z => laplaceBeltrami g gi
      (fun x => vanVleckGatedWitness g gi hChr hK S a b τ x z) 0)
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    u (epsSeq m) (epsSeq_pos m) hFzero (hLapContEvery u) (hBcontEvery u)

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @pairingSlice_aesm
#check @hmeasHeatLevi_allU
#check @hmeasLapLevi_allU

#print axioms pairingSlice_aesm
#print axioms hmeasHeatLevi_allU
#print axioms hmeasLapLevi_allU

end QIQTH.AllUSliceMeas
