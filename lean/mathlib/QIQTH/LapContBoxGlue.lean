/-
  LapContBoxGlue — J4-390: the laplaceBeltrami-slice BOX GLUE closing the `r2` continuity atom of
  census pile (ix) — the `hLapContEvery` carry of `QIQTH.AllUSliceMeas.hmeasLapLevi_allU`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only discharges the `hLapContEvery` joint-continuity
  carry of the `∀ (m u)` laplaceBeltrami-slice s-slice ae-strong-measurability fact, down to the
  honest positive-time-compact BOX continuity family (the banked `ParametrixPartsContinuity` route),
  via the already-banked GENERIC local-to-global lift `QIQTH.JointContinuityAtoms.stripContOn_of_boxes`
  (J4-384).  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous /
  unsatisfiable hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing file
  edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE PROVIDES.

    * `hLapCont_of_boxes` — ★★ (L1) the STRIP fact for the laplaceBeltrami slice
      `p ↦ laplaceBeltrami g gi (fun x => vanVleckGatedWitness … p.1 x p.2) 0` on the full positive-time
      strip `Ioc 0 T ×ˢ univ`, from its continuity on each positive-time-compact box
      `Icc (τ₀/2) T ×ˢ closedBall 0 R`.  A one-line instantiation of the banked GENERIC lift
      `QIQTH.JointContinuityAtoms.stripContOn_of_boxes` — the EXACT mirror of that file's
      `hSecCont_of_boxes`, with the FULL Laplace–Beltrami slice in place of the single
      `witnessSecondXDeriv` component (difference (c) of the AllUSliceMeas shape-comparison verdict).
      The carried box family is the honest input, dischargeable via the banked
      `QIQTH.ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts` route (the
      `laplaceBeltrami` unfold into first/second spatial-partial continuities on each positive-time
      box); it is per-instance strictly weaker than, and NOT, the strip conclusion.

    * `hLapContEvery_of_boxes` — ★★ (L2) the EVERY-CEILING version matching the EXACT `hLapContEvery`
      carry shape of `AllUSliceMeas.hmeasLapLevi_allU` (`∀ Tc, ContinuousOn … (Ioc 0 Tc ×ˢ univ)`).
      From a single `Tc`-generic box family `∀ Tc, ∀ τ₀ ∈ Ioc 0 Tc, ∀ R, …` (one carry serves all
      ceilings), by `hLapCont_of_boxes` at each `Tc`.

    * `hmeasLapLevi_from_boxes` — ★ (L3) the CONSOLIDATED statement: `AllUSliceMeas.hmeasLapLevi_allU`
      with its `hLapContEvery` carry DISCHARGED via `hLapContEvery_of_boxes`.  The `∀ (m u)`
      laplaceBeltrami-slice · Levi s-slice ae-strong-measurability, now resting on the box family
      (`hLapBoxes`) + the banked Levi vanishing (`hFzero`) + the every-ceiling Levi-series continuity
      (`hBcontEvery`) only.

  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JointContinuityAtoms
import QIQTH.AllUSliceMeas

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerMeasFubini QIQTH.LaplaceBeltrami
open scoped Interval Topology BigOperators

namespace QIQTH.LapContBoxGlue

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (L1) — the laplaceBeltrami-slice STRIP fact from the box family.
    ############################################################################### -/

/-- **★★ (L1) `hLapCont_of_boxes` — THE laplaceBeltrami-slice STRIP FACT.**  Joint `(τ,z)`-continuity
    of the gated van-Vleck laplaceBeltrami slice
    `p ↦ laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0` on the
    full positive-time strip `Ioc 0 T ×ˢ univ`, from its continuity on each positive-time-compact box
    `Icc (τ₀/2) T ×ˢ closedBall 0 R` (the carried `hboxes`, the banked `ParametrixPartsContinuity`
    laplaceBeltrami box shape).  A one-line instantiation of the banked GENERIC lift
    `QIQTH.JointContinuityAtoms.stripContOn_of_boxes` (J4-384) — the EXACT mirror of that file's
    `hSecCont_of_boxes`, with the full Laplace–Beltrami slice in place of the single
    `witnessSecondXDeriv` component (difference (c) of the `AllUSliceMeas` shape-comparison verdict).
    This is EXACTLY the fixed-`T` member of the `hLapContEvery` carry consumed by
    `AllUSliceMeas.hmeasLapLevi_allU`.  The box family is the honest, satisfiable carry (a
    positive-time-bounded finite-radius compact continuity, dischargeable via
    `ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts`); it is per-instance strictly
    weaker than, and NOT, the strip conclusion.  NOT `a₁ = R/6`. -/
theorem hLapCont_of_boxes (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hboxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  QIQTH.JointContinuityAtoms.stripContOn_of_boxes _ T hboxes

/-! ###############################################################################
    ### (L2) — the EVERY-CEILING version matching the `hLapContEvery` carry shape.
    ############################################################################### -/

/-- **★★ (L2) `hLapContEvery_of_boxes` — THE `hLapContEvery` CARRY.**  The EVERY-CEILING laplaceBeltrami
    slice joint continuity `∀ Tc, ContinuousOn … (Ioc 0 Tc ×ˢ univ)` — the EXACT shape of the
    `hLapContEvery` hypothesis consumed by `AllUSliceMeas.hmeasLapLevi_allU` — from a single
    `Tc`-generic positive-time-compact box family `∀ Tc, ∀ τ₀ ∈ Ioc 0 Tc, ∀ R, …` (one carry serves
    all ceilings), by `hLapCont_of_boxes` at each `Tc`.  The box family is the honest, satisfiable
    carry (the banked `ParametrixPartsContinuity` route at each ceiling); NOT the conclusion.
    NOT `a₁ = R/6`. -/
theorem hLapContEvery_of_boxes (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hboxes : ∀ Tc : ℝ, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) Tc, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
        (Set.Icc (τ₀ / 2) Tc ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n))) := by
  intro Tc
  exact hLapCont_of_boxes g gi hChr hK S a b Tc (hboxes Tc)

/-! ###############################################################################
    ### (L3) — the CONSOLIDATED `∀ (m u)` slice-measurability with `hLapContEvery` discharged.
    ############################################################################### -/

/-- **★ (L3) `hmeasLapLevi_from_boxes` — THE CONSOLIDATED SLICE-MEASURABILITY.**
    `AllUSliceMeas.hmeasLapLevi_allU` with its `hLapContEvery` joint-continuity carry DISCHARGED via
    `hLapContEvery_of_boxes`.  The `∀ (m u)` s-slice ae-strong-measurability of the
    `laplaceBeltrami-slice · leviSeries` pairing on `uIoc 0 (u − epsSeq m)` (for EVERY `u`), now resting
    on the honest per-ceiling laplaceBeltrami BOX family (`hLapBoxes`, dischargeable via
    `ParametrixPartsContinuity`) + the banked Levi source vanishing (`hFzero`) + the every-ceiling
    Levi-series joint continuity (`hBcontEvery`) ONLY — the `hLapContEvery` atom no longer appears.
    NOT `a₁ = R/6`. -/
theorem hmeasLapLevi_from_boxes (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hLapBoxes : ∀ Tc : ℝ, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) Tc, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
        (Set.Icc (τ₀ / 2) Tc ×ˢ Metric.closedBall (0 : Point n) R))
    (hBcontEvery : ∀ Tc : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 Tc ×ˢ (Set.univ : Set (Point n)))) :
    ∀ (m : ℕ) (u : ℝ), AEStronglyMeasurable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))) :=
  QIQTH.AllUSliceMeas.hmeasLapLevi_allU g gi hChr hK S a b hFzero
    (hLapContEvery_of_boxes g gi hChr hK S a b hLapBoxes) hBcontEvery

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @hLapCont_of_boxes
#check @hLapContEvery_of_boxes
#check @hmeasLapLevi_from_boxes

#print axioms hLapCont_of_boxes
#print axioms hLapContEvery_of_boxes
#print axioms hmeasLapLevi_from_boxes

end QIQTH.LapContBoxGlue
