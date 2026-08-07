/-
  JointContinuityAtoms — J4-384: the JOINT-CONTINUITY ATOMS for the s-slice MEASURABILITY
  supplier (`QIQTH.SliceMeasurability`, census pile (v)).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  This file supplies the positive-time STRIP joint-continuity
  data (`hHeatCont`, `hSecCont`) that `QIQTH.SliceMeasurability`'s four census facts
  (`hmeasLo_slice`, `hmeasHi_slice`, `hmeas2Lo_slice`, `hmeas2Hi_slice`) still consume as carried
  hypotheses — as genuine (std-3, axiom-free) theorems, built by the local-to-global GLUING of the
  ALREADY-BANKED positive-time-compact box continuities (`Icc (τ₀/2) T ×ˢ closedBall 0 R`, the
  `HeatOpWitnessContinuity` / `ParametrixPartsContinuity` box shape).  No `sorry`, no new axioms,
  no `:= True`, no vacuous or unsatisfiable hypotheses, no conclusion-in-disguise.

  ## THE STRUCTURAL ROUTE — local boxability of the positive-time strip.

    The strip `Ioc 0 T ×ˢ univ` is LOCALLY BOXABLE: at any `(τ,z)` with `0 < τ ≤ T`, the compact
    box `Icc (τ/2) T ×ˢ closedBall 0 (‖z‖+1)` is a NEIGHBOURHOOD WITHIN THE STRIP of `(τ,z)`
    (witnessed by the open set `Ioi (τ/2) ×ˢ ball 0 (‖z‖+1)`, whose intersection with the strip
    lands in the box: `q.1 > τ/2 ∧ q.1 ≤ T ⟹ q.1 ∈ Icc (τ/2) T`, and `ball ⊆ closedBall`).  The
    `τ/2` floor keeps the box strictly inside positive time, so there is NO `τ → 0` Gaussian
    blow-up.  `ContinuousOn = ∀ p, ContinuousWithinAt`; the box `ContinuousOn` gives
    `ContinuousWithinAt f box p`, and `ContinuousWithinAt.mono_of_mem_nhdsWithin` (with the box a
    within-nbhd of `p`) upgrades it to `ContinuousWithinAt f strip p`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `stripContOn_of_boxes` — ★★★ THE GENERIC LIFT.  For ANY `f : ℝ × Point n → E` (E a
      topological space), a positive-time-compact box `ContinuousOn` FAMILY
      `∀ τ₀ ∈ Ioc 0 T, ∀ R, ContinuousOn f (Icc (τ₀/2) T ×ˢ closedBall 0 R)` glues to the full
      strip `ContinuousOn f (Ioc 0 T ×ˢ univ)`.  Pure topology — the local-to-global gluing.  This
      is the reusable ATOM; the box family is a genuine (compact, positive-time-bounded, finite
      spatial radius) input, strictly weaker per-instance than the strip conclusion — NOT the
      conclusion in disguise (a single box ≠ the strip; the content is the gluing).

    * `hHeatCont_of_boxes` — ★★ the `hHeatCont` STRIP fact for the gated van-Vleck heat operator,
      by instantiating `stripContOn_of_boxes` at
      `f = fun p => heatOp g gi (vanVleckGatedWitness …) p.1 0 p.2`.  The box family is the honest
      carry — satisfiable via the banked `HeatOpWitnessContinuity.heatOpWitness_jointContinuousOn_of_identity`
      (gate-local residual identity + explicit-formula continuity on each positive-time box).

    * `hSecCont_of_boxes` — ★★ the `hSecCont` STRIP fact for the gated witness second-`x`-derivative
      (per `i : Fin n`), by the same instantiation at
      `f = fun p => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2`.  Box family carried; satisfiable
      via the banked `ParametrixPartsContinuity` spatial-derivative box continuities.

  ── HONEST CARRIED INPUT (satisfiable, non-vacuous, NEVER the conclusion).
    * the positive-time-compact box `ContinuousOn` FAMILY (`hboxes`) — one `ContinuousOn` on each
      `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀`).  This is the EXACT `HeatOpWitnessContinuity`
      box shape (`Icc t₁ t₂ ×ˢ closedBall 0 R`, `0 < t₁`); each member is dischargeable by the
      banked `heatOpWitness_jointContinuousOn_of_identity` / `ParametrixPartsContinuity` bricks
      (themselves carrying the gate-local identity + explicit-formula continuity — the genuine
      remaining analytic work, NOT this file's concern).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerMeasFubini
import QIQTH.AmplitudePackage

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.InnerMeasFubini
open scoped Interval Topology BigOperators

namespace QIQTH.JointContinuityAtoms

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE GENERIC LIFT — positive-time-compact boxes ⟹ the full positive-time strip.
    ############################################################################### -/

/-- **★★★ `stripContOn_of_boxes` — THE GENERIC LOCAL-TO-GLOBAL LIFT.**  For any function
    `f : ℝ × Point n → E` (`E` a topological space), if `f` is jointly `ContinuousOn` EVERY
    positive-time-compact box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (for `τ₀ ∈ Ioc 0 T` and every radius
    `R`), then `f` is jointly `ContinuousOn` the full positive-time strip `Ioc 0 T ×ˢ univ`.

    Route (pure topology).  `ContinuousOn` = `∀ p, ContinuousWithinAt`.  At `p = (τ,z)` with
    `0 < τ ≤ T` we take the box at `τ₀ = τ`, `R = ‖z‖+1`:  `p` lies in it (`τ/2 ≤ τ ≤ T`,
    `‖z‖ ≤ ‖z‖+1`), so the box `ContinuousOn` yields `ContinuousWithinAt f box p`.  The box is a
    within-strip neighbourhood of `p`, witnessed by the OPEN set `Ioi (τ/2) ×ˢ ball 0 R` whose
    intersection with the strip lands inside the box (`q.1 > τ/2 ∧ q.1 ≤ T ⟹ q.1 ∈ Icc (τ/2) T`;
    `ball ⊆ closedBall`).  `ContinuousWithinAt.mono_of_mem_nhdsWithin` upgrades to the strip.

    The box family is a genuine, satisfiable input (positive-time-bounded, finite-radius compacts —
    the banked box shape); it is per-instance strictly weaker than, and NOT, the strip conclusion.
    NOT `a₁ = R/6`. -/
theorem stripContOn_of_boxes {E : Type*} [TopologicalSpace E]
    (f : ℝ × Point n → E) (T : ℝ)
    (hboxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn f (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn f (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) := by
  intro p hp
  have hτ : p.1 ∈ Set.Ioc (0 : ℝ) T := hp.1
  have hτpos : 0 < p.1 := hτ.1
  have hτT : p.1 ≤ T := hτ.2
  set R : ℝ := ‖p.2‖ + 1 with hR
  have hbox := hboxes p.1 hτ R
  -- `p` lies in the box.
  have hpbox : p ∈ Set.Icc (p.1 / 2) T ×ˢ Metric.closedBall (0 : Point n) R := by
    refine ⟨⟨by linarith, hτT⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, hR]
    linarith
  have hcwa_box : ContinuousWithinAt f
      (Set.Icc (p.1 / 2) T ×ˢ Metric.closedBall (0 : Point n) R) p :=
    hbox.continuousWithinAt hpbox
  -- the box is a within-strip neighbourhood of `p`.
  have hmem : (Set.Icc (p.1 / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      ∈ nhdsWithin p (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioi (p.1 / 2) ×ˢ Metric.ball (0 : Point n) R,
      isOpen_Ioi.prod Metric.isOpen_ball, ?_, ?_⟩
    · refine ⟨Set.mem_Ioi.mpr (by linarith), ?_⟩
      rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
    · intro q hq
      obtain ⟨hqO, hqS⟩ := hq
      refine ⟨⟨le_of_lt (Set.mem_Ioi.mp hqO.1), hqS.1.2⟩,
        Metric.ball_subset_closedBall hqO.2⟩
  exact hcwa_box.mono_of_mem_nhdsWithin hmem

/-! ###############################################################################
    ### THE TWO CONCRETE STRIP FACTS — `hHeatCont` and `hSecCont`.
    ############################################################################### -/

/-- **★★ `hHeatCont_of_boxes` — THE `hHeatCont` STRIP FACT.**  Joint `(τ,z)`-continuity of the gated
    van-Vleck heat operator `p ↦ heatOp g gi (vanVleckGatedWitness …) p.1 0 p.2` on the full
    positive-time strip `Ioc 0 T ×ˢ univ`, from its continuity on each positive-time-compact box
    (the carried `hboxes`, the banked `HeatOpWitnessContinuity` box shape).  A one-line instantiation
    of `stripContOn_of_boxes`.  This is EXACTLY the `hHeatCont` carry consumed by
    `SliceMeasurability.hmeasLo_slice` / `hmeasHi_slice`.  NOT `a₁ = R/6`. -/
theorem hHeatCont_of_boxes (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hboxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  stripContOn_of_boxes _ T hboxes

/-- **★★ `hSecCont_of_boxes` — THE `hSecCont` STRIP FACT.**  Joint `(τ,z)`-continuity of the gated
    witness second-`x`-derivative `p ↦ witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2` on the full
    positive-time strip `Ioc 0 T ×ˢ univ`, per `i : Fin n`, from its continuity on each
    positive-time-compact box (the carried `hboxes`, the banked `ParametrixPartsContinuity` spatial
    box shape).  A one-line per-`i` instantiation of `stripContOn_of_boxes`.  This is EXACTLY the
    `hSecCont` carry consumed by `SliceMeasurability.hmeas2Lo_slice` / `hmeas2Hi_slice`.
    NOT `a₁ = R/6`. -/
theorem hSecCont_of_boxes (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hboxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) := by
  intro i
  exact stripContOn_of_boxes _ T (hboxes i)

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @stripContOn_of_boxes
#check @hHeatCont_of_boxes
#check @hSecCont_of_boxes

#print axioms stripContOn_of_boxes
#print axioms hHeatCont_of_boxes
#print axioms hSecCont_of_boxes

end QIQTH.JointContinuityAtoms
