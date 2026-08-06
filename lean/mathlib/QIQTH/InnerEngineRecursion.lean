/-
  InnerEngineRecursion — J4-291: the INNER-engine RECURSION step (the two per-level carries of the
  OUTER `iterE` engine, `C-meas` + `C-cont`).  Feeds `QIQTH.IterEEngineWiring`
  (`iterE_succ_jointContinuousOn_wired` / `iterE_jointContinuousOn_wired`), whose OUTER
  dominated-continuity step consumes, at each level `k`, two honest carries:
    • (C-meas) `hmeas` — for each `p` on the compact, the `AEStronglyMeasurable`ity on `Ioc 0 1` of
        `u ↦ ∫ w, E (p.1 − p.1·u) p.2 w · iterE E k (p.1·u) w 0`;
    • (C-cont) `hcont` — for a.e. `u`, the joint `(s,z)`-continuity on the compact of the same inner
        spatial integral.
  This file DISCHARGES (C-meas) OUTRIGHT from the single base measurability `hEmeas` (R2), and WIRES
  the INNER engine `IterEContinuity.heatConvSpatial_jointContinuousOn_of_dominated` for (C-cont),
  deriving its measurability slot from `hEmeas` and carrying the two GENUINE analytic slots — the
  spatial dominator and the integrand's joint `(s,z)`-continuity — as precisely-named hypotheses (R1).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity / wiring brick.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE SLOT-REQUIREMENT MAP (the load-bearing recon).  At level `k` the inner integrand is
        `w ↦ E (s − s·u) z w · iterE E k (s·u) w 0`   (here `p = (s,z)`, `u ∈ Ioc 0 1` fixed).
     The INNER engine `heatConvSpatial_jointContinuousOn_of_dominated E (iterE E k) t₁ t₂ R u bnd`
     needs FOUR slots, whose exact continuity/measurability content is:

       (S-meas)  `∀ p ∈ K, AEStronglyMeasurable (fun w => E (s−s·u) z w · iterE E k (s·u) w 0) volume`.
                 ★ DERIVABLE — exactly `IterEEngineWiring.convStepIntegrand_aestronglyMeasurable`
                   (`hEmeas`-slice for the `E` factor · `HeatResidualBound.iterE_zmeas` for the
                   `iterE` factor).  BUILT here (no carry).

       (S-dom)   an `Integrable` spatial dominator `bnd : Point n → ℝ`, `p`-UNIFORM on `K`, with
                 `∀ p ∈ K, ∀ᵐ w, ‖E (s−s·u) z w · iterE E k (s·u) w 0‖ ≤ bnd w`.
                 ⚠ GENUINE CARRY — the `W1` pointwise majorant
                   `(C·baseKernelW κ 0 (s−s·u) z w)·(C^k·iterKernelW κ 0 k (s·u) w 0)` DEPENDS on
                   `p = (s,z)`; a `p`-uniform spatial dominator is the (R-dom) uniform-Gaussian carry.

       (S-cont)  `∀ᵐ w, ContinuousOn (fun p => E (s−s·u) z w · iterE E k (s·u) w 0) K`.  Factors as a
                 `.mul` of TWO per-`w` continuities, and THIS is where the recursion's real walls sit:
                   • (Gap-A / `hcontE`) `∀ᵐ w, ContinuousOn (fun p => E (s−s·u) z w) K` — E's joint
                     `(time, FIRST-spatial)` continuity **at the SECOND spatial argument `= w`**
                     (`w` = the integration variable, ranging over ALL of space).  The BANKED base
                     (J4-288 chart-free capstone `hbase`) is the `(·,·,0)` SLICE only
                     (`fun p => E p.1 p.2 0`), so it does NOT cover general `w ≠ 0`.  ⇒ CARRY.
                   • (Gap-B / `hcontIter`) `∀ᵐ w, ContinuousOn (fun p => iterE E k (s·u) w 0) K` — this
                     depends on `p` through the TIME `s·u` only (`w`,`0` fixed), i.e. `iterE E k`'s
                     TIME-continuity at the fixed spatial point `(w, 0)` for `w` over ALL of space.
                     The OUTER induction hypothesis supplies `iterE E k`'s joint `(time, FIRST-spatial)`
                     continuity on the compact BALL `closedBall 0 R` in the first spatial slot — NOT at
                     first spatial `= w` for `w` outside the ball.  ⇒ CARRY.

     NET.  (S-meas) is DERIVED from `hEmeas`.  (S-dom), (Gap-A), (Gap-B) are the three genuine analytic
     carries — none is the conclusion, each satisfiable (Gaussian domination; the base-`w`-general and
     ball-free versions of the J4-285/287/288 chain and the outer IH, which the base-`0`-anchored
     constructions do NOT hand over for free — a parameterization/consult item).

  ── WHAT LANDS (all DERIVED / soundly WIRED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (R2 / C-meas) `convStepIntegral_u_aestronglyMeasurable` — ★ the parametric-Fubini
        `u`-measurability, DISCHARGED OUTRIGHT (no carry) from `hEmeas`: the joint `(u,w)`-strong
        measurability of the integrand (`hEmeas`-composition · `iterE_joint_stronglyMeasurable`),
        integrated out by `AEStronglyMeasurable.integral_prod_right'`.  Holds for EVERY `p`.

    * (R2-feed) `convStepIntegral_u_aestronglyMeasurable_wired` — the same, packaged in the EXACT
        `∀ k, ∀ p ∈ K, …(iterE E (k+1))…` shape consumed by `iterE_jointContinuousOn_wired`'s `hmeas`
        argument.  Fully discharges the C-meas carry of the OUTER engine.

    * (R1a / C-cont, single `u`) `innerStep_cont_of_slots` — the INNER-engine instantiation at a fixed
        `u`: `heatConvSpatial_jointContinuousOn_of_dominated E (iterE E k)` with (S-meas) DERIVED from
        `hEmeas` and (S-dom)+(Gap-A)+(Gap-B) carried; `.mul` joins the two per-`w` continuities.

    * (R1b / C-cont, a.e. `u`) `innerStep_cont_ae` — the a.e.-`u` packaging matching the OUTER engine's
        `hcont` argument, from the `∀ᵐ u` families of the same three carries.

    * (R3) `innerRecursion_step_reduced` — the composition: feeds R2 (`hmeas`) and R1b (`hcont`) into
        `IterEEngineWiring.iterE_succ_jointContinuousOn_wired`, so the OUTER-engine STEP output
        `ContinuousOn (iterE E (k+1))` is reduced to the OUTER bounds (`hEbound`/`hInt`) + the three
        INNER carries.  Exhibits the exact residual surface.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     The three INNER carries above: `hbnd_int`/`hbound` (S-dom, the uniform Gaussian spatial dominator),
     `hcontE` (Gap-A, E's continuity at general second spatial argument `w`), `hcontIter` (Gap-B,
     `iterE E k`'s time-continuity at first spatial argument `w` over all of space).  Gap-A/Gap-B are
     the genuine recursion walls: the banked continuity is `(·,·,0)`-slice- and ball-anchored, so the
     general-`w`/ball-free versions do not follow from the banked base + IH without a parameterized
     re-run (or a two-point/homogeneity argument) — this is the bankable intel for a possible consult.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.IterEEngineWiring
import QIQTH.IterEContinuity
import QIQTH.IterEMeasurable

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.IterEContinuity QIQTH.IterEEngineWiring
open scoped Topology

namespace QIQTH.InnerEngineRecursion

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (R2 / C-meas) The parametric-Fubini `u`-measurability — DISCHARGED from `hEmeas`.
    ############################################################################### -/

/-- **(R2 / C-meas) `convStepIntegral_u_aestronglyMeasurable`.**  The OUTER engine's `hmeas` slot at the
    actual integrand, DISCHARGED OUTRIGHT (no analytic carry) from the single base joint measurability
    `hEmeas`: the `u`-integral
        `u ↦ ∫ w, E (p.1 − p.1·u) p.2 w · iterE E k (p.1·u) w 0`
    is `AEStronglyMeasurable` on `Ioc 0 1` (indeed on `ℝ`), for EVERY `p` and level `k ≥ 1`.  Route: the
    joint `(u,w)`-strong measurability of the integrand — the `E` factor is `hEmeas` precomposed with
    the measurable section `(u,w) ↦ (p.1 − p.1·u, p.2, w)`, the `iterE` factor is
    `HeatResidualBound.iterE_joint_stronglyMeasurable` precomposed with `(u,w) ↦ (p.1·u, w)` — then
    `AEStronglyMeasurable.integral_prod_right'` integrates `w` out.  NOT `a₁ = R/6`. -/
theorem convStepIntegral_u_aestronglyMeasurable
    (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (p : ℝ × Point n) :
    AEStronglyMeasurable
      (fun u => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  -- The `E` factor as a joint `(u,w)`-strongly-measurable function.
  have hA : StronglyMeasurable
      (fun q : ℝ × Point n => E (p.1 - p.1 * q.1) p.2 q.2) :=
    hEmeas.comp_measurable
      ((measurable_const.sub (measurable_const.mul measurable_fst)).prodMk
        (measurable_const.prodMk measurable_snd))
  -- The `iterE E k` factor, via the measure-free joint carrier.
  have hB : StronglyMeasurable
      (fun q : ℝ × Point n => iterE E k (p.1 * q.1) q.2 0) :=
    (iterE_joint_stronglyMeasurable E hEmeas k hk 0).comp_measurable
      ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hmul : StronglyMeasurable
      (fun q : ℝ × Point n => E (p.1 - p.1 * q.1) p.2 q.2 * iterE E k (p.1 * q.1) q.2 0) :=
    hA.mul hB
  exact
    (hmul.aestronglyMeasurable
      (μ := (volume.restrict (Set.Ioc (0:ℝ) 1)).prod (volume : Measure (Point n)))).integral_prod_right'

/-- **(R2-feed) `convStepIntegral_u_aestronglyMeasurable_wired`.**  The R2 measurability packaged in the
    EXACT shape of the `hmeas` argument of `IterEEngineWiring.iterE_jointContinuousOn_wired`
    (`∀ k, ∀ p ∈ K, …(iterE E (k+1))…`).  Fully DISCHARGES the OUTER engine's `C-meas` carry from
    `hEmeas` alone.  NOT `a₁ = R/6`. -/
theorem convStepIntegral_u_aestronglyMeasurable_wired
    (E : ℝ → Point n → Point n → ℝ) (t₁ t₂ R : ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    ∀ k : ℕ, ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable
        (fun u => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
  fun k p _ =>
    convStepIntegral_u_aestronglyMeasurable E (Nat.succ_le_succ (Nat.zero_le k)) hEmeas p

/-! ###############################################################################
    ## (R1a / C-cont) The INNER-engine instantiation at a FIXED `u`.
    ############################################################################### -/

/-- **(R1a / C-cont, single `u`) `innerStep_cont_of_slots`.**  For a FIXED `u`, the joint `(s,z)`
    continuity on the compact `Icc t₁ t₂ ×ˢ closedBall 0 R` of the inner spatial integral
        `p ↦ ∫ w, E (p.1 − p.1·u) p.2 w · iterE E k (p.1·u) w 0`,
    by `IterEContinuity.heatConvSpatial_jointContinuousOn_of_dominated` at `A = E`, `B = iterE E k`.
    The (S-meas) slot is DERIVED from `hEmeas` (`convStepIntegrand_aestronglyMeasurable`); the three
    genuine analytic slots are carried:
      • `hbnd_int` + `hbound` — (S-dom) the `p`-uniform integrable spatial dominator;
      • `hcontE`   — (Gap-A) `∀ᵐ w`, `(s,z) ↦ E (s−s·u) z w` continuous — E at general 2nd arg `w`;
      • `hcontIter`— (Gap-B) `∀ᵐ w`, `(s,z) ↦ iterE E k (s·u) w 0` continuous — `iterE` time-continuity
                     at 1st spatial arg `w`.
    `.mul` joins the two per-`w` continuities into the integrand's (S-cont) slot.  None of the carries
    is the conclusion.  NOT `a₁ = R/6`. -/
theorem innerStep_cont_of_slots
    (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k) (t₁ t₂ R u : ℝ)
    (bnd : Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hbnd_int : Integrable bnd volume)
    (hbound : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      ∀ᵐ w ∂volume, ‖E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0‖ ≤ bnd w)
    (hcontE : ∀ᵐ w ∂volume, ContinuousOn
      (fun p : ℝ × Point n => E (p.1 - p.1 * u) p.2 w)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcontIter : ∀ᵐ w ∂volume, ContinuousOn
      (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine heatConvSpatial_jointContinuousOn_of_dominated E (iterE E k) t₁ t₂ R u bnd
    ?_ hbound hbnd_int ?_
  · intro p _hp
    exact convStepIntegrand_aestronglyMeasurable E hk (p.1 - p.1 * u) (p.1 * u) hEmeas p.2
  · filter_upwards [hcontE, hcontIter] with w hcE hcI
    exact hcE.mul hcI

/-! ###############################################################################
    ## (R1b / C-cont) The a.e.-`u` packaging (the OUTER engine's `hcont` argument).
    ############################################################################### -/

/-- **(R1b / C-cont, a.e. `u`) `innerStep_cont_ae`.**  The a.e.-`u` inner joint continuity in the EXACT
    shape consumed by `IterEEngineWiring.iterE_succ_jointContinuousOn_wired`'s `hcont` argument, from the
    `∀ᵐ u` families of the three INNER carries (S-dom, Gap-A, Gap-B).  Each fibre is discharged by
    `innerStep_cont_of_slots` (S-meas derived from `hEmeas`).  None of the carries is the conclusion.
    NOT `a₁ = R/6`. -/
theorem innerStep_cont_ae
    (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k) (t₁ t₂ R : ℝ)
    (bnd : ℝ → Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (hbnd_int : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume)
    (hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
        ∀ᵐ w ∂volume, ‖E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0‖ ≤ bnd u w)
    (hcontE : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂volume, ContinuousOn
        (fun p : ℝ × Point n => E (p.1 - p.1 * u) p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcontIter : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂volume, ContinuousOn
        (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  filter_upwards [hbnd_int, hbound, hcontE, hcontIter] with u hbi hb hcE hcI
  exact innerStep_cont_of_slots E hk t₁ t₂ R u (bnd u) hEmeas hbi hb hcE hcI

/-! ###############################################################################
    ## (R3) The OUTER-engine STEP reduced to the INNER carries.
    ############################################################################### -/

/-- **(R3) `innerRecursion_step_reduced`.**  The composition capstone: feeds R2 (`hmeas`, DISCHARGED
    from `hEmeas`) and R1b (`hcont`) into `IterEEngineWiring.iterE_succ_jointContinuousOn_wired`,
    reducing the OUTER-engine STEP output
        `ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0) (Icc t₁ t₂ ×ˢ closedBall 0 R)`
    to the OUTER bounds (`hEbound` — the width-`κ` one-step residual bound / C4c wall — and `hInt`) plus
    the three INNER carries (`hbnd_int`/`hbound` = S-dom, `hcontE` = Gap-A, `hcontIter` = Gap-B).  This
    exhibits the EXACT residual surface of one recursion rung; none of the carries is the conclusion.
    NOT `a₁ = R/6`. -/
theorem innerRecursion_step_reduced
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (bnd : ℝ → Point n → ℝ)
    (hbnd_int : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume)
    (hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
        ∀ᵐ w ∂volume, ‖E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0‖ ≤ bnd u w)
    (hcontE : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂volume, ContinuousOn
        (fun p : ℝ × Point n => E (p.1 - p.1 * u) p.2 w)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcontIter : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ᵐ w ∂volume, ContinuousOn
        (fun p : ℝ × Point n => iterE E k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  iterE_succ_jointContinuousOn_wired E κ C hκ hC hk t₁ t₂ R ht₁ hEbound hInt
    (fun p _hp => convStepIntegral_u_aestronglyMeasurable E hk hEmeas p)
    (innerStep_cont_ae E hk t₁ t₂ R bnd hEmeas hbnd_int hbound hcontE hcontIter)

#check @convStepIntegral_u_aestronglyMeasurable
#check @convStepIntegral_u_aestronglyMeasurable_wired
#check @innerStep_cont_of_slots
#check @innerStep_cont_ae
#check @innerRecursion_step_reduced

end QIQTH.InnerEngineRecursion

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.InnerEngineRecursion
#print axioms convStepIntegral_u_aestronglyMeasurable
#print axioms convStepIntegral_u_aestronglyMeasurable_wired
#print axioms innerStep_cont_of_slots
#print axioms innerStep_cont_ae
#print axioms innerRecursion_step_reduced
end AxiomChecks
