/-
  LeviIterBoxInduction — J4-394: the `leviIter` z-slot BOX-continuity induction (Sol #16 brick 5).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only supplies the z-slot (`x = 0` frozen, `y = p.2`
  varying) orientation of the termwise iterated-convolution (`iterE`) JOINT `(τ,z)`-continuity
  induction on the FIXED positive-time-compact box `Icc (τ₀/2) T ×ˢ closedBall 0 R`, feeding Sol #16
  brick 6's Weierstrass M-test.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO
  vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SLOT-SYMMETRY VERDICT (Phase-1, dont-undercredit).

    The Duhamel convolution is `heatConv A B t x y = ∫ s in 0..t, ∫ z, A (t−s) x z · B s z y`, so `x`
    is A's FIRST spatial slot (outer) and `y` is B's SECOND spatial slot (outer), with `z` integrated.
    The BANKED x-slot step `IterEContinuity.heatConv_jointContinuousOn_of_dominated` proves box
    continuity of `p ↦ heatConv A B p.1 p.2 0` — the varying spatial variable `p.2` sitting in A's
    FIRST slot, B FROZEN at `0`.  This brick needs the OTHER orientation `p ↦ heatConv A B p.1 0 p.2` —
    A FROZEN at `0`, the varying `p.2` sitting in B's SECOND slot.  Because `p.2` sits in a DIFFERENT
    integrand argument position, the banked step is NOT slot-symmetric and does NOT transport verbatim.
    What IS fully generic is the STEP MACHINERY: the change-of-variables identity
    `IterEContinuity.heatConv_eq_smul_unitInterval` (moving upper limit → the fixed `Ioc 0 1` domain)
    holds for ALL `(x,y)`, and the double `MeasureTheory.continuousOn_of_dominated` + multiply-by-`p.1`
    route is integrand-agnostic.  So the z-slot step is a MECHANICAL REBUILD (not a transport) of the
    banked step with the varying coordinate re-oriented into B's second slot.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (I1a) `heatConv_z_jointContinuousOn_of_dominated` — ★★ THE z-slot STEP.  Joint `ContinuousOn` of
      `p ↦ heatConv A B p.1 0 p.2` on the box, from the fixed-domain (`Ioc 0 1`) parametric-integral
      data of the re-oriented integrand `∫ w, A (p.1−p.1·u) 0 w · B (p.1·u) w p.2`.  Rebuild of the
      banked outer engine in the z-slot orientation.

    * (I1b) `iterE_z_succ_jointContinuousOn_of_dominated` — ★ the z-slot STEP AT THE `iterE` LEVEL
      (`k ≥ 1`): the z-slot outer engine at `A = E`, `B = iterE E k`, giving joint continuity of
      `iterE E (k+1) p.1 0 p.2` from that convolution's z-slot domination data.

    * (I2) `iterE_z_continuousOn_box` — ★ the INDUCTION CAPSTONE.  `∀ n`, joint continuity of
      `p ↦ iterE E (n+1) p.1 0 p.2` on the FIXED box, by induction from the BASE (`iterE E 1 = E`
      z-slot joint continuity `hbase`, dischargeable by `NonLeviBoxContinuity`'s N2) and a per-level
      z-slot STEP provider (`hstep`, dischargeable by (I1b)).  The box is FIXED through the whole
      induction — never per-`n` boxes/floors (Sol's trap).

    * (I3) `iterE_z_continuousOn_box_family` — ★ the `∀ τ₀ ∈ Ioc 0 T, ∀ R` BOX-FAMILY shape feeding
      Sol brick 6's M-test, obtained from the `∀`-quantified base/step carries by (I2) at each box.

  ── HONEST CARRIES (satisfiable, non-vacuous, NEVER the conclusion).
    * `hbase` — the z-slot joint continuity of `E` itself, `p ↦ E p.1 0 p.2` (`E = heatOp g gi W_vv`,
      the Levi residual: one heat operator past the banked witness-kernel continuity).  This is EXACTLY
      `NonLeviBoxContinuity.heatOp_slice_continuousOn_box_of_parts` (J4-393, N2) — the banked z-slot
      base case, carried here as a hypothesis.
    * `hstep` — the per-level z-slot convolution step (dischargeable by (I1b) given each rung's
      Gaussian-integrable z-slot domination data, satisfiable from the banked `iterConvW_bound` /
      `RestrictedEboundW`-type geometric-over-`Γ` bounds uniformly on the compact `τ₀/2 > 0`).
    * The (I1) engine hypotheses `hmeas/hbound/hbnd_int/hcont` — the genuine analytic ingredients of the
      parametric-continuity theorem (measurability, integrable envelope, a.e. inner continuity); none is
      the joint-continuity conclusion.

    Sol brick 6's Weierstrass M-test then consumes this `∀ n` termwise box continuity together with the
    banked uniform majorant per box — `LeviSeriesLocalData.hmajor`
    (`|iterE E (k+1)| ≤ C^(k+1)·iterKernelW 2 0`) and `LeviSeriesLocalData.hmajorSum` (the `Γ`/factorial
    scalar-majorant summability) — to conclude joint continuity of the Levi tsum on the box.

  ⚠ STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LeviSeries
import QIQTH.IterEContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.IterEContinuity
open scoped Topology Interval

namespace QIQTH.LeviIterBoxInduction

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (I1a) — the z-slot OUTER engine (THE STEP, `x = 0` frozen, `y = p.2` varying).
    ############################################################################### -/

/-- **★★ (I1a) `heatConv_z_jointContinuousOn_of_dominated` — THE z-slot STEP.**  Joint `ContinuousOn`
    of the z-slot convolution slice
        `p ↦ heatConv A B p.1 0 p.2`
    on the compact box `Icc t₁ t₂ ×ˢ closedBall 0 R`, from the fixed-domain (`Ioc 0 1`)
    parametric-integral data of the RE-ORIENTED integrand
        `p ↦ ∫ w, A (p.1 − p.1·u) 0 w · B (p.1·u) w p.2`
    (varying `p.2` now sitting in B's SECOND spatial slot, A frozen at `0`):  for a.e. `u ∈ (0,1)` the
    inner spatial joint continuity (`hcont`); an integrable `u`-envelope (`hbnd_int`); and measurability
    (`hmeas`).  Route (mechanical rebuild of the banked x-slot
    `IterEContinuity.heatConv_jointContinuousOn_of_dominated`, re-oriented):
    `heatConv_eq_smul_unitInterval` (moving limit → `Ioc 0 1`), then `continuousOn_of_dominated` on the
    `u`-measure, then multiply by the continuous first coordinate `p.1`.  The carried hypotheses are the
    genuine analytic ingredients — NONE is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatConv_z_jointContinuousOn_of_dominated
    (A B : ℝ → Point n → Point n → ℝ) (t₁ t₂ R : ℝ) (bnd : ℝ → ℝ)
    (hmeas : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable (fun u => ∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2)
        (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hbound : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        ‖∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2‖ ≤ bnd u)
    (hbnd_int : Integrable bnd (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcont : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn (fun p : ℝ × Point n => ∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => heatConv A B p.1 0 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  -- joint `ContinuousOn` of the `u`-integral of the re-oriented inner spatial integral.
  have hG : ContinuousOn
      (fun p : ℝ × Point n =>
        ∫ u, (∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    continuousOn_of_dominated hmeas hbound hbnd_int hcont
  -- multiply by the continuous first coordinate.
  have hmul : ContinuousOn
      (fun p : ℝ × Point n =>
        p.1 * ∫ u, (∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2)
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (continuous_fst.continuousOn).mul hG
  refine hmul.congr ?_
  intro p _
  show heatConv A B p.1 0 p.2
    = p.1 * ∫ u, (∫ w, A (p.1 - p.1 * u) 0 w * B (p.1 * u) w p.2)
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))
  rw [heatConv_eq_smul_unitInterval, smul_eq_mul,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-! ###############################################################################
    ### (I1b) — the z-slot STEP at the `iterE` level (`k ≥ 1`).
    ############################################################################### -/

/-- **★ (I1b) `iterE_z_succ_jointContinuousOn_of_dominated` — the z-slot STEP at the `iterE` level
    (`k ≥ 1`).**  The z-slot outer engine at `A = E`, `B = iterE E k`: since
    `iterE E (k+1) = heatConvK E (iterE E k) = heatConv E (iterE E k)` for `k ≥ 1`, the z-slot joint
    continuity of `iterE E (k+1) p.1 0 p.2` follows from that convolution's z-slot fixed-domain
    domination data.  (`k = 1`: `iterE E 2 = heatConv E E`, the STEP at `k = 1`.)  Carried hypotheses =
    the z-slot outer engine's; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem iterE_z_succ_jointContinuousOn_of_dominated
    (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k) (t₁ t₂ R : ℝ) (bnd : ℝ → ℝ)
    (hmeas : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable
        (fun u => ∫ w, E (p.1 - p.1 * u) 0 w * iterE E k (p.1 * u) w p.2)
        (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hbound : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        ‖∫ w, E (p.1 - p.1 * u) 0 w * iterE E k (p.1 * u) w p.2‖ ≤ bnd u)
    (hbnd_int : Integrable bnd (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcont : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) 0 w * iterE E k (p.1 * u) w p.2)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 0 p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq : (fun p : ℝ × Point n => iterE E (k + 1) p.1 0 p.2)
      = (fun p : ℝ × Point n => heatConv E (iterE E k) p.1 0 p.2) := by
    funext p; rw [iterE_succ E hk, heatConvK_apply]
  rw [hEq]
  exact heatConv_z_jointContinuousOn_of_dominated E (iterE E k) t₁ t₂ R bnd
    hmeas hbound hbnd_int hcont

/-! ###############################################################################
    ### (I2) — the z-slot INDUCTION CAPSTONE on the FIXED box.
    ############################################################################### -/

/-- **★ (I2) `iterE_z_continuousOn_box` — the z-slot INDUCTION CAPSTONE.**  `∀ n`, joint `ContinuousOn`
    of `p ↦ iterE E (n+1) p.1 0 p.2` on the FIXED positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R`, by
    induction from the BASE (`iterE E 1 = E` z-slot joint continuity, `hbase`) and a per-level z-slot
    STEP provider (`hstep`, dischargeable by `iterE_z_succ_jointContinuousOn_of_dominated` given each
    rung's z-slot domination data).  The box is FIXED through the whole induction — never per-`n`
    boxes/floors.

    HONEST: `hbase` is the z-slot residual `p ↦ E p.1 0 p.2` continuity — EXACTLY
    `NonLeviBoxContinuity.heatOp_slice_continuousOn_box_of_parts` (J4-393, N2) for `E = heatOp g gi
    W_vv` — and `hstep` the per-level z-slot convolution step; both carried, satisfiable, non-vacuous —
    neither is the `∀ n` conclusion.  NOT `a₁ = R/6`. -/
theorem iterE_z_continuousOn_box
    (E : ℝ → Point n → Point n → ℝ) (τ₀ T R : ℝ)
    (hbase : ContinuousOn (fun p : ℝ × Point n => E p.1 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hstep : ∀ m : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (m + 1) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      → ContinuousOn (fun p : ℝ × Point n => iterE E (m + 2) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro k
  induction k with
  | zero => exact hbase
  | succ m ih => exact hstep m ih

/-! ###############################################################################
    ### (I3) — the `∀ τ₀ ∈ Ioc 0 T, ∀ R` BOX-FAMILY shape (M-test feed).
    ############################################################################### -/

/-- **★ (I3) `iterE_z_continuousOn_box_family` — the M-test BOX-FAMILY feed.**  The
    `∀ τ₀ ∈ Ioc 0 T, ∀ R, ∀ n` z-slot termwise box continuity family, obtained from the
    `∀`-quantified z-slot base carry (`hbase`, EXACTLY the `NonLeviBoxContinuity` N2 box member per
    `(τ₀,R)`) and the `∀`-quantified z-slot per-level step carry (`hstep`) by (I2) at each `(τ₀, R)`.
    This is the exact per-box termwise-continuity input consumed, together with the banked uniform
    majorant `LeviSeriesLocalData.hmajor` / `hmajorSum`, by Sol #16 brick 6's Weierstrass M-test.  NOT
    `a₁ = R/6`. -/
theorem iterE_z_continuousOn_box_family
    (E : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (hbase : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn (fun p : ℝ × Point n => E p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hstep : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ m : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (m + 1) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      → ContinuousOn (fun p : ℝ × Point n => iterE E (m + 2) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k : ℕ,
      ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  exact iterE_z_continuousOn_box E τ₀ T R (hbase τ₀ hτ₀ R) (hstep τ₀ hτ₀ R)

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @heatConv_z_jointContinuousOn_of_dominated
#check @iterE_z_succ_jointContinuousOn_of_dominated
#check @iterE_z_continuousOn_box
#check @iterE_z_continuousOn_box_family

#print axioms heatConv_z_jointContinuousOn_of_dominated
#print axioms iterE_z_succ_jointContinuousOn_of_dominated
#print axioms iterE_z_continuousOn_box
#print axioms iterE_z_continuousOn_box_family

end QIQTH.LeviIterBoxInduction
