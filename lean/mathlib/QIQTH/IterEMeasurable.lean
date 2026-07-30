/-
  IterEMeasurable — M6 / analytic carry (regularity propagation): the space-slice and space-time
  joint measurabilities of the iterated Levi/Duhamel convolutions `iterE E k`, PROPAGATED by
  induction on `k` from a single BASE joint measurability of the residual kernel `E`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  PURPOSE.  `IterConvIntegrableFull.iterConvIntegrableW_of_bound_continuous` reduces the full
  per-step integrability family `IterConvIntegrableW E 2 0 C` to the one-step bound `hEbound`,
  the vanishing `hEzero`, and FOUR regularity carries:
      `hE_zmeas`, `hIterE_zmeas`, `hConv_meas`   (+ `hEzero` is separate).
  This file discharges the two INDUCTIVE ones — `hIterE_zmeas` and `hConv_meas` — plus the
  space-slice `hE_zmeas`, from a SINGLE base hypothesis:
      `hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)`
  i.e. the joint (time, source, target) strong measurability of `E`.  It is genuine, non-vacuous
  (measurability ⊊ integrability), and satisfied by the concrete residual `parametrixResidualN 0`
  via its joint continuity (`Continuous.stronglyMeasurable`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE INDUCTION.  The clean carrier is the MEASURE-FREE joint strong measurability of the pair
  variable `(σ, ζ) ↦ iterE E k σ ζ y` on `ℝ × Point n` (`iterE_joint_stronglyMeasurable`), proved
  by `Nat.le_induction`:
    • base `k = 1`: `iterE E 1 = E` (`iterE_one`), so it is `hEmeas` composed with `p ↦ (p.1, p.2, y)`.
    • step `k → k+1`: `iterE E (k+1) = heatConvK E (iterE E k)` (`iterE_succ`), whose value is
        `∫ u in 0..s, ∫ w, E (s-u) z w · iterE E k u w y`.
      The inner `∫ w` is handled by `StronglyMeasurable.integral_prod_right'` (the EVERYWHERE,
      measure-free Fubini-measurability lemma) fed the joint measurability of the 4-variable
      integrand `E (s-u) z w · iterE E k u w y` (`hEmeas` for the first factor, the IH for the
      second).  The variable-upper-limit `∫ u in 0..s` is unfolded to the `intervalIntegral`
      difference of two `Ioc`-set integrals, each rewritten as a full integral of a
      product-measurable indicator (the sets `{0 < u ∧ u ≤ s}` / `{s < u ∧ u ≤ 0}` are measurable),
      then integrated out by a SECOND application of `integral_prod_right'`.

  From the measure-free carrier both target carries follow trivially (slice = precompose with
  `Prod.mk s`; the space-time integrand = the base joint measurability of `(s,z) ↦ E (t-s) x z`
  times the carrier), converting to `AEStronglyMeasurable` for the requisite (restricted product)
  measure via `StronglyMeasurable.aestronglyMeasurable`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  PAYOFF.  `iterConvIntegrableW_of_bound_baseMeas` reduces `IterConvIntegrableW E 2 0 C` to
  `hEbound` + `hEzero` + the SINGLE base measurability `hEmeas` — feeding the derived carries into
  `iterConvIntegrableW_of_bound_continuous`.

  ⚠ HONEST SCOPE.  This discharges the regularity carries only; it does NOT touch `hEbound` (the
  width-2 one-step residual bound — the recenter/off-diagonal wall) and is NOT `a₁ = R/6`.  No
  `sorry`, no new axioms, no vacuous hypotheses; `hEmeas` is genuinely used at every level.
-/
import Mathlib
import QIQTH.IterConvIntegrableFull

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ The measure-free joint strong measurability of every iterated residual convolution.**
    From the joint (time, source, target) strong measurability of `E`, the pair map
    `(σ, ζ) ↦ iterE E k σ ζ y` is `StronglyMeasurable` on `ℝ × Point n`, for every level `k ≥ 1`
    and every fixed target `y`.  Proof by `Nat.le_induction`: the base is `E` precomposed with a
    measurable section; the step convolves once more, its inner spatial integral and its
    variable-upper-limit time integral both made measurable by `StronglyMeasurable.integral_prod_right'`
    (via the measurable-indicator form of the `Ioc` set integrals). -/
theorem iterE_joint_stronglyMeasurable
    (E : ℝ → Point n → Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    ∀ k, 1 ≤ k → ∀ y : Point n,
      StronglyMeasurable (fun p : ℝ × Point n => iterE E k p.1 p.2 y) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro y
      have hrw : (fun p : ℝ × Point n => iterE E 1 p.1 p.2 y)
          = (fun p : ℝ × Point n => E p.1 p.2 y) := by
        funext p; rw [iterE_one]
      rw [hrw]
      exact hEmeas.comp_measurable
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  | succ m hm ih =>
      intro y
      -- The 4-variable convolution integrand, jointly strongly measurable.
      have hFmeas : StronglyMeasurable
          (fun q : ((ℝ × Point n) × ℝ) × Point n =>
            E (q.1.1.1 - q.1.2) q.1.1.2 q.2 * iterE E m q.1.2 q.2 y) := by
        have hEpart : StronglyMeasurable
            (fun q : ((ℝ × Point n) × ℝ) × Point n => E (q.1.1.1 - q.1.2) q.1.1.2 q.2) :=
          hEmeas.comp_measurable
            (((measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
                (measurable_snd.comp measurable_fst)).prodMk
              ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
        have hBpart : StronglyMeasurable
            (fun q : ((ℝ × Point n) × ℝ) × Point n => iterE E m q.1.2 q.2 y) :=
          (ih y).comp_measurable ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
        exact hEpart.mul hBpart
      -- Integrate out the spatial variable `w`: measure-free Fubini-measurability.
      have hH : StronglyMeasurable
          (fun r : (ℝ × Point n) × ℝ =>
            ∫ w, E (r.1.1 - r.2) r.1.2 w * iterE E m r.2 w y) :=
        hFmeas.integral_prod_right'
      -- The two `Ioc`-set indicators are product-measurable.
      have hS1 : MeasurableSet {q : (ℝ × Point n) × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1} :=
        (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
      have hS2 : MeasurableSet {q : (ℝ × Point n) × ℝ | q.1.1 < q.2 ∧ q.2 ≤ 0} :=
        (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
      -- The two variable-upper-limit `Ioc` time integrals are strongly measurable in `p`.
      have hG1 : StronglyMeasurable
          (fun p : ℝ × Point n =>
            ∫ u in Set.Ioc (0 : ℝ) p.1, ∫ w, E (p.1 - u) p.2 w * iterE E m u w y) := by
        have e1 : (fun p : ℝ × Point n =>
              ∫ u in Set.Ioc (0 : ℝ) p.1, ∫ w, E (p.1 - u) p.2 w * iterE E m u w y)
            = (fun p : ℝ × Point n =>
              ∫ u, Set.indicator {q : (ℝ × Point n) × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1}
                (fun r => ∫ w, E (r.1.1 - r.2) r.1.2 w * iterE E m r.2 w y) (p, u)) := by
          funext p
          rw [← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := p.1))]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          dsimp only
          by_cases hu : (0 : ℝ) < u ∧ u ≤ p.1
          · rw [Set.indicator_of_mem (by simpa only [Set.mem_Ioc] using hu),
                Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq] using hu)]
          · rw [Set.indicator_of_notMem (by simpa only [Set.mem_Ioc] using hu),
                Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq] using hu)]
        rw [e1]
        exact (hH.indicator hS1).integral_prod_right'
      have hG2 : StronglyMeasurable
          (fun p : ℝ × Point n =>
            ∫ u in Set.Ioc p.1 (0 : ℝ), ∫ w, E (p.1 - u) p.2 w * iterE E m u w y) := by
        have e2 : (fun p : ℝ × Point n =>
              ∫ u in Set.Ioc p.1 (0 : ℝ), ∫ w, E (p.1 - u) p.2 w * iterE E m u w y)
            = (fun p : ℝ × Point n =>
              ∫ u, Set.indicator {q : (ℝ × Point n) × ℝ | q.1.1 < q.2 ∧ q.2 ≤ 0}
                (fun r => ∫ w, E (r.1.1 - r.2) r.1.2 w * iterE E m r.2 w y) (p, u)) := by
          funext p
          rw [← integral_indicator (measurableSet_Ioc (a := p.1) (b := (0 : ℝ)))]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          dsimp only
          by_cases hu : p.1 < u ∧ u ≤ (0 : ℝ)
          · rw [Set.indicator_of_mem (by simpa only [Set.mem_Ioc] using hu),
                Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq] using hu)]
          · rw [Set.indicator_of_notMem (by simpa only [Set.mem_Ioc] using hu),
                Set.indicator_of_notMem (by simpa only [Set.mem_setOf_eq] using hu)]
        rw [e2]
        exact (hH.indicator hS2).integral_prod_right'
      -- Assemble: `iterE E (m+1)` = the `intervalIntegral` = difference of the two `Ioc` integrals.
      have key : (fun p : ℝ × Point n => iterE E (m + 1) p.1 p.2 y)
          = (fun p : ℝ × Point n =>
              (∫ u in Set.Ioc (0 : ℝ) p.1, ∫ w, E (p.1 - u) p.2 w * iterE E m u w y)
                - (∫ u in Set.Ioc p.1 (0 : ℝ), ∫ w, E (p.1 - u) p.2 w * iterE E m u w y)) := by
        funext p
        rw [iterE_succ E hm, heatConvK_apply]
        rfl
      rw [key]
      exact hG1.sub hG2

/-- **The space-slice measurability carry `hIterE_zmeas`.**  The middle-argument slice
    `z ↦ iterE E k s z y` is `AEStronglyMeasurable` (for volume), for every level `k ≥ 1`.
    It is the joint carrier precomposed with the measurable section `z ↦ (s, z)`. -/
theorem iterE_zmeas
    (E : ℝ → Point n → Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ) (y : Point n),
      AEStronglyMeasurable (fun z : Point n => iterE E k s z y) volume := by
  intro k hk s y
  have h := iterE_joint_stronglyMeasurable E hEmeas k hk y
  exact (h.comp_measurable measurable_prodMk_left).aestronglyMeasurable

/-- **The space-time joint measurability carry `hConv_meas`.**  The convolution integrand
    `(s, z) ↦ E (t-s) x z · iterE E k s z y` is `AEStronglyMeasurable` on the restricted product
    `(volume.restrict (Ioc 0 t)).prod volume`, for every level `k ≥ 1`.  It is the base joint
    measurability of `(s, z) ↦ E (t-s) x z` times the joint carrier, as a `StronglyMeasurable`
    function, restricted to the given measure. -/
theorem conv_meas
    (E : ℝ → Point n → Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      AEStronglyMeasurable
        (Function.uncurry (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y))
        ((volume.restrict (Set.Ioc 0 t)).prod volume) := by
  intro k hk t _ht x y
  have hB := iterE_joint_stronglyMeasurable E hEmeas k hk y
  have hA : StronglyMeasurable (fun p : ℝ × Point n => E (t - p.1) x p.2) :=
    hEmeas.comp_measurable
      ((measurable_const.sub measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have hmul : StronglyMeasurable
      (fun p : ℝ × Point n => E (t - p.1) x p.2 * iterE E k p.1 p.2 y) := hA.mul hB
  simpa only [Function.uncurry] using hmul.aestronglyMeasurable

/-- **★ THE PAYOFF: the full per-step integrability family from the one-step bound + a SINGLE base
    measurability.**  Given the width-2 one-step residual bound `hEbound`, the vanishing at
    nonpositive time `hEzero`, and the joint strong measurability `hEmeas` of `E`, the full
    per-step integrability family `IterConvIntegrableW E 2 0 C` holds — the three regularity
    carries of `iterConvIntegrableW_of_bound_continuous` being supplied by `iterE_zmeas` /
    `conv_meas` (and the space slice of `hEmeas`).  Reduces the `hInt` discharge to
    `hEbound` + `hEzero` + base `E`-measurability. -/
theorem iterConvIntegrableW_of_bound_baseMeas
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C := by
  refine iterConvIntegrableW_of_bound_continuous E C hEbound hEzero ?_ ?_ ?_
  · intro τ p
    exact (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact iterE_zmeas E hEmeas
  · exact conv_meas E hEmeas

end QIQTH.HeatResidualBound
