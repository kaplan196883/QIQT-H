/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiffFour
import QIQTH.PullbackMetricC3

/-!
# UNCONDITIONAL `ContDiff³` of the `q`-centered pullback metric (J4-6a)

This file discharges the last remaining side hypothesis `hfd3` in the pullback-metric-`C³` chain,
turning `contDiffOn_expPullbackMetric_three` (which carried the Rung-4 exp Jet₄ third-jet `C¹`
regularity `hfd3` as an explicit hypothesis) into an **unconditional** theorem whose only inputs are
the base data `(g, gi, hC, p)` (plus the genuine ambient-metric smoothness `hg` and the indices
`i j`, neither of which is `hfd3`).

The crux is now the landed `expMap_contDiffOn_four` (`ExpMapContDiffFour.lean`): `exp_p ∈ C⁴` on the
injectivity ball, UNCONDITIONALLY.  Iterating `ContDiffOn.fderiv_of_isOpen` three times on the open
ball produces exactly the `hfd3` obligation (`ContDiff¹` of the third Fréchet derivative), which we
then feed to the existing conditional pullback-`C³` lemma.

## Honest firewall (binding)

* `expMap_fderiv3_contDiffOn_one` is **derived** from `expMap_contDiffOn_four` — no carried `hfd3`.
* `contDiffOn_expPullbackMetric_three_uncond` is obtained by feeding the derived `hfd3` to the
  existing `contDiffOn_expPullbackMetric_three`; `hg` (ambient metric `g ∈ C^∞`, component-wise)
  remains a genuine hypothesis (it is NOT derivable from `hC` alone), exactly as in the original.
* This does NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric

-- The third-derivative CLM tower needs a deeper pending-instance synthesis depth (mirror of
-- `PullbackMetricC3.lean` / `ExpMapContDiff4.lean`).
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-- **`hfd3`, now UNCONDITIONAL.**  The third Fréchet derivative of `exp_p` is `ContDiff¹` on the
    exp-ball, with the ONLY hypotheses being the base data `(g, gi, hC, p)`.  Derived from the landed
    `expMap_contDiffOn_four` (`exp_p ∈ C⁴`) by iterating `ContDiffOn.fderiv_of_isOpen` three times on
    the open ball: `C⁴ exp_p ⟹ C³ (fderiv exp_p) ⟹ C² (fderiv² exp_p) ⟹ C¹ (fderiv³ exp_p)`. -/
theorem expMap_fderiv3_contDiffOn_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  -- `F₁ := fderiv exp_p` is `ContDiffOn ℝ 3` on the open ball (one order below `C⁴ exp_p`).
  have hF1cd3 : ContDiffOn ℝ 3 (fun v => fderiv ℝ (expMap g gi hC p) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    (expMap_contDiffOn_four g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  -- `F₂ := fderiv F₁` is `ContDiffOn ℝ 2`.
  have hF2cd2 : ContDiffOn ℝ 2 (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    hF1cd3.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  -- `F₃ := fderiv F₂` is `ContDiffOn ℝ 1` — exactly the `hfd3` obligation.
  exact hF2cd2.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)

/-- **UNCONDITIONAL `ContDiff³` of the pullback metric (the J4-6a deliverable):** each component
    `x ↦ g̃(x)_{ij}` of the `q`-centered pullback metric is `ContDiffOn ℝ 3` on the exp-ball, with
    NO `hfd3` side hypothesis.  Obtained by feeding the now-derived third-jet regularity
    `expMap_fderiv3_contDiffOn_one` to the existing conditional `contDiffOn_expPullbackMetric_three`.
    `hg` (ambient metric `g ∈ C^∞`) remains a genuine hypothesis, exactly as in the original. -/
theorem contDiffOn_expPullbackMetric_three_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j : Fin n) :
    ContDiffOn ℝ 3 (fun x => expPullbackMetric g gi hC p x i j)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
  contDiffOn_expPullbackMetric_three g gi hC p hg i j
    (expMap_fderiv3_contDiffOn_one g gi hC p)

end QIQTH.ExpMap
