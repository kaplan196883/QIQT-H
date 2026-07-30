/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import QIQTH.PullbackMetric
import QIQTH.ExpMapContDiff4

/-!
# `ContDiff³` of the `q`-centered pullback metric (brick R3c-1 of RECENTER)

This file upgrades the regularity of the pullback metric `g̃ = exp_p^* g` by one Fréchet-derivative
order, from the sharp-for-`C³`-`exp` result `contDiffOn_expPullbackMetric`
(`ContDiffOn ℝ 2`, in `PullbackMetric.lean`) to `ContDiffOn ℝ 3`, **conditional on the Rung-4 exp
regularity input** `hfd3` (the exp Jet₄ third-jet `C¹` regularity that
`expMap_contDiffOn_four_of_fderiv3_contDiffOn_one` carries as an explicit hypothesis).

The proof is the exact mirror of `contDiffOn_expPullbackMetric`, one order higher:
* `hE : ContDiffOn ℝ 3 (exp_p)` from `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one … hfd3`;
* `hgcomp : ContDiffOn ℝ 3 (g ∘ exp_p)` (`C^∞` `g`-component composed with `C³` `exp_p`);
* the Jacobian components at `ContDiffOn ℝ 3` (fderiv of a `C⁴` function is `C³`), via the helper
  `contDiffOn_fderiv_expMap_component_three`;
* the triple product and finite `∑_{a,b}` preserve the minimum order `3`.

## Honest firewall (binding)

* `hfd3` is **genuine**: it is exactly the Rung-4 exp obligation (the Jet₄ third-jet map is `C¹`),
  carried through `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one` and honestly threaded here. It is
  NOT discharged (that is the Jet₄ sub-campaign, not built anywhere).
* `hg` (ambient metric `g` is `C^∞` component-wise) is genuine and used, mirroring the `C²` original;
  it is NOT derivable from the Christoffel smoothness `hC` alone.
* This does NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`.
-/

namespace QIQTH.PullbackMetric

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic
open Finset

-- Mirror the Rung-4 file: the fourth-derivative CLM tower needs a deeper pending-instance depth.
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-- **The Jacobian of `exp_p` is `ContDiffOn ℝ 3` on the exp-ball, conditional on `hfd3`.**  `fderiv`
    drops one differentiability order from the `ContDiff⁴` `exp_p`
    (`expMap_contDiffOn_four_of_fderiv3_contDiffOn_one … hfd3`), on the open ball.  One order above
    `contDiffOn_fderiv_expMap`. -/
theorem contDiffOn_fderiv_expMap_three (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 3 (fun x => fderiv ℝ (expMap g gi hC p) x)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
  (expMap_contDiffOn_four_of_fderiv3_contDiffOn_one g gi hC p hfd3).fderiv_of_isOpen
    Metric.isOpen_ball (by norm_num)

/-- Each scalar component of the Jacobian, `x ↦ (D exp_p x · e_i)_a`, is `ContDiffOn ℝ 3` on the
    exp-ball (conditional on `hfd3`): apply the `ContDiffOn ℝ 3` CLM-field `x ↦ D exp_p x` to the
    constant vector `e_i` (`ContDiffOn.clm_apply`) and read off the `a`-th coordinate (compose with
    the projection CLM).  One order above `contDiffOn_fderiv_expMap_component`. -/
theorem contDiffOn_fderiv_expMap_component_three (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p)))
    (i a : Fin n) :
    ContDiffOn ℝ 3 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  have hJv : ContDiffOn ℝ 3 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1))
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    (contDiffOn_fderiv_expMap_three g gi hC p hfd3).clm_apply contDiffOn_const
  exact hJv.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a)

/-- **REGULARITY OF THE PULLBACK METRIC AT `C³` (the deliverable, conditional on `hfd3`):** each
    component `x ↦ g̃(x)_{ij}` of the pullback metric is `ContDiffOn ℝ 3` on the exp-ball, given the
    Rung-4 exp regularity input `hfd3` (`exp_p ∈ C⁴`) and the ambient metric `g ∈ C^∞`.

    Exact mirror of `contDiffOn_expPullbackMetric`, one order higher:
    * `x ↦ g(exp_p x)_{ab}` is `ContDiffOn ℝ 3` (`C^∞` `g` composed with `C³` `exp_p`);
    * `x ↦ (D exp_p x · e_i)_a` is `ContDiffOn ℝ 3` (`fderiv exp_p` is one order below `C⁴` `exp_p`);
    * the triple product and the finite `∑_{a,b}` preserve the minimum order `3`. -/
theorem contDiffOn_expPullbackMetric_three (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j : Fin n)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p))) :
    ContDiffOn ℝ 3 (fun x => expPullbackMetric g gi hC p x i j)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hs
  -- `exp_p ∈ C⁴` on `s` (conditional on `hfd3`); downgrade to `C³` where needed.
  have hE : ContDiffOn ℝ 3 (expMap g gi hC p) s :=
    (expMap_contDiffOn_four_of_fderiv3_contDiffOn_one g gi hC p hfd3).of_le (by norm_num)
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  -- `x ↦ g(exp_p x)_{ab}` : `C^∞` `g`-component composed with `C³` `exp_p`.
  have hgcomp : ContDiffOn ℝ 3 (fun x => g (expMap g gi hC p x) a b) s :=
    ((hg a b).of_le (le_top)).comp_contDiffOn hE
  -- the two Jacobian components, at order 3.
  have hJa : ContDiffOn ℝ 3 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) s :=
    contDiffOn_fderiv_expMap_component_three g gi hC p hfd3 i a
  have hJb : ContDiffOn ℝ 3 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) s :=
    contDiffOn_fderiv_expMap_component_three g gi hC p hfd3 j b
  exact (hgcomp.mul hJa).mul hJb

end QIQTH.PullbackMetric
