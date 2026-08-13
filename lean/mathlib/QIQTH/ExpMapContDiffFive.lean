/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapFDeriv4
import QIQTH.ExpJet5Phase1

/-!
# JET-5 TOWER -- rung J5-5(e): `exp_p` is `ContDiff^5` near `0` (from bricks (a)-(d) + J5-4).

This file lands `expMap_contDiffOn_five`, the faithful one-Frechet-order-up mirror of the Rung-4
capstone `expMap_contDiffOn_four` (`ExpMapContDiffFour.lean`).  The `q`-centered exponential map is
`ContDiffOn ℝ 5` on the injectivity ball `‖v‖ < expRho`, with the ONLY hypotheses being the base
data `(g, gi, hC, p)`.

## The assembly

The proven Rung-5 reduction `expMap_contDiffOn_five_of_fderiv4_contDiffOn_one` (`ExpJet5Phase1.lean`)
needs one crux: `ContDiffOn ℝ 1 (fun v => fderiv^4 exp_p v)` on the ball.  This file discharges it:

* the fifth derivative `v ↦ fderiv (fderiv^4 exp_p) v` is Lipschitz on the exp-ball
  (`expJetD5_two_pt_diff` at once-obtained geometric constants), hence continuous;
* the fourth derivative `v ↦ fderiv^4 exp_p v` is differentiable (`expMap_fderiv4_hasFDerivAt`,
  brick (d));
* so `v ↦ fderiv^4 exp_p v` is `ContDiff^1` (`contDiffOn_succ_of_fderivWithin`, with
  `fderivWithin = fderiv` on the open ball), which the reduction upgrades to `ContDiff^5`.

## Honest firewall (binding)

**What is proven here:** brick (e) -- the `ContDiff^5` regularity of `exp_p` on the injectivity ball,
from brick (d) `expMap_fderiv4_hasFDerivAt` + the J5-4 two-point bound `expJetD5_two_pt_diff` + the
banked Rung-5 reduction.

**What is NOT closed:** this does NOT reach `kappa = 1/6`, the heat-kernel parametrix, or `a_1 = R/6`
(CONDITIONAL: curved still owes the J5-6 weld + Duhamel carry + fat-K carriers + capstone
co-instantiation), and is NOT QG.  Axiom-free.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

set_option maxHeartbeats 12800000 in
/-- **(D5) -- the Rung-5 CAPSTONE: `exp_p` is `ContDiff^5` near `0`.**
    The fifth derivative `v ↦ fderiv (fderiv^4 exp_p) v` is Lipschitz on the exp-ball
    (`expJetD5_two_pt_diff` at once-obtained geometric constants), hence continuous; the fourth
    derivative `v ↦ fderiv^4 exp_p v` is differentiable (`expMap_fderiv4_hasFDerivAt`, brick (d)); so
    `v ↦ fderiv^4 exp_p v` is `ContDiff^1` (`contDiffOn_succ_of_fderivWithin`, `fderivWithin = fderiv`
    on the open ball), which the proven reduction `expMap_contDiffOn_five_of_fderiv4_contDiffOn_one`
    upgrades to `ContDiff^5`.  Brick (e) of J5-5; NOT `kappa = 1/6`, NOT `a_1 = R/6`, NOT QG. -/
theorem expMap_contDiffOn_five (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 5 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  refine expMap_contDiffOn_five_of_fderiv4_contDiffOn_one g gi hC p ?_
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hsdef
  -- once-obtained geometric constants.
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2F⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3F⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Ld4f, hLipD4F⟩ := expJet_fderiv4_lipschitzOnWith g gi hC p
  obtain ⟨Ld5f, hLipD5F⟩ := expJet_fderiv5_lipschitzOnWith g gi hC p
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hKstar2f⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hKstar3f⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hKstar4f⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar5, hKstar50, hKstar5f⟩ := expJet_fderiv5_tube_bddAbove_unif g gi hC p
  set Cc : ℝ := expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
    Kstar Kstar2 Kstar3 Kstar4 Kstar5 with hCcdef
  have hCc0 : 0 ≤ Cc :=
    expJet5VtpConst_nonneg _ _ _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2
      hKstar20 hKstar30 hKstar40 hKstar50
  have hmemlt : ∀ v ∈ s, ‖v‖ < expRho g gi hC p := by
    intro v hv; rw [hsdef, Metric.mem_ball, dist_zero_right] at hv; exact hv
  -- the fourth derivative `F₄ = fderiv⁴ exp_p` is differentiable on the ball (brick (d)).
  have hdiffF4 : DifferentiableOn ℝ
      (fun v => fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (expMap g gi hC p) w) z) y) v) s := by
    intro v hv
    obtain ⟨Φv, hΦv0, hΦvd, hFDv⟩ := hasFDerivAt_expMap g gi hC p v (hmemlt v hv)
    have hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1) :=
      fun t ht => (hΦvd t ht).continuousWithinAt
    exact (expMap_fderiv4_hasFDerivAt g gi hC p v Φv (hmemlt v hv) hΦv0 hΦvcont hΦvd
      hFDv.fderiv).differentiableAt.differentiableWithinAt
  -- the fifth derivative `v ↦ fderiv F₄ v` is Lipschitz (⟹ continuous) on the ball.
  have hcont : ContinuousOn
      (fun v => fderiv ℝ (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (expMap g gi hC p) w) z) y) x) v) s := by
    have hlip : LipschitzOnWith Cc.toNNReal
        (fun v => fderiv ℝ (fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
          (expMap g gi hC p) w) z) y) x) v) s := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro v hv w hw
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hCc0]
      obtain ⟨Φv, hΦv0, hΦvd, hFDv⟩ := hasFDerivAt_expMap g gi hC p v (hmemlt v hv)
      obtain ⟨Φw, hΦw0, hΦwd, hFDw⟩ := hasFDerivAt_expMap g gi hC p w (hmemlt w hw)
      have hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1) :=
        fun t ht => (hΦvd t ht).continuousWithinAt
      have hΦwcont : ContinuousOn Φw (Set.Icc (0 : ℝ) 1) :=
        fun t ht => (hΦwd t ht).continuousWithinAt
      have hev := (expMap_fderiv4_hasFDerivAt g gi hC p v Φv (hmemlt v hv) hΦv0 hΦvcont hΦvd
        hFDv.fderiv).fderiv
      have hew := (expMap_fderiv4_hasFDerivAt g gi hC p w Φw (hmemlt w hw) hΦw0 hΦwcont hΦwd
        hFDw.fderiv).fderiv
      rw [hev, hew]
      exact expJetD5_two_pt_diff g gi hC p v w (hmemlt v hv).le (hmemlt w hw).le
        Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5
        hKstar0 hKstar20 hKstar30 hKstar40 hKstar50
        hLipF hLipDF hLipD2F hLipD3F hLipD4F hLipD5F
        hKstar hKstar2f hKstar3f hKstar4f hKstar5f
        Φv Φw hΦv0 hΦw0 hΦvd hΦwd hΦvcont hΦwcont
    exact hlip.continuousOn
  -- assemble `ContDiff¹` of the fourth derivative.
  have hopen : IsOpen s := by rw [hsdef]; exact Metric.isOpen_ball
  have hcont_fw : ContinuousOn
      (fun y => fderivWithin ℝ (fun v => fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ
        (fun w => fderiv ℝ (expMap g gi hC p) w) z) y) v) s y) s :=
    hcont.congr (fun y hy => fderivWithin_of_isOpen hopen hy)
  have hres := contDiffOn_succ_of_fderivWithin (n := 0) hdiffF4 (by simp)
    (contDiffOn_zero.mpr hcont_fw)
  rwa [zero_add] at hres

end QIQTH.ExpMap
