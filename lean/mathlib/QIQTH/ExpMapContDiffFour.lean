/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapFDeriv3
import QIQTH.ExpMapContDiff4
import QIQTH.ExpJet4DFull
import QIQTH.ExpJet4ValFull
import QIQTH.ExpJet4Prereq
import QIQTH.ExpMapContDiff3

/-!
# JET-4 TOWER — rung J4-5f (the CAPSTONE): `exp_p` is `ContDiff⁴` near `0`, UNCONDITIONALLY

This file lands `expMap_contDiffOn_four`, the faithful one-Fréchet-order-up mirror of the Rung-3
capstone `expMap_contDiffOn_three` (`ExpMapContDiff3.lean`).  The `q`-centered exponential map is
`ContDiffOn ℝ 4` on the injectivity ball `‖v‖ < expRho`, with the ONLY hypotheses being the base
data `(g, gi, hC, p)` — `exp_p ∈ C⁴` is now UNCONDITIONAL.

## The assembly

The proven Rung-4 reduction `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one` needs one crux:
`ContDiffOn ℝ 1 (fun v => fderiv³ exp_p v)` on the ball.  This file discharges it:

* the fourth derivative `v ↦ fderiv (fderiv³ exp_p) v` is Lipschitz on the exp-ball
  (`expJetD4_two_pt_diff` at once-obtained geometric constants), hence continuous;
* the third derivative `v ↦ fderiv³ exp_p v` is differentiable (`expMap_fderiv3_hasFDerivAt`);
* so `v ↦ fderiv³ exp_p v` is `ContDiff¹` (`contDiffOn_succ_of_fderivWithin`, with
  `fderivWithin = fderiv` on the open ball via `fderivWithin_of_isOpen`), which the reduction upgrades
  to `ContDiff⁴`.

Every crux left open by the Rung-4 reduction is now discharged by the Jet₄ fundamental-solution /
Grönwall machinery (`expJetD4_two_pt_diff`, `expMap_fderiv3_hasFDerivAt`).  NO side hypothesis — the
milestone `ContDiff⁴ exp_p`.

## Honest firewall (binding)

**What is proven here:** the UNCONDITIONAL `ContDiff⁴` regularity of `exp_p` on the injectivity ball.

**What is NOT closed:** this does NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`,
and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁴F` is a QUADRUPLY-nested continuous-linear-map space; raise pending-instance
-- synthesis depth (mirror of the Rung-4 differentiability file `ExpMapFDeriv3`).
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

variable {n : ℕ}

set_option maxHeartbeats 6400000 in
/-- **(D4) — the Rung-4 CAPSTONE: `exp_p` is `ContDiff⁴` near `0`, UNCONDITIONALLY.**
    The fourth derivative `v ↦ fderiv (fun z => fderiv³ exp_p z) v` is Lipschitz on the exp-ball
    (`expJetD4_two_pt_diff` at once-obtained geometric constants), hence continuous; the third
    derivative `v ↦ fderiv³ exp_p v` is differentiable (`expMap_fderiv3_hasFDerivAt`); so
    `v ↦ fderiv³ exp_p v` is `ContDiff¹` (`contDiffOn_succ_of_fderivWithin`, `fderivWithin = fderiv`
    on the open ball), which the proven reduction `expMap_contDiffOn_four_of_fderiv3_contDiffOn_one`
    upgrades to `ContDiff⁴`.  NO SIDE HYPOTHESIS: every crux left open by the earlier reduction is now
    discharged — the milestone `ContDiff⁴ exp_p`. -/
theorem expMap_contDiffOn_four (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 4 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  refine expMap_contDiffOn_four_of_fderiv3_contDiffOn_one g gi hC p ?_
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
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hKstar2f⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hKstar3f⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hKstar4f⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  set Cc : ℝ := expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ)
    Kstar Kstar2 Kstar3 Kstar4 with hCcdef
  have hCc0 : 0 ≤ Cc :=
    expJet4VtpConst_nonneg _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 hKstar20 hKstar30 hKstar40
  have hmemlt : ∀ v ∈ s, ‖v‖ < expRho g gi hC p := by
    intro v hv; rw [hsdef, Metric.mem_ball, dist_zero_right] at hv; exact hv
  -- the third derivative `F₃ = fderiv³ exp_p` is differentiable on the ball.
  have hdiffF3 : DifferentiableOn ℝ
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g gi hC p) w) z) v) s := by
    intro v hv
    obtain ⟨Φv, hΦv0, hΦvd, hFDv⟩ := hasFDerivAt_expMap g gi hC p v (hmemlt v hv)
    have hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1) :=
      fun t ht => (hΦvd t ht).continuousWithinAt
    exact (expMap_fderiv3_hasFDerivAt g gi hC p v Φv (hmemlt v hv) hΦv0 hΦvcont hΦvd
      hFDv.fderiv).differentiableAt.differentiableWithinAt
  -- the fourth derivative `v ↦ fderiv F₃ v` is Lipschitz (⟹ continuous) on the ball.
  have hcont : ContinuousOn
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (fun u => fderiv ℝ (expMap g gi hC p) u) w) z) v) s := by
    have hlip : LipschitzOnWith Cc.toNNReal
        (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
          (fun u => fderiv ℝ (expMap g gi hC p) u) w) z) v) s := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro v hv w hw
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hCc0]
      obtain ⟨Φv, hΦv0, hΦvd, hFDv⟩ := hasFDerivAt_expMap g gi hC p v (hmemlt v hv)
      obtain ⟨Φw, hΦw0, hΦwd, hFDw⟩ := hasFDerivAt_expMap g gi hC p w (hmemlt w hw)
      have hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1) :=
        fun t ht => (hΦvd t ht).continuousWithinAt
      have hΦwcont : ContinuousOn Φw (Set.Icc (0 : ℝ) 1) :=
        fun t ht => (hΦwd t ht).continuousWithinAt
      have hev := (expMap_fderiv3_hasFDerivAt g gi hC p v Φv (hmemlt v hv) hΦv0 hΦvcont hΦvd
        hFDv.fderiv).fderiv
      have hew := (expMap_fderiv3_hasFDerivAt g gi hC p w Φw (hmemlt w hw) hΦw0 hΦwcont hΦwd
        hFDw.fderiv).fderiv
      rw [hev, hew]
      exact expJetD4_two_pt_diff g gi hC p v w (hmemlt v hv).le (hmemlt w hw).le
        Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
        hKstar0 hKstar20 hKstar30 hKstar40
        hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f
        Φv Φw hΦv0 hΦw0 hΦvd hΦwd hΦvcont hΦwcont
    exact hlip.continuousOn
  -- assemble `ContDiff¹` of the third derivative.
  have hopen : IsOpen s := by rw [hsdef]; exact Metric.isOpen_ball
  have hcont_fw : ContinuousOn
      (fun y => fderivWithin ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ
        (fun u => fderiv ℝ (expMap g gi hC p) u) w) z) s y) s :=
    hcont.congr (fun y hy => fderivWithin_of_isOpen hopen hy)
  have hres := contDiffOn_succ_of_fderivWithin (n := 0) hdiffF3 (by simp)
    (contDiffOn_zero.mpr hcont_fw)
  rwa [zero_add] at hres

end QIQTH.ExpMap
