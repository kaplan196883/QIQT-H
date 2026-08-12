/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase4
import QIQTH.ExpJet5TeleA
import QIQTH.ExpJet5BlkA
import QIQTH.ExpJet5BlkB
import QIQTH.ExpJet5BlkC
import QIQTH.ExpJet5RhoEq
import Mathlib

/-!
# JET-5 phase 5 (J4-649): the 202-sub-term `ρ₅`-telescope — `expJet5Val_v_two_pt_diff` CLOSED

Brick **J4-649** of the JET-5 campaign toward the truly-unconditional `a₁ = R/6`
(`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`): stage (iii-b) of the J5-3 crux — the concrete
202-sub-term `ρ₅`-telescope discharging the `hrbound` hypothesis of the banked
`expJet5Val_v_two_pt_diff_gronwall` (`ExpJet5Phase4.lean`), closing the order-5 two-point
Lipschitz bound

`‖R⁵_v(1) − R⁵_w(1)‖ ≤ expJet5VtpConst · ‖v−w‖·‖h‖‖k‖‖l‖‖m‖‖r‖`.

The 51-term source difference `Θ₅_v − Θ₅_w` telescopes through the four generic peel bounds
(`ExpJet5TeleA.lean`): `1×6 + 10×5 + 25×4 + 15×3 = 201` sub-terms plus the leading
`[DF(Y_v)−DF(Y_w)](R_w)` Lipschitz term `= 202`.  Every peel consumes only banked feeders:
`expJet2Fund_value_bound_Icc` / `expJet3Fund_value_bound_Icc` / `expJet4Fund_value_bound_Icc` /
`expJet5Fund_value_bound_Icc` (value bounds), `expJet2_v_two_pt_Icc_const` /
`expJet3Val_v_two_pt_Icc_const` / `expJet4Val_v_two_pt_Icc_const` (lower-order two-point
Lipschitz), `expFund_two_pt_diff_Icc` (propagator two-point), and the `DⁱF` tube/Lipschitz data.

## Honest firewall (binding)

**What IS closed here:** J5-3 (the order-5 two-point Grönwall crux), as a conditional theorem
at explicit tube/Lipschitz data (`hLipD5F`, `Kstar5`, …), the exact mirror of the banked
order-≤4 layers.  **What is NOT closed:** J5-4 (`expJetD5` quintilinear CLM packaging),
J5-5/J5-6 (`hfd4` / `exp_p ∈ C⁵` wiring).  This does NOT establish `exp_p ∈ C⁵`, does NOT
reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`, and is NOT numerical-`G` /
the conjecture / QG.  `a₁ = R/6` remains CONDITIONAL (flat tower non-vacuous; curved owes
the remaining Jet-5 packaging + the Duhamel carry + fat-K carriers + capstone
co-instantiation + the prior labelled piles).
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 65536

variable {n : ℕ}

set_option maxHeartbeats 12800000 in
/-- **★ (J4-649) The (D) core, Rung 5 — the `v`-two-point Lipschitz bound of the
    fifth-variation value (J5-3 CLOSED).**
    `‖Rv 1 − Rw 1‖ ≤ expJet5VtpConst·‖v−w‖·‖h‖‖k‖‖l‖‖m‖‖r‖`.  The residual
    `D = Rv − Rw` solves `D' = DF(Y_v)(D) + ρ₅`; the `ρ₅`-residual telescopes into the
    202 sub-terms (via the `ExpJet5TeleA` peel bounds), each `≤ C·‖v−w‖‖h‖‖k‖‖l‖‖m‖‖r‖`;
    then the residual Grönwall (`expJet5Val_v_two_pt_diff_gronwall`, J4-648). -/
theorem expJet5Val_v_two_pt_diff
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f Ld3f Ld4f Ld5f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3)
    (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi)) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD3F : LipschitzOnWith Ld3f (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD4F : LipschitzOnWith Ld4f (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD5F : LipschitzOnWith Ld5f (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar2f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p u t)‖ ≤ Kstar2)
    (hKstar3f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p u t)‖ ≤ Kstar3)
    (hKstar4f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p u t)‖ ≤ Kstar4)
    (hKstar5f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) (expTube g gi hC p u t)‖ ≤ Kstar5)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (Qhkv Qhlv Qhmv Qhrv Qklv : ℝ → (Point n × Point n))
    (Qkmv Qkrv Qlmv Qlrv Qmrv : ℝ → (Point n × Point n))
    (Qhkw Qhlw Qhmw Qhrw Qklw : ℝ → (Point n × Point n))
    (Qkmw Qkrw Qlmw Qlrw Qmrw : ℝ → (Point n × Point n))
    (Qhklv Qhkmv Qhkrv Qhlmv Qhlrv : ℝ → (Point n × Point n))
    (Qhmrv Qklmv Qklrv Qkmrv Qlmrv : ℝ → (Point n × Point n))
    (Qhklw Qhkmw Qhkrw Qhlmw Qhlrw : ℝ → (Point n × Point n))
    (Qhmrw Qklmw Qklrw Qkmrw Qlmrw : ℝ → (Point n × Point n))
    (Qhklmv Qhklrv Qhkmrv Qhlmrv Qklmrv : ℝ → (Point n × Point n))
    (Qhklmw Qhklrw Qhkmrw Qhlmrw Qklmrw : ℝ → (Point n × Point n))
    (Rv Rw : ℝ → (Point n × Point n)) (h k l m r : Point n)
    (hQhkv0 : Qhkv 0 = 0)
    (hQhlv0 : Qhlv 0 = 0)
    (hQhmv0 : Qhmv 0 = 0)
    (hQhrv0 : Qhrv 0 = 0)
    (hQklv0 : Qklv 0 = 0)
    (hQkmv0 : Qkmv 0 = 0)
    (hQkrv0 : Qkrv 0 = 0)
    (hQlmv0 : Qlmv 0 = 0)
    (hQlrv0 : Qlrv 0 = 0)
    (hQmrv0 : Qmrv 0 = 0)
    (hQhkw0 : Qhkw 0 = 0)
    (hQhlw0 : Qhlw 0 = 0)
    (hQhmw0 : Qhmw 0 = 0)
    (hQhrw0 : Qhrw 0 = 0)
    (hQklw0 : Qklw 0 = 0)
    (hQkmw0 : Qkmw 0 = 0)
    (hQkrw0 : Qkrw 0 = 0)
    (hQlmw0 : Qlmw 0 = 0)
    (hQlrw0 : Qlrw 0 = 0)
    (hQmrw0 : Qmrw 0 = 0)
    (hQhklv0 : Qhklv 0 = 0)
    (hQhkmv0 : Qhkmv 0 = 0)
    (hQhkrv0 : Qhkrv 0 = 0)
    (hQhlmv0 : Qhlmv 0 = 0)
    (hQhlrv0 : Qhlrv 0 = 0)
    (hQhmrv0 : Qhmrv 0 = 0)
    (hQklmv0 : Qklmv 0 = 0)
    (hQklrv0 : Qklrv 0 = 0)
    (hQkmrv0 : Qkmrv 0 = 0)
    (hQlmrv0 : Qlmrv 0 = 0)
    (hQhklw0 : Qhklw 0 = 0)
    (hQhkmw0 : Qhkmw 0 = 0)
    (hQhkrw0 : Qhkrw 0 = 0)
    (hQhlmw0 : Qhlmw 0 = 0)
    (hQhlrw0 : Qhlrw 0 = 0)
    (hQhmrw0 : Qhmrw 0 = 0)
    (hQklmw0 : Qklmw 0 = 0)
    (hQklrw0 : Qklrw 0 = 0)
    (hQkmrw0 : Qkmrw 0 = 0)
    (hQlmrw0 : Qlmrw 0 = 0)
    (hQhklmv0 : Qhklmv 0 = 0)
    (hQhklrv0 : Qhklrv 0 = 0)
    (hQhkmrv0 : Qhkmrv 0 = 0)
    (hQhlmrv0 : Qhlmrv 0 = 0)
    (hQklmrv0 : Qklmrv 0 = 0)
    (hQhklmw0 : Qhklmw 0 = 0)
    (hQhklrw0 : Qhklrw 0 = 0)
    (hQhkmrw0 : Qhkmrw 0 = 0)
    (hQhlmrw0 : Qhlmrw 0 = 0)
    (hQklmrw0 : Qklmrw 0 = 0)
    (hRv0 : Rv 0 = 0) (hRw0 : Rw 0 = 0)
    (hQhkvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkv t) + expJet2Rhs g gi hC p v Φv h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlv t) + expJet2Rhs g gi hC p v Φv h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhmv t) + expJet2Rhs g gi hC p v Φv h m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhrv t) + expJet2Rhs g gi hC p v Φv h r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklv t) + expJet2Rhs g gi hC p v Φv k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qkmv t) + expJet2Rhs g gi hC p v Φv k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQkrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qkrv t) + expJet2Rhs g gi hC p v Φv k r t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qlmv t) + expJet2Rhs g gi hC p v Φv l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQlrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qlrv t) + expJet2Rhs g gi hC p v Φv l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qmrv t) + expJet2Rhs g gi hC p v Φv m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkw t) + expJet2Rhs g gi hC p w Φw h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlw t) + expJet2Rhs g gi hC p w Φw h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhmw t) + expJet2Rhs g gi hC p w Φw h m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhrw t) + expJet2Rhs g gi hC p w Φw h r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklw t) + expJet2Rhs g gi hC p w Φw k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qkmw t) + expJet2Rhs g gi hC p w Φw k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQkrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qkrw t) + expJet2Rhs g gi hC p w Φw k r t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qlmw t) + expJet2Rhs g gi hC p w Φw l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQlrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qlrw t) + expJet2Rhs g gi hC p w Φw l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qmrw t) + expJet2Rhs g gi hC p w Φw m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhklv t) + expJet3Rhs g gi hC p v Φv Qklv Qhlv Qhkv h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkmv t) + expJet3Rhs g gi hC p v Φv Qkmv Qhmv Qhkv h k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkrv t) + expJet3Rhs g gi hC p v Φv Qkrv Qhrv Qhkv h k r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlmv t) + expJet3Rhs g gi hC p v Φv Qlmv Qhmv Qhlv h l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlrv t) + expJet3Rhs g gi hC p v Φv Qlrv Qhrv Qhlv h l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhmrv t) + expJet3Rhs g gi hC p v Φv Qmrv Qhrv Qhmv h m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklmv t) + expJet3Rhs g gi hC p v Φv Qlmv Qkmv Qklv k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklrv t) + expJet3Rhs g gi hC p v Φv Qlrv Qkrv Qklv k l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qkmrv t) + expJet3Rhs g gi hC p v Φv Qmrv Qkrv Qkmv k m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qlmrv t) + expJet3Rhs g gi hC p v Φv Qmrv Qlrv Qlmv l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhklw t) + expJet3Rhs g gi hC p w Φw Qklw Qhlw Qhkw h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkmw t) + expJet3Rhs g gi hC p w Φw Qkmw Qhmw Qhkw h k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkrw t) + expJet3Rhs g gi hC p w Φw Qkrw Qhrw Qhkw h k r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlmw t) + expJet3Rhs g gi hC p w Φw Qlmw Qhmw Qhlw h l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlrw t) + expJet3Rhs g gi hC p w Φw Qlrw Qhrw Qhlw h l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhmrw t) + expJet3Rhs g gi hC p w Φw Qmrw Qhrw Qhmw h m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklmw t) + expJet3Rhs g gi hC p w Φw Qlmw Qkmw Qklw k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklrw t) + expJet3Rhs g gi hC p w Φw Qlrw Qkrw Qklw k l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qkmrw t) + expJet3Rhs g gi hC p w Φw Qmrw Qkrw Qkmw k m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qlmrw t) + expJet3Rhs g gi hC p w Φw Qmrw Qlrw Qlmw l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhklmv t) + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhklrv t) + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhrv Qklv Qkrv Qlrv Qhklv Qhkrv Qhlrv Qklrv h k l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkmrv t) + expJet4Rhs g gi hC p v Φv Qhkv Qhmv Qhrv Qkmv Qkrv Qmrv Qhkmv Qhkrv Qhmrv Qkmrv h k m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlmrv t) + expJet4Rhs g gi hC p v Φv Qhlv Qhmv Qhrv Qlmv Qlrv Qmrv Qhlmv Qhlrv Qhmrv Qlmrv h l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmrvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmrv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklmrv t) + expJet4Rhs g gi hC p v Φv Qklv Qkmv Qkrv Qlmv Qlrv Qmrv Qklmv Qklrv Qkmrv Qlmrv k l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhklmw t) + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhklrw t) + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhrw Qklw Qkrw Qlrw Qhklw Qhkrw Qhlrw Qklrw h k l r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkmrw t) + expJet4Rhs g gi hC p w Φw Qhkw Qhmw Qhrw Qkmw Qkrw Qmrw Qhkmw Qhkrw Qhmrw Qkmrw h k m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlmrw t) + expJet4Rhs g gi hC p w Φw Qhlw Qhmw Qhrw Qlmw Qlrw Qmrw Qhlmw Qhlrw Qhmrw Qlmrw h l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmrwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmrw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklmrw t) + expJet4Rhs g gi hC p w Φw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw Qklmw Qklrw Qkmrw Qlmrw k l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hRvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t) + expJet5Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qhrv Qklv Qkmv Qkrv Qlmv Qlrv Qmrv Qhklv Qhkmv Qhkrv Qhlmv Qhlrv Qhmrv Qklmv Qklrv Qkmrv Qlmrv Qhklmv Qhklrv Qhkmrv Qhlmrv Qklmrv h k l m r t) (Set.Icc (0 : ℝ) 1) t)
    (hRwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t) + expJet5Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qhrw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw Qhklw Qhkmw Qhkrw Qhlmw Qhlrw Qhmrw Qklmw Qklrw Qkmrw Qlmrw Qhklmw Qhklrw Qhkmrw Qhlmrw Qklmrw h k l m r t) (Set.Icc (0 : ℝ) 1) t)
    : ‖Rv 1 - Rw 1‖
      ≤ expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
          Kstar Kstar2 Kstar3 Kstar4 Kstar5 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p w hw
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hSv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hSw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p w t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hw hC₀)
  have hKstarv := hKstar v hv
  have hKstarw := hKstar w hw
  have hK2v := hKstar2f v hv
  have hK2w := hKstar2f w hw
  have hK3v := hKstar3f v hv
  have hK3w := hKstar3f w hw
  have hK4v := hKstar4f v hv
  have hK4w := hKstar4f w hw
  have hK5v := hKstar5f v hv
  have hK5w := hKstar5f w hw
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  have hιm : ‖expJetIota (n := n) m‖ ≤ ‖m‖ :=
    ((expJetIota (n := n)).le_opNorm m).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg m))
  have hιr : ‖expJetIota (n := n) r‖ ≤ ‖r‖ :=
    ((expJetIota (n := n)).le_opNorm r).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg r))
  have hΦvnorm := expJetFund_norm_le_exp g gi hC p v Φv Kstar hKstar0 hKstarv hΦv0 hΦvd
  have hΦwnorm := expJetFund_norm_le_exp g gi hC p w Φw Kstar hKstar0 hKstarw hΦw0 hΦwd
  have hdist0 : dist (expTube g gi hC p v 0) (expTube g gi hC p w 0) = ‖v - w‖ := by
    rw [hY0v, hY0w, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi (S := S) (K := Kf) hLipF
    (fun t ht => hYdv t (hIcc_Ioo t ht)) (fun t ht => hYdw t (hIcc_Ioo t ht)) hSv hSw
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t - expTube g gi hC p w t‖ ≤ ‖v - w‖ * Real.exp (Kf : ℝ) := by
    intro t ht
    have hh := htwopoint t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  have hDFdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) - (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD2diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t) - (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)‖
        ≤ (Ld2f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD2F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD3diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t) - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p w t)‖
        ≤ (Ld3f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD3F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD4diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t) - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p w t)‖
        ≤ (Ld4f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD4F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD5diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) (expTube g gi hC p v t) - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) (expTube g gi hC p w t)‖
        ≤ (Ld5f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD5F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hΦdiff := expFund_two_pt_diff_Icc g gi hC p v w Kf Ldf Kstar hKstar0 hLipF hLipDF
    hKstarv hKstarw hv hw Φv Φw hΦv0 hΦw0 hΦvd hΦwd
  have hCe2 : 0 ≤ expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 :=
    expJet2VtpConst_nonneg _ _ _ _ _ Ldf.2 Ld2f.2 hKstar20
  have hCe3 : 0 ≤ expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3 :=
    expJet3VtpConst_nonneg _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 hKstar20 hKstar30
  have hCe4 : 0 ≤ expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) Kstar Kstar2 Kstar3 Kstar4 :=
    expJet4VtpConst_nonneg _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 hKstar20 hKstar30 hKstar40
  have hval_hkv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv h k Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhkv hQhkv0 hQhkvd
  have hval_hlv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv h l Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhlv hQhlv0 hQhlvd
  have hval_hmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv h m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhmv hQhmv0 hQhmvd
  have hval_hrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhrv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv h r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhrv hQhrv0 hQhrvd
  have hval_klv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv k l Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qklv hQklv0 hQklvd
  have hval_kmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv k m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qkmv hQkmv0 hQkmvd
  have hval_krv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkrv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv k r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qkrv hQkrv0 hQkrvd
  have hval_lmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv l m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qlmv hQlmv0 hQlmvd
  have hval_lrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlrv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv l r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qlrv hQlrv0 hQlrvd
  have hval_mrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmrv t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p v Φv m r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qmrv hQmrv0 hQmrvd
  have hval_hkw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw h k Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhkw hQhkw0 hQhkwd
  have hval_hlw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw h l Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhlw hQhlw0 hQhlwd
  have hval_hmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw h m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhmw hQhmw0 hQhmwd
  have hval_hrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhrw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw h r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhrw hQhrw0 hQhrwd
  have hval_klw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw k l Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qklw hQklw0 hQklwd
  have hval_kmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw k m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qkmw hQkmw0 hQkmwd
  have hval_krw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkrw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw k r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qkrw hQkrw0 hQkrwd
  have hval_lmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw l m Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qlmw hQlmw0 hQlmwd
  have hval_lrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlrw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw l r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qlrw hQlrw0 hQlrwd
  have hval_mrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmrw t‖ ≤ (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖ :=
    expJet2Fund_value_bound_Icc g gi hC p w Φw m r Kstar Kstar2 (Real.exp Kstar)
      hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qmrw hQmrw0 hQmrwd
  have hval3_hklv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qklv Qhlv Qhkv h k l
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_klv hval_hlv hval_hkv Qhklv hQhklv0 hQhklvd t ht).trans (le_of_eq (by ring))
  have hval3_hkmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qkmv Qhmv Qhkv h k m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_kmv hval_hmv hval_hkv Qhkmv hQhkmv0 hQhkmvd t ht).trans (le_of_eq (by ring))
  have hval3_hkrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qkrv Qhrv Qhkv h k r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_krv hval_hrv hval_hkv Qhkrv hQhkrv0 hQhkrvd t ht).trans (le_of_eq (by ring))
  have hval3_hlmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlmv Qhmv Qhlv h l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lmv hval_hmv hval_hlv Qhlmv hQhlmv0 hQhlmvd t ht).trans (le_of_eq (by ring))
  have hval3_hlrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlrv Qhrv Qhlv h l r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lrv hval_hrv hval_hlv Qhlrv hQhlrv0 hQhlrvd t ht).trans (le_of_eq (by ring))
  have hval3_hmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qmrv Qhrv Qhmv h m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_mrv hval_hrv hval_hmv Qhmrv hQhmrv0 hQhmrvd t ht).trans (le_of_eq (by ring))
  have hval3_klmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlmv Qkmv Qklv k l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lmv hval_kmv hval_klv Qklmv hQklmv0 hQklmvd t ht).trans (le_of_eq (by ring))
  have hval3_klrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlrv Qkrv Qklv k l r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lrv hval_krv hval_klv Qklrv hQklrv0 hQklrvd t ht).trans (le_of_eq (by ring))
  have hval3_kmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qmrv Qkrv Qkmv k m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_mrv hval_krv hval_kmv Qkmrv hQkmrv0 hQkmrvd t ht).trans (le_of_eq (by ring))
  have hval3_lmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmrv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qmrv Qlrv Qlmv l m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_mrv hval_lrv hval_lmv Qlmrv hQlmrv0 hQlmrvd t ht).trans (le_of_eq (by ring))
  have hval3_hklw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qklw Qhlw Qhkw h k l
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_klw hval_hlw hval_hkw Qhklw hQhklw0 hQhklwd t ht).trans (le_of_eq (by ring))
  have hval3_hkmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qkmw Qhmw Qhkw h k m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_kmw hval_hmw hval_hkw Qhkmw hQhkmw0 hQhkmwd t ht).trans (le_of_eq (by ring))
  have hval3_hkrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qkrw Qhrw Qhkw h k r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_krw hval_hrw hval_hkw Qhkrw hQhkrw0 hQhkrwd t ht).trans (le_of_eq (by ring))
  have hval3_hlmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlmw Qhmw Qhlw h l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lmw hval_hmw hval_hlw Qhlmw hQhlmw0 hQhlmwd t ht).trans (le_of_eq (by ring))
  have hval3_hlrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlrw Qhrw Qhlw h l r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lrw hval_hrw hval_hlw Qhlrw hQhlrw0 hQhlrwd t ht).trans (le_of_eq (by ring))
  have hval3_hmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qmrw Qhrw Qhmw h m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_mrw hval_hrw hval_hmw Qhmrw hQhmrw0 hQhmrwd t ht).trans (le_of_eq (by ring))
  have hval3_klmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlmw Qkmw Qklw k l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lmw hval_kmw hval_klw Qklmw hQklmw0 hQklmwd t ht).trans (le_of_eq (by ring))
  have hval3_klrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlrw Qkrw Qklw k l r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lrw hval_krw hval_klw Qklrw hQklrw0 hQklrwd t ht).trans (le_of_eq (by ring))
  have hval3_kmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qmrw Qkrw Qkmw k m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_mrw hval_krw hval_kmw Qkmrw hQkmrw0 hQkmrwd t ht).trans (le_of_eq (by ring))
  have hval3_lmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmrw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qmrw Qlrw Qlmw l m r
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_mrw hval_lrw hval_lmw Qlmrw hQlmrw0 hQlmrwd t ht).trans (le_of_eq (by ring))
  have hval4_hklmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklmv t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv
      Qhklv Qhkmv Qhlmv Qklmv h k l m
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK4v hK3v hK2v hΦvnorm
      hval_hkv hval_hlv hval_hmv hval_klv hval_kmv hval_lmv hval3_hklv hval3_hkmv hval3_hlmv hval3_klmv Qhklmv hQhklmv0 hQhklmvd t ht).trans (le_of_eq (by ring))
  have hval4_hklrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklrv t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p v Φv Qhkv Qhlv Qhrv Qklv Qkrv Qlrv
      Qhklv Qhkrv Qhlrv Qklrv h k l r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK4v hK3v hK2v hΦvnorm
      hval_hkv hval_hlv hval_hrv hval_klv hval_krv hval_lrv hval3_hklv hval3_hkrv hval3_hlrv hval3_klrv Qhklrv hQhklrv0 hQhklrvd t ht).trans (le_of_eq (by ring))
  have hval4_hkmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmrv t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p v Φv Qhkv Qhmv Qhrv Qkmv Qkrv Qmrv
      Qhkmv Qhkrv Qhmrv Qkmrv h k m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK4v hK3v hK2v hΦvnorm
      hval_hkv hval_hmv hval_hrv hval_kmv hval_krv hval_mrv hval3_hkmv hval3_hkrv hval3_hmrv hval3_kmrv Qhkmrv hQhkmrv0 hQhkmrvd t ht).trans (le_of_eq (by ring))
  have hval4_hlmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmrv t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p v Φv Qhlv Qhmv Qhrv Qlmv Qlrv Qmrv
      Qhlmv Qhlrv Qhmrv Qlmrv h l m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK4v hK3v hK2v hΦvnorm
      hval_hlv hval_hmv hval_hrv hval_lmv hval_lrv hval_mrv hval3_hlmv hval3_hlrv hval3_hmrv hval3_lmrv Qhlmrv hQhlmrv0 hQhlmrvd t ht).trans (le_of_eq (by ring))
  have hval4_klmrv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmrv t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p v Φv Qklv Qkmv Qkrv Qlmv Qlrv Qmrv
      Qklmv Qklrv Qkmrv Qlmrv k l m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK4v hK3v hK2v hΦvnorm
      hval_klv hval_kmv hval_krv hval_lmv hval_lrv hval_mrv hval3_klmv hval3_klrv hval3_kmrv hval3_lmrv Qklmrv hQklmrv0 hQklmrvd t ht).trans (le_of_eq (by ring))
  have hval4_hklmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklmw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw
      Qhklw Qhkmw Qhlmw Qklmw h k l m
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_hkw hval_hlw hval_hmw hval_klw hval_kmw hval_lmw hval3_hklw hval3_hkmw hval3_hlmw hval3_klmw Qhklmw hQhklmw0 hQhklmwd t ht).trans (le_of_eq (by ring))
  have hval4_hklrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklrw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qhkw Qhlw Qhrw Qklw Qkrw Qlrw
      Qhklw Qhkrw Qhlrw Qklrw h k l r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_hkw hval_hlw hval_hrw hval_klw hval_krw hval_lrw hval3_hklw hval3_hkrw hval3_hlrw hval3_klrw Qhklrw hQhklrw0 hQhklrwd t ht).trans (le_of_eq (by ring))
  have hval4_hkmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmrw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qhkw Qhmw Qhrw Qkmw Qkrw Qmrw
      Qhkmw Qhkrw Qhmrw Qkmrw h k m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_hkw hval_hmw hval_hrw hval_kmw hval_krw hval_mrw hval3_hkmw hval3_hkrw hval3_hmrw hval3_kmrw Qhkmrw hQhkmrw0 hQhkmrwd t ht).trans (le_of_eq (by ring))
  have hval4_hlmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmrw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qhlw Qhmw Qhrw Qlmw Qlrw Qmrw
      Qhlmw Qhlrw Qhmrw Qlmrw h l m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_hlw hval_hmw hval_hrw hval_lmw hval_lrw hval_mrw hval3_hlmw hval3_hlrw hval3_hmrw hval3_lmrw Qhlmrw hQhlmrw0 hQhlmrwd t ht).trans (le_of_eq (by ring))
  have hval4_klmrw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmrw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw
      Qklmw Qklrw Qkmrw Qlmrw k l m r
      Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_klw hval_kmw hval_krw hval_lmw hval_lrw hval_mrw hval3_klmw hval3_klrw hval3_kmrw hval3_lmrw Qklmrw hQklmrw0 hQklmrwd t ht).trans (le_of_eq (by ring))
  have htp_hk := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhkw h k hQhkv0 hQhkw0 hQhkvd hQhkwd
  have htp_hl := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhlv Qhlw h l hQhlv0 hQhlw0 hQhlvd hQhlwd
  have htp_hm := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhmv Qhmw h m hQhmv0 hQhmw0 hQhmvd hQhmwd
  have htp_hr := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhrv Qhrw h r hQhrv0 hQhrw0 hQhrvd hQhrwd
  have htp_kl := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qklv Qklw k l hQklv0 hQklw0 hQklvd hQklwd
  have htp_km := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qkmv Qkmw k m hQkmv0 hQkmw0 hQkmvd hQkmwd
  have htp_kr := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qkrv Qkrw k r hQkrv0 hQkrw0 hQkrvd hQkrwd
  have htp_lm := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qlmw l m hQlmv0 hQlmw0 hQlmvd hQlmwd
  have htp_lr := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlrv Qlrw l r hQlrv0 hQlrw0 hQlrvd hQlrwd
  have htp_mr := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qmrv Qmrw m r hQmrv0 hQmrw0 hQmrvd hQmrwd
  have htp3_hkl := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qklv Qhlv Qhkv Qklw Qhlw Qhkw Qhklv Qhklw h k l
    hQklv0 hQhlv0 hQhkv0 hQklw0 hQhlw0 hQhkw0 hQhklv0 hQhklw0
    hQklvd hQhlvd hQhkvd hQklwd hQhlwd hQhkwd hQhklvd hQhklwd
  have htp3_hkm := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qkmv Qhmv Qhkv Qkmw Qhmw Qhkw Qhkmv Qhkmw h k m
    hQkmv0 hQhmv0 hQhkv0 hQkmw0 hQhmw0 hQhkw0 hQhkmv0 hQhkmw0
    hQkmvd hQhmvd hQhkvd hQkmwd hQhmwd hQhkwd hQhkmvd hQhkmwd
  have htp3_hkr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qkrv Qhrv Qhkv Qkrw Qhrw Qhkw Qhkrv Qhkrw h k r
    hQkrv0 hQhrv0 hQhkv0 hQkrw0 hQhrw0 hQhkw0 hQhkrv0 hQhkrw0
    hQkrvd hQhrvd hQhkvd hQkrwd hQhrwd hQhkwd hQhkrvd hQhkrwd
  have htp3_hlm := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qhmv Qhlv Qlmw Qhmw Qhlw Qhlmv Qhlmw h l m
    hQlmv0 hQhmv0 hQhlv0 hQlmw0 hQhmw0 hQhlw0 hQhlmv0 hQhlmw0
    hQlmvd hQhmvd hQhlvd hQlmwd hQhmwd hQhlwd hQhlmvd hQhlmwd
  have htp3_hlr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlrv Qhrv Qhlv Qlrw Qhrw Qhlw Qhlrv Qhlrw h l r
    hQlrv0 hQhrv0 hQhlv0 hQlrw0 hQhrw0 hQhlw0 hQhlrv0 hQhlrw0
    hQlrvd hQhrvd hQhlvd hQlrwd hQhrwd hQhlwd hQhlrvd hQhlrwd
  have htp3_hmr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qmrv Qhrv Qhmv Qmrw Qhrw Qhmw Qhmrv Qhmrw h m r
    hQmrv0 hQhrv0 hQhmv0 hQmrw0 hQhrw0 hQhmw0 hQhmrv0 hQhmrw0
    hQmrvd hQhrvd hQhmvd hQmrwd hQhrwd hQhmwd hQhmrvd hQhmrwd
  have htp3_klm := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qkmv Qklv Qlmw Qkmw Qklw Qklmv Qklmw k l m
    hQlmv0 hQkmv0 hQklv0 hQlmw0 hQkmw0 hQklw0 hQklmv0 hQklmw0
    hQlmvd hQkmvd hQklvd hQlmwd hQkmwd hQklwd hQklmvd hQklmwd
  have htp3_klr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlrv Qkrv Qklv Qlrw Qkrw Qklw Qklrv Qklrw k l r
    hQlrv0 hQkrv0 hQklv0 hQlrw0 hQkrw0 hQklw0 hQklrv0 hQklrw0
    hQlrvd hQkrvd hQklvd hQlrwd hQkrwd hQklwd hQklrvd hQklrwd
  have htp3_kmr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qmrv Qkrv Qkmv Qmrw Qkrw Qkmw Qkmrv Qkmrw k m r
    hQmrv0 hQkrv0 hQkmv0 hQmrw0 hQkrw0 hQkmw0 hQkmrv0 hQkmrw0
    hQmrvd hQkrvd hQkmvd hQmrwd hQkrwd hQkmwd hQkmrvd hQkmrwd
  have htp3_lmr := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qmrv Qlrv Qlmv Qmrw Qlrw Qlmw Qlmrv Qlmrw l m r
    hQmrv0 hQlrv0 hQlmv0 hQmrw0 hQlrw0 hQlmw0 hQlmrv0 hQlmrw0
    hQmrvd hQlrvd hQlmvd hQmrwd hQlrwd hQlmwd hQlmrvd hQlmrwd
  have htp4_hklm := expJet4Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40 hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhlv Qhmv Qklv Qkmv Qlmv
    Qhkw Qhlw Qhmw Qklw Qkmw Qlmw
    Qhklv Qhkmv Qhlmv Qklmv
    Qhklw Qhkmw Qhlmw Qklmw
    Qhklmv Qhklmw h k l m
    hQhkv0 hQhlv0 hQhmv0 hQklv0 hQkmv0 hQlmv0
    hQhkw0 hQhlw0 hQhmw0 hQklw0 hQkmw0 hQlmw0
    hQhklv0 hQhkmv0 hQhlmv0 hQklmv0
    hQhklw0 hQhkmw0 hQhlmw0 hQklmw0
    hQhklmv0 hQhklmw0
    hQhkvd hQhlvd hQhmvd hQklvd hQkmvd hQlmvd
    hQhkwd hQhlwd hQhmwd hQklwd hQkmwd hQlmwd
    hQhklvd hQhkmvd hQhlmvd hQklmvd
    hQhklwd hQhkmwd hQhlmwd hQklmwd
    hQhklmvd hQhklmwd
  have htp4_hklr := expJet4Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40 hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhlv Qhrv Qklv Qkrv Qlrv
    Qhkw Qhlw Qhrw Qklw Qkrw Qlrw
    Qhklv Qhkrv Qhlrv Qklrv
    Qhklw Qhkrw Qhlrw Qklrw
    Qhklrv Qhklrw h k l r
    hQhkv0 hQhlv0 hQhrv0 hQklv0 hQkrv0 hQlrv0
    hQhkw0 hQhlw0 hQhrw0 hQklw0 hQkrw0 hQlrw0
    hQhklv0 hQhkrv0 hQhlrv0 hQklrv0
    hQhklw0 hQhkrw0 hQhlrw0 hQklrw0
    hQhklrv0 hQhklrw0
    hQhkvd hQhlvd hQhrvd hQklvd hQkrvd hQlrvd
    hQhkwd hQhlwd hQhrwd hQklwd hQkrwd hQlrwd
    hQhklvd hQhkrvd hQhlrvd hQklrvd
    hQhklwd hQhkrwd hQhlrwd hQklrwd
    hQhklrvd hQhklrwd
  have htp4_hkmr := expJet4Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40 hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhmv Qhrv Qkmv Qkrv Qmrv
    Qhkw Qhmw Qhrw Qkmw Qkrw Qmrw
    Qhkmv Qhkrv Qhmrv Qkmrv
    Qhkmw Qhkrw Qhmrw Qkmrw
    Qhkmrv Qhkmrw h k m r
    hQhkv0 hQhmv0 hQhrv0 hQkmv0 hQkrv0 hQmrv0
    hQhkw0 hQhmw0 hQhrw0 hQkmw0 hQkrw0 hQmrw0
    hQhkmv0 hQhkrv0 hQhmrv0 hQkmrv0
    hQhkmw0 hQhkrw0 hQhmrw0 hQkmrw0
    hQhkmrv0 hQhkmrw0
    hQhkvd hQhmvd hQhrvd hQkmvd hQkrvd hQmrvd
    hQhkwd hQhmwd hQhrwd hQkmwd hQkrwd hQmrwd
    hQhkmvd hQhkrvd hQhmrvd hQkmrvd
    hQhkmwd hQhkrwd hQhmrwd hQkmrwd
    hQhkmrvd hQhkmrwd
  have htp4_hlmr := expJet4Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40 hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhlv Qhmv Qhrv Qlmv Qlrv Qmrv
    Qhlw Qhmw Qhrw Qlmw Qlrw Qmrw
    Qhlmv Qhlrv Qhmrv Qlmrv
    Qhlmw Qhlrw Qhmrw Qlmrw
    Qhlmrv Qhlmrw h l m r
    hQhlv0 hQhmv0 hQhrv0 hQlmv0 hQlrv0 hQmrv0
    hQhlw0 hQhmw0 hQhrw0 hQlmw0 hQlrw0 hQmrw0
    hQhlmv0 hQhlrv0 hQhmrv0 hQlmrv0
    hQhlmw0 hQhlrw0 hQhmrw0 hQlmrw0
    hQhlmrv0 hQhlmrw0
    hQhlvd hQhmvd hQhrvd hQlmvd hQlrvd hQmrvd
    hQhlwd hQhmwd hQhrwd hQlmwd hQlrwd hQmrwd
    hQhlmvd hQhlrvd hQhmrvd hQlmrvd
    hQhlmwd hQhlrwd hQhmrwd hQlmrwd
    hQhlmrvd hQhlmrwd
  have htp4_klmr := expJet4Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40 hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qklv Qkmv Qkrv Qlmv Qlrv Qmrv
    Qklw Qkmw Qkrw Qlmw Qlrw Qmrw
    Qklmv Qklrv Qkmrv Qlmrv
    Qklmw Qklrw Qkmrw Qlmrw
    Qklmrv Qklmrw k l m r
    hQklv0 hQkmv0 hQkrv0 hQlmv0 hQlrv0 hQmrv0
    hQklw0 hQkmw0 hQkrw0 hQlmw0 hQlrw0 hQmrw0
    hQklmv0 hQklrv0 hQkmrv0 hQlmrv0
    hQklmw0 hQklrw0 hQkmrw0 hQlmrw0
    hQklmrv0 hQklmrw0
    hQklvd hQkmvd hQkrvd hQlmvd hQlrvd hQmrvd
    hQklwd hQkmwd hQkrwd hQlmwd hQlrwd hQmrwd
    hQklmvd hQklrvd hQkmrvd hQlmrvd
    hQklmwd hQklrwd hQkmrwd hQlmrwd
    hQklmrvd hQklmrwd
  have hRwval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Rw t‖ ≤ ((Kstar5 * Real.exp Kstar ^ 5 + 10 * (Kstar4 * Real.exp Kstar ^ 3 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) + 15 * (Kstar3 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) + 10 * (Kstar3 * Real.exp Kstar ^ 2 * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) + 10 * (Kstar2 * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) + 5 * (Kstar2 * Real.exp Kstar * ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar))) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ :=
    fun t ht => (expJet5Fund_value_bound_Icc g gi hC p w Φw Qhkw Qhlw Qhmw Qhrw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw Qhklw Qhkmw Qhkrw Qhlmw Qhlrw Qhmrw Qklmw Qklrw Qkmrw Qlmrw Qhklmw Qhklrw Qhkmrw Qhlmrw Qklmrw
      h k l m r Kstar Kstar5 Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖r‖)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖m‖ * ‖r‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖l‖ * ‖m‖ * ‖r‖)
      (((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖)
      (((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖)
      (((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖)
      (((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖)
      (((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖)
      hKstar0 hKstar50 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le
      hKstarw hK5w hK4w hK3w hK2w hΦwnorm
      hval_hkw hval_hlw hval_hmw hval_hrw hval_klw hval_kmw hval_krw hval_lmw hval_lrw hval_mrw
      hval3_hklw hval3_hkmw hval3_hkrw hval3_hlmw hval3_hlrw hval3_hmrw hval3_klmw hval3_klrw hval3_kmrw hval3_lmrw
      hval4_hklmw hval4_hklrw hval4_hkmrw hval4_hlmrw hval4_klmrw
      Rw hRw0 hRwd t ht).trans (le_of_eq (by ring))
  set E : ℝ := Real.exp Kstar with hEdef
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKfdef
  set CPD : ℝ := (Ldf : ℝ) * eKf * E * E with hCPDdef
  set B2 : ℝ := Kstar2 * E ^ 2 * E with hB2def
  set B3 : ℝ := (Kstar3 * E ^ 3 + 3 * Kstar2 * E * B2) * E with hB3def
  set B4 : ℝ := (Kstar4 * E ^ 4 + 6 * Kstar3 * E ^ 2 * B2 + 3 * Kstar2 * B2 ^ 2 + 4 * Kstar2 * E * B3) * E with hB4def
  set B5 : ℝ := (Kstar5 * E ^ 5 + 10 * (Kstar4 * E ^ 3 * B2) + 15 * (Kstar3 * E * B2 ^ 2) + 10 * (Kstar3 * E ^ 2 * B3) + 10 * (Kstar2 * B3 * B2) + 5 * (Kstar2 * E * B4)) * E with hB5def
  set T2 : ℝ := expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 with hT2def
  set T3 : ℝ := expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3 with hT3def
  set T4 : ℝ := expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) Kstar Kstar2 Kstar3 Kstar4 with hT4def
  have hE0 : (0:ℝ) ≤ E := by rw [hEdef]; positivity
  have heKf0 : (0:ℝ) ≤ eKf := by rw [heKfdef]; positivity
  have hCPD0 : (0:ℝ) ≤ CPD := by rw [hCPDdef]; positivity
  have hB20 : (0:ℝ) ≤ B2 := by rw [hB2def]; positivity
  have hB30 : (0:ℝ) ≤ B3 := by rw [hB3def]; positivity
  have hB40 : (0:ℝ) ≤ B4 := by rw [hB4def]; positivity
  have hB50 : (0:ℝ) ≤ B5 := by rw [hB5def]; positivity
  have hT20 : (0:ℝ) ≤ T2 := by rw [hT2def]; exact hCe2
  have hT30 : (0:ℝ) ≤ T3 := by rw [hT3def]; exact hCe3
  have hT40 : (0:ℝ) ≤ T4 := by rw [hT4def]; exact hCe4
  clear_value B5 B4 B3 B2 T4 T3 T2 CPD eKf E
  set ρ5 : ℝ := ((Ldf : ℝ) * (‖v - w‖ * eKf)) * (B5 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖) + ((Kstar5 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) + Kstar5 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) + Kstar5 * (E * ‖h‖) * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) + Kstar5 * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖m‖) * (E * ‖r‖) + Kstar5 * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (CPD * ‖v - w‖ * ‖r‖) + ((Ld5f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (E * ‖r‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖k‖) + Kstar4 * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖k‖) + Kstar4 * (E * ‖l‖) * (E * ‖m‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖k‖) + Kstar4 * (E * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖k‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖k‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖l‖) + Kstar4 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖l‖) + Kstar4 * (E * ‖k‖) * (E * ‖m‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖l‖) + Kstar4 * (E * ‖k‖) * (E * ‖m‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖l‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖l‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖l‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖m‖) + Kstar4 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖m‖) + Kstar4 * (E * ‖k‖) * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖m‖) + Kstar4 * (E * ‖k‖) * (E * ‖l‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖m‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖l‖) * (E * ‖r‖) * (B2 * ‖h‖ * ‖m‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (B2 * ‖h‖ * ‖r‖) + Kstar4 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖m‖) * (B2 * ‖h‖ * ‖r‖) + Kstar4 * (E * ‖k‖) * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖h‖ * ‖r‖) + Kstar4 * (E * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖r‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖l‖) * (E * ‖m‖) * (B2 * ‖h‖ * ‖r‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖m‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar4 * (E * ‖h‖) * (E * ‖m‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar4 * (E * ‖h‖) * (E * ‖m‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖l‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖m‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖l‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖l‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (E * ‖l‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖m‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖l‖) * (E * ‖r‖) * (B2 * ‖k‖ * ‖m‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖l‖) * (E * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖l‖) * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖r‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖l‖) * (E * ‖m‖) * (B2 * ‖k‖ * ‖r‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖k‖) * (E * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖m‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖k‖) * (E * ‖r‖) * (B2 * ‖l‖ * ‖m‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖k‖) * (E * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖r‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖k‖) * (E * ‖m‖) * (B2 * ‖l‖ * ‖r‖)) + (Kstar4 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar4 * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (T2 * ‖v - w‖ * ‖m‖ * ‖r‖) + ((Ld4f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖k‖) * (E * ‖l‖) * (B2 * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (B2 * ‖k‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (B2 * ‖k‖ * ‖l‖) * (T2 * ‖v - w‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (B2 * ‖k‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (B2 * ‖k‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (B2 * ‖k‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (B2 * ‖k‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (B2 * ‖k‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖h‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖h‖) * (B2 * ‖k‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (B2 * ‖k‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (B2 * ‖h‖ * ‖l‖) * (T2 * ‖v - w‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (B2 * ‖h‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖k‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖k‖) * (B2 * ‖h‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖l‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖k‖) * (B2 * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (B2 * ‖h‖ * ‖k‖) * (T2 * ‖v - w‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖l‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (B2 * ‖h‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖l‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖l‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖l‖) * (B2 * ‖h‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖m‖) * (B2 * ‖h‖ * ‖k‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖m‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖m‖) * (B2 * ‖h‖ * ‖l‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖m‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖m‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖m‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖m‖) * (B2 * ‖h‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖l‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖m‖) * (B2 * ‖h‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖r‖) * (B2 * ‖h‖ * ‖k‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖r‖) * (B2 * ‖h‖ * ‖k‖) * (B2 * ‖l‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖r‖) * (B2 * ‖h‖ * ‖l‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖r‖) * (B2 * ‖h‖ * ‖l‖) * (B2 * ‖k‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖r‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖r‖) * (B2 * ‖h‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖l‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖r‖) * (B2 * ‖h‖ * ‖m‖) * (B2 * ‖k‖ * ‖l‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖m‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖m‖) * (CPD * ‖v - w‖ * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖l‖) + Kstar3 * (E * ‖m‖) * (E * ‖r‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖m‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖l‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖m‖) + Kstar3 * (E * ‖l‖) * (E * ‖r‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖k‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖l‖) * (E * ‖m‖) * (B3 * ‖h‖ * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (CPD * ‖v - w‖ * ‖m‖) * (B3 * ‖h‖ * ‖k‖ * ‖r‖) + Kstar3 * (E * ‖l‖) * (E * ‖m‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (E * ‖m‖) * (B3 * ‖h‖ * ‖k‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖r‖) * (B3 * ‖h‖ * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖k‖) * (E * ‖r‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖l‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖r‖) * (B3 * ‖h‖ * ‖l‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖m‖) * (B3 * ‖h‖ * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖m‖) * (B3 * ‖h‖ * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (E * ‖m‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖l‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖m‖) * (B3 * ‖h‖ * ‖l‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖k‖) * (E * ‖l‖) * (B3 * ‖h‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (CPD * ‖v - w‖ * ‖l‖) * (B3 * ‖h‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖k‖) * (E * ‖l‖) * (T3 * ‖v - w‖ * ‖h‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (E * ‖l‖) * (B3 * ‖h‖ * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖r‖) * (B3 * ‖k‖ * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖r‖) * (B3 * ‖k‖ * ‖l‖ * ‖m‖) + Kstar3 * (E * ‖h‖) * (E * ‖r‖) * (T3 * ‖v - w‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖r‖) * (B3 * ‖k‖ * ‖l‖ * ‖m‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖m‖) * (B3 * ‖k‖ * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖m‖) * (B3 * ‖k‖ * ‖l‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (E * ‖m‖) * (T3 * ‖v - w‖ * ‖k‖ * ‖l‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖m‖) * (B3 * ‖k‖ * ‖l‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖l‖) * (B3 * ‖k‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖l‖) * (B3 * ‖k‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (E * ‖l‖) * (T3 * ‖v - w‖ * ‖k‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖l‖) * (B3 * ‖k‖ * ‖m‖ * ‖r‖)) + (Kstar3 * (CPD * ‖v - w‖ * ‖h‖) * (E * ‖k‖) * (B3 * ‖l‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (CPD * ‖v - w‖ * ‖k‖) * (B3 * ‖l‖ * ‖m‖ * ‖r‖) + Kstar3 * (E * ‖h‖) * (E * ‖k‖) * (T3 * ‖v - w‖ * ‖l‖ * ‖m‖ * ‖r‖) + ((Ld3f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (E * ‖k‖) * (B3 * ‖l‖ * ‖m‖ * ‖r‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖) + Kstar2 * (B3 * ‖h‖ * ‖k‖ * ‖l‖) * (T2 * ‖v - w‖ * ‖m‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖k‖ * ‖l‖) * (B2 * ‖m‖ * ‖r‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖) + Kstar2 * (B3 * ‖h‖ * ‖k‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖k‖ * ‖m‖) * (B2 * ‖l‖ * ‖r‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖) + Kstar2 * (B3 * ‖h‖ * ‖k‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖l‖ * ‖m‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖k‖ * ‖r‖) * (B2 * ‖l‖ * ‖m‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖l‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖) + Kstar2 * (B3 * ‖h‖ * ‖l‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖l‖ * ‖m‖) * (B2 * ‖k‖ * ‖r‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖l‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖) + Kstar2 * (B3 * ‖h‖ * ‖l‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖m‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖l‖ * ‖r‖) * (B2 * ‖k‖ * ‖m‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖h‖ * ‖m‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖) + Kstar2 * (B3 * ‖h‖ * ‖m‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖k‖ * ‖l‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖h‖ * ‖m‖ * ‖r‖) * (B2 * ‖k‖ * ‖l‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖k‖ * ‖l‖ * ‖m‖) * (B2 * ‖h‖ * ‖r‖) + Kstar2 * (B3 * ‖k‖ * ‖l‖ * ‖m‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖k‖ * ‖l‖ * ‖m‖) * (B2 * ‖h‖ * ‖r‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖k‖ * ‖l‖ * ‖r‖) * (B2 * ‖h‖ * ‖m‖) + Kstar2 * (B3 * ‖k‖ * ‖l‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖m‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖k‖ * ‖l‖ * ‖r‖) * (B2 * ‖h‖ * ‖m‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖k‖ * ‖m‖ * ‖r‖) * (B2 * ‖h‖ * ‖l‖) + Kstar2 * (B3 * ‖k‖ * ‖m‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖l‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖k‖ * ‖m‖ * ‖r‖) * (B2 * ‖h‖ * ‖l‖)) + (Kstar2 * (T3 * ‖v - w‖ * ‖l‖ * ‖m‖ * ‖r‖) * (B2 * ‖h‖ * ‖k‖) + Kstar2 * (B3 * ‖l‖ * ‖m‖ * ‖r‖) * (T2 * ‖v - w‖ * ‖h‖ * ‖k‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (B3 * ‖l‖ * ‖m‖ * ‖r‖) * (B2 * ‖h‖ * ‖k‖)) + (Kstar2 * (CPD * ‖v - w‖ * ‖h‖) * (B4 * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖) + Kstar2 * (E * ‖h‖) * (T4 * ‖v - w‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖h‖) * (B4 * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖)) + (Kstar2 * (CPD * ‖v - w‖ * ‖k‖) * (B4 * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖) + Kstar2 * (E * ‖k‖) * (T4 * ‖v - w‖ * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖k‖) * (B4 * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖)) + (Kstar2 * (CPD * ‖v - w‖ * ‖l‖) * (B4 * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖) + Kstar2 * (E * ‖l‖) * (T4 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖l‖) * (B4 * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖)) + (Kstar2 * (CPD * ‖v - w‖ * ‖m‖) * (B4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖) + Kstar2 * (E * ‖m‖) * (T4 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖m‖) * (B4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖)) + (Kstar2 * (CPD * ‖v - w‖ * ‖r‖) * (B4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + Kstar2 * (E * ‖r‖) * (T4 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Ld2f : ℝ) * (‖v - w‖ * eKf)) * (E * ‖r‖) * (B4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖))) with hρ5def
  have hrbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
         + (expJet5Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qhrv Qklv Qkmv Qkrv Qlmv Qlrv Qmrv Qhklv Qhkmv Qhkrv Qhlmv Qhlrv Qhmrv Qklmv Qklrv Qkmrv Qlmrv Qhklmv Qhklrv Qhkmrv Qhlmrv Qklmrv h k l m r t
            - expJet5Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qhrw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw Qhklw Qhkmw Qhkrw Qhlmw Qhlrw Qhmrw Qklmw Qklrw Qkmrw Qlmrw Qhklmw Qhklrw Qhkmrw Qhlmrw Qklmrw h k l m r t)‖ ≤ ρ5 := by
    intro t ht
    simp only [expJet5Rhs_apply]
    have hpn_h : ‖Φv t (expJetIota h)‖ ≤ E * ‖h‖ :=
      ((Φv t).le_opNorm _).trans (mul_le_mul (hΦvnorm t ht) hιh (norm_nonneg _) hE0)
    have hpn'_h : ‖Φw t (expJetIota h)‖ ≤ E * ‖h‖ :=
      ((Φw t).le_opNorm _).trans (mul_le_mul (hΦwnorm t ht) hιh (norm_nonneg _) hE0)
    have hpn_k : ‖Φv t (expJetIota k)‖ ≤ E * ‖k‖ :=
      ((Φv t).le_opNorm _).trans (mul_le_mul (hΦvnorm t ht) hιk (norm_nonneg _) hE0)
    have hpn'_k : ‖Φw t (expJetIota k)‖ ≤ E * ‖k‖ :=
      ((Φw t).le_opNorm _).trans (mul_le_mul (hΦwnorm t ht) hιk (norm_nonneg _) hE0)
    have hpn_l : ‖Φv t (expJetIota l)‖ ≤ E * ‖l‖ :=
      ((Φv t).le_opNorm _).trans (mul_le_mul (hΦvnorm t ht) hιl (norm_nonneg _) hE0)
    have hpn'_l : ‖Φw t (expJetIota l)‖ ≤ E * ‖l‖ :=
      ((Φw t).le_opNorm _).trans (mul_le_mul (hΦwnorm t ht) hιl (norm_nonneg _) hE0)
    have hpn_m : ‖Φv t (expJetIota m)‖ ≤ E * ‖m‖ :=
      ((Φv t).le_opNorm _).trans (mul_le_mul (hΦvnorm t ht) hιm (norm_nonneg _) hE0)
    have hpn'_m : ‖Φw t (expJetIota m)‖ ≤ E * ‖m‖ :=
      ((Φw t).le_opNorm _).trans (mul_le_mul (hΦwnorm t ht) hιm (norm_nonneg _) hE0)
    have hpn_r : ‖Φv t (expJetIota r)‖ ≤ E * ‖r‖ :=
      ((Φv t).le_opNorm _).trans (mul_le_mul (hΦvnorm t ht) hιr (norm_nonneg _) hE0)
    have hpn'_r : ‖Φw t (expJetIota r)‖ ≤ E * ‖r‖ :=
      ((Φw t).le_opNorm _).trans (mul_le_mul (hΦwnorm t ht) hιr (norm_nonneg _) hE0)
    have hpd_h : ‖Φv t (expJetIota h) - Φw t (expJetIota h)‖ ≤ CPD * ‖v - w‖ * ‖h‖ := by
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota h)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) h‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (CPD * ‖v - w‖) * ‖h‖ := mul_le_mul (hΦdiff t ht) hιh (norm_nonneg _) (by positivity)
        _ = CPD * ‖v - w‖ * ‖h‖ := by ring
    have hpd_k : ‖Φv t (expJetIota k) - Φw t (expJetIota k)‖ ≤ CPD * ‖v - w‖ * ‖k‖ := by
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota k)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) k‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (CPD * ‖v - w‖) * ‖k‖ := mul_le_mul (hΦdiff t ht) hιk (norm_nonneg _) (by positivity)
        _ = CPD * ‖v - w‖ * ‖k‖ := by ring
    have hpd_l : ‖Φv t (expJetIota l) - Φw t (expJetIota l)‖ ≤ CPD * ‖v - w‖ * ‖l‖ := by
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota l)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) l‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (CPD * ‖v - w‖) * ‖l‖ := mul_le_mul (hΦdiff t ht) hιl (norm_nonneg _) (by positivity)
        _ = CPD * ‖v - w‖ * ‖l‖ := by ring
    have hpd_m : ‖Φv t (expJetIota m) - Φw t (expJetIota m)‖ ≤ CPD * ‖v - w‖ * ‖m‖ := by
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota m)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) m‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (CPD * ‖v - w‖) * ‖m‖ := mul_le_mul (hΦdiff t ht) hιm (norm_nonneg _) (by positivity)
        _ = CPD * ‖v - w‖ * ‖m‖ := by ring
    have hpd_r : ‖Φv t (expJetIota r) - Φw t (expJetIota r)‖ ≤ CPD * ‖v - w‖ * ‖r‖ := by
      rw [← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota r)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) r‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (CPD * ‖v - w‖) * ‖r‖ := mul_le_mul (hΦdiff t ht) hιr (norm_nonneg _) (by positivity)
        _ = CPD * ‖v - w‖ * ‖r‖ := by ring
    have hG0 : ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)‖ ≤ ((Ldf : ℝ) * (‖v - w‖ * eKf)) * (B5 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖) :=
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)).le_opNorm (Rw t)).trans
        (mul_le_mul (hDFdiff t ht) (hRwval t ht) (norm_nonneg _) (by positivity))
    rw [hρ5def]
    simp only [add_sub_add_comm]
    refine (norm_add_le _ _).trans (add_le_add hG0 ?_)
    exact expJet5TeleA2 (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhklmv t) (Qhklmw t) (Qhklrv t) (Qhklrw t) (Qhkmrv t) (Qhkmrw t) (Qhlmrv t) (Qhlmrw t) (Qklmrv t) (Qklmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD2diff t ht) (hK2v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval4_hklmv t ht) (hval4_hklmw t ht) (hval4_hklrv t ht) (hval4_hklrw t ht) (hval4_hkmrv t ht) (hval4_hkmrw t ht) (hval4_hlmrv t ht) (hval4_hlmrw t ht) (hval4_klmrv t ht) (hval4_klmrw t ht) (htp4_hklm t ht) (htp4_hklr t ht) (htp4_hkmr t ht) (htp4_hlmr t ht) (htp4_klmr t ht) (expJet5TeleA1 (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhkv t) (Qhkw t) (Qhlv t) (Qhlw t) (Qhmv t) (Qhmw t) (Qhrv t) (Qhrw t) (Qklv t) (Qklw t) (Qhmrv t) (Qhmrw t) (Qklmv t) (Qklmw t) (Qklrv t) (Qklrw t) (Qkmrv t) (Qkmrw t) (Qlmrv t) (Qlmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD2diff t ht) (hK2v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hkv t ht) (hval_hkw t ht) (hval_hlv t ht) (hval_hlw t ht) (hval_hmv t ht) (hval_hmw t ht) (hval_hrv t ht) (hval_hrw t ht) (hval_klv t ht) (hval_klw t ht) (hval3_hmrv t ht) (hval3_hmrw t ht) (hval3_klmv t ht) (hval3_klmw t ht) (hval3_klrv t ht) (hval3_klrw t ht) (hval3_kmrv t ht) (hval3_kmrw t ht) (hval3_lmrv t ht) (hval3_lmrw t ht) (htp_hk t ht) (htp_hl t ht) (htp_hm t ht) (htp_hr t ht) (htp_kl t ht) (htp3_hmr t ht) (htp3_klm t ht) (htp3_klr t ht) (htp3_kmr t ht) (htp3_lmr t ht) (expJet5TeleA0 (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qkmv t) (Qkmw t) (Qkrv t) (Qkrw t) (Qlmv t) (Qlmw t) (Qlrv t) (Qlrw t) (Qmrv t) (Qmrw t) (Qhklv t) (Qhklw t) (Qhkmv t) (Qhkmw t) (Qhkrv t) (Qhkrw t) (Qhlmv t) (Qhlmw t) (Qhlrv t) (Qhlrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD2diff t ht) (hK2v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_kmv t ht) (hval_kmw t ht) (hval_krv t ht) (hval_krw t ht) (hval_lmv t ht) (hval_lmw t ht) (hval_lrv t ht) (hval_lrw t ht) (hval_mrv t ht) (hval_mrw t ht) (hval3_hklv t ht) (hval3_hklw t ht) (hval3_hkmv t ht) (hval3_hkmw t ht) (hval3_hkrv t ht) (hval3_hkrw t ht) (hval3_hlmv t ht) (hval3_hlmw t ht) (hval3_hlrv t ht) (hval3_hlrw t ht) (htp_km t ht) (htp_kr t ht) (htp_lm t ht) (htp_lr t ht) (htp_mr t ht) (htp3_hkl t ht) (htp3_hkm t ht) (htp3_hkr t ht) (htp3_hlm t ht) (htp3_hlr t ht) (expJet5TeleB4 (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhmrv t) (Qhmrw t) (Qklmv t) (Qklmw t) (Qklrv t) (Qklrw t) (Qkmrv t) (Qkmrw t) (Qlmrv t) (Qlmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD3diff t ht) (hK3v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval3_hmrv t ht) (hval3_hmrw t ht) (hval3_klmv t ht) (hval3_klmw t ht) (hval3_klrv t ht) (hval3_klrw t ht) (hval3_kmrv t ht) (hval3_kmrw t ht) (hval3_lmrv t ht) (hval3_lmrw t ht) (htp3_hmr t ht) (htp3_klm t ht) (htp3_klr t ht) (htp3_kmr t ht) (htp3_lmr t ht) (expJet5TeleB3 (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhklv t) (Qhklw t) (Qhkmv t) (Qhkmw t) (Qhkrv t) (Qhkrw t) (Qhlmv t) (Qhlmw t) (Qhlrv t) (Qhlrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD3diff t ht) (hK3v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval3_hklv t ht) (hval3_hklw t ht) (hval3_hkmv t ht) (hval3_hkmw t ht) (hval3_hkrv t ht) (hval3_hkrw t ht) (hval3_hlmv t ht) (hval3_hlmw t ht) (hval3_hlrv t ht) (hval3_hlrw t ht) (htp3_hkl t ht) (htp3_hkm t ht) (htp3_hkr t ht) (htp3_hlm t ht) (htp3_hlr t ht) (expJet5TeleB2 (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhkv t) (Qhkw t) (Qhlv t) (Qhlw t) (Qhmv t) (Qhmw t) (Qhrv t) (Qhrw t) (Qklv t) (Qklw t) (Qkmv t) (Qkmw t) (Qkrv t) (Qkrw t) (Qlmv t) (Qlmw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD3diff t ht) (hK3v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hkv t ht) (hval_hkw t ht) (hval_hlv t ht) (hval_hlw t ht) (hval_hmv t ht) (hval_hmw t ht) (hval_hrv t ht) (hval_hrw t ht) (hval_klv t ht) (hval_klw t ht) (hval_kmv t ht) (hval_kmw t ht) (hval_krv t ht) (hval_krw t ht) (hval_lmv t ht) (hval_lmw t ht) (htp_hk t ht) (htp_hl t ht) (htp_hm t ht) (htp_hr t ht) (htp_kl t ht) (htp_km t ht) (htp_kr t ht) (htp_lm t ht) (expJet5TeleB1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhkv t) (Qhkw t) (Qhmv t) (Qhmw t) (Qhrv t) (Qhrw t) (Qkmv t) (Qkmw t) (Qkrv t) (Qkrw t) (Qlmv t) (Qlmw t) (Qlrv t) (Qlrw t) (Qmrv t) (Qmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD3diff t ht) (hK3v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hkv t ht) (hval_hkw t ht) (hval_hmv t ht) (hval_hmw t ht) (hval_hrv t ht) (hval_hrw t ht) (hval_kmv t ht) (hval_kmw t ht) (hval_krv t ht) (hval_krw t ht) (hval_lmv t ht) (hval_lmw t ht) (hval_lrv t ht) (hval_lrw t ht) (hval_mrv t ht) (hval_mrw t ht) (htp_hk t ht) (htp_hm t ht) (htp_hr t ht) (htp_km t ht) (htp_kr t ht) (htp_lm t ht) (htp_lr t ht) (htp_mr t ht) (expJet5TeleB0 (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhlv t) (Qhlw t) (Qhmv t) (Qhmw t) (Qklv t) (Qklw t) (Qkmv t) (Qkmw t) (Qkrv t) (Qkrw t) (Qlmv t) (Qlmw t) (Qlrv t) (Qlrw t) (Qmrv t) (Qmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD3diff t ht) (hK3v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hlv t ht) (hval_hlw t ht) (hval_hmv t ht) (hval_hmw t ht) (hval_klv t ht) (hval_klw t ht) (hval_kmv t ht) (hval_kmw t ht) (hval_krv t ht) (hval_krw t ht) (hval_lmv t ht) (hval_lmw t ht) (hval_lrv t ht) (hval_lrw t ht) (hval_mrv t ht) (hval_mrw t ht) (htp_hl t ht) (htp_hm t ht) (htp_kl t ht) (htp_km t ht) (htp_kr t ht) (htp_lm t ht) (htp_lr t ht) (htp_mr t ht) (expJet5TeleC2 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qlmv t) (Qlmw t) (Qlrv t) (Qlrw t) (Qmrv t) (Qmrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD4diff t ht) (hK4v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_lmv t ht) (hval_lmw t ht) (hval_lrv t ht) (hval_lrw t ht) (hval_mrv t ht) (hval_mrw t ht) (htp_lm t ht) (htp_lr t ht) (htp_mr t ht) (expJet5TeleC1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhrv t) (Qhrw t) (Qklv t) (Qklw t) (Qkmv t) (Qkmw t) (Qkrv t) (Qkrw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD4diff t ht) (hK4v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hrv t ht) (hval_hrw t ht) (hval_klv t ht) (hval_klw t ht) (hval_kmv t ht) (hval_kmw t ht) (hval_krv t ht) (hval_krw t ht) (htp_hr t ht) (htp_kl t ht) (htp_km t ht) (htp_kr t ht) (expJet5TeleC0 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p w t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p w t)) (Φv t (expJetIota h)) (Φw t (expJetIota h)) (Φv t (expJetIota k)) (Φw t (expJetIota k)) (Φv t (expJetIota l)) (Φw t (expJetIota l)) (Φv t (expJetIota m)) (Φw t (expJetIota m)) (Φv t (expJetIota r)) (Φw t (expJetIota r)) (Qhkv t) (Qhkw t) (Qhlv t) (Qhlw t) (Qhmv t) (Qhmw t) E eKf CPD B2 B3 B4 B5 T2 T3 T4 Kstar2 Kstar3 Kstar4 Kstar5 (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ) ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖ hE0 heKf0 hCPD0 hB20 hB30 hB40 hB50 hT20 hT30 hT40 hKstar20 hKstar30 hKstar40 hKstar50 Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hD4diff t ht) (hD5diff t ht) (hK4v t ht) (hK5v t ht) hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r (hval_hkv t ht) (hval_hkw t ht) (hval_hlv t ht) (hval_hlw t ht) (hval_hmv t ht) (hval_hmw t ht) (htp_hk t ht) (htp_hl t ht) (htp_hm t ht)))))))))))
  have hρ50 : 0 ≤ ρ5 :=
    (norm_nonneg _).trans (hrbound 0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩))
  have hfin := expJet5Val_v_two_pt_diff_gronwall g gi hC p v w Kstar hKstar0
    Φv Φw Qhkv Qhlv Qhmv Qhrv Qklv Qkmv Qkrv Qlmv Qlrv Qmrv Qhklv Qhkmv Qhkrv Qhlmv Qhlrv Qhmrv Qklmv Qklrv Qkmrv Qlmrv Qhklmv Qhklrv Qhkmrv Qhlmrv Qklmrv
    Qhkw Qhlw Qhmw Qhrw Qklw Qkmw Qkrw Qlmw Qlrw Qmrw Qhklw Qhkmw Qhkrw Qhlmw Qhlrw Qhmrw Qklmw Qklrw Qkmrw Qlmrw Qhklmw Qhklrw Qhkmrw Qhlmrw Qklmrw Rv Rw h k l m r
    hRv0 hRw0 hRvd hRwd hKstarv ρ5 hρ50 hrbound
  refine hfin.trans (le_of_eq ?_)
  rw [hρ5def]
  exact expJet5RhoConst_eq E eKf CPD B2 B3 B4 B5 T2 T3 T4
    (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
    Kstar Kstar2 Kstar3 Kstar4 Kstar5 ‖v - w‖ ‖h‖ ‖k‖ ‖l‖ ‖m‖ ‖r‖
    hEdef heKfdef hCPDdef hB2def hB3def hB4def hB5def hT2def hT3def hT4def

end QIQTH.ExpMap
