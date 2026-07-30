/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4FundBounds
import QIQTH.ExpJet4FundGlobal
import QIQTH.ExpJet4Fund
import QIQTH.ExpJet4Rhs
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# The Jet₄ two-point analytic heart — reusable ingredients (J4-3, partial)

This file lands the **reachable, composable structure of the J4-3 brick** of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`) toward the truly-unconditional `a₁ = R/6`: the pieces of the
two-point Lipschitz "analytic heart" `expJet4Val_v_two_pt_diff` — a FAITHFUL MIRROR one Fréchet order
up of `expJet3Val_v_two_pt_diff` (`ExpMapContDiff3.lean`) — that are self-contained and reusable.

The full jet-4 value two-point difference reduces, via a residual ODE + Grönwall, to a `ρ₄`-telescope
of **fifty-one** differenced sub-terms (vs the fourteen of jet-3): the `[DF(Y_v)−DF(Y_w)]R_w` term,
the five-way peel of the `D⁴F` `(1+1+1+1)` block, the four-way peel of each of the six `D³F`
`(2+1+1)` blocks, the three-way peel of each of the three `D²F` `(2+2)` blocks and each of the four
`D²F` `(3+1)` blocks.  The `(3+1)` blocks are the only genuinely-new consumers: their differenced
third-variation factor `Q^{···}_v − Q^{···}_w` requires a `[0,1]`-uniform third-variation two-point
bound that did NOT exist (only the `t = 1` value `expJet3Val_v_two_pt_diff` was built).

## What is proven here (all axiom-clean, std-3)

* `expJet3Val_v_two_pt_Icc_const` — the **`[0,1]`-uniform third-variation two-point** bound
  `∀ t ∈ [0,1], ‖R^{hkl}_v(t) − R^{hkl}_w(t)‖ ≤ expJet3VtpConst·‖v−w‖·‖h‖‖k‖‖l‖`.  The verbatim mirror
  of `expJet3Val_v_two_pt_diff` with the `t = 1` vector Grönwall (`gronwall_vec_residual`) replaced by
  the uniform `gronwall_vec_residual_Icc`.  THE new reusable ingredient the jet-4 `(3+1)` telescope
  consumes.
* `expJet4_v_residual_hasDerivWithinAt` — the Jet₄ `R_v − R_w` parameter-residual ODE identity
  `D'(t) = DF(Y_v t)(D t) + ([DF(Y_v t)−DF(Y_w t)](R_w t) + (Θ₄^v(t) − Θ₄^w(t)))`; the exact mirror of
  `expJet3_v_residual_hasDerivWithinAt`, one Fréchet order up.
* `expJet4Val_v_two_pt_diff_gronwall` — the residual-Grönwall application: carrying the (genuine,
  non-vacuous) `ρ₄`-residual bound `hrbound` as an explicit hypothesis, the two-point value obeys
  `‖R^{hklm}_v(1) − R^{hklm}_w(1)‖ ≤ ρ₄·e^{Kstar}`.  This is `expJet4Val_v_two_pt_diff` MINUS the
  fifty-one-term algebraic `ρ₄`-telescope; once the telescope discharges `hrbound` with the concrete
  `ρ₄`, the full theorem follows by a `ring`-normalization of the constant.

## Honest firewall (binding)

**What is NOT closed here:** the fifty-one-term `ρ₄`-telescope itself (the concrete discharge of
`hrbound` with the assembled `expJet4VtpConst`), hence the full `expJet4Val_v_two_pt_diff` and its
lifted `expJetD4_two_pt_diff`, are NOT proven — `hrbound` is carried as a genuine explicit hypothesis.
This does NOT discharge `hfd3` / `ContDiff¹ (fderiv³ exp_p)`, does NOT establish `exp_p ∈ C⁴`, does
NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`, and is NOT numerical-`G` / the
conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### Generic multilinear CLM-application norm bounds (local private copies)

The `ExpMapContDiff3` helpers are `private`; we re-declare local copies (kept generic, no tube atoms,
so the nested-CLM `whnf` never fires) exactly as `ExpJet4Rhs.lean` does. -/

/-- **Generic CLM-application norm bound.**  `‖C a‖ ≤ KC · Ka`. -/
private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

/-- **Generic bilinear CLM-application norm bound.**  `‖B a b‖ ≤ KB · Ka · Kb`. -/
private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

/-- **Generic trilinear CLM-application norm bound.**  `‖B a b c‖ ≤ KB · Ka · Kb · Kc`. -/
private theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
  clmApply2_norm_le (B a) b c (mul_nonneg hKB hKa) hKb (clmApply_norm_le B a hKB hB ha) hb hc

/-! ### The `[0,1]`-uniform third-variation two-point bound -/

set_option maxHeartbeats 3200000 in
/-- **The `[0,1]`-uniform third-variation two-point Lipschitz bound.**  The `∀ t ∈ [0,1]` mirror of
    `expJet3Val_v_two_pt_diff` (its `t = 1` endpoint): identical `ρ₃`-telescope, with the `t = 1`
    vector Grönwall (`gronwall_vec_residual`) replaced by the uniform `gronwall_vec_residual_Icc`, so
    `‖R^{hkl}_v(t) − R^{hkl}_w(t)‖ ≤ expJet3VtpConst·‖v−w‖·‖h‖‖k‖‖l‖` for every `t ∈ [0,1]`.  The
    reusable ingredient the jet-4 `(3+1)` `ρ₄`-telescope consumes (its differenced third-variation
    factor `Q^{···}_v − Q^{···}_w`). -/
theorem expJet3Val_v_two_pt_Icc_const (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f Ld3f : NNReal) (Kstar Kstar2 Kstar3 : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD3F : LipschitzOnWith Ld3f (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar2f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar2)
    (hKstar3f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p u t)‖ ≤ Kstar3)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (Qklv Qhlv Qhkv Qklw Qhlw Qhkw Rv Rw : ℝ → (Point n × Point n)) (h k l : Point n)
    (hQklv0 : Qklv 0 = 0) (hQhlv0 : Qhlv 0 = 0) (hQhkv0 : Qhkv 0 = 0)
    (hQklw0 : Qklw 0 = 0) (hQhlw0 : Qhlw 0 = 0) (hQhkw0 : Qhkw 0 = 0)
    (hRv0 : Rv 0 = 0) (hRw0 : Rw 0 = 0)
    (hQklvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklv t)
        + expJet2Rhs g gi hC p v Φv k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlv t)
        + expJet2Rhs g gi hC p v Φv h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkv t)
        + expJet2Rhs g gi hC p v Φv h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQklwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklw t)
        + expJet2Rhs g gi hC p w Φw k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlw t)
        + expJet2Rhs g gi hC p w Φw h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkw t)
        + expJet2Rhs g gi hC p w Φw h k t) (Set.Icc (0 : ℝ) 1) t)
    (hRvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t)
        + expJet3Rhs g gi hC p v Φv Qklv Qhlv Qhkv h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hRwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
        + expJet3Rhs g gi hC p w Φw Qklw Qhlw Qhkw h k l t) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Rv t - Rw t‖
      ≤ expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3
          * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ := by
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
  have hK3w := hKstar3f w hw
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans
      (by simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
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
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD2diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)‖
        ≤ (Ld2f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD2F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD3diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)‖
        ≤ (Ld3f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD3F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hΦdiff := expFund_two_pt_diff_Icc g gi hC p v w Kf Ldf Kstar hKstar0 hLipF hLipDF
    hKstarv hKstarw hv hw Φv Φw hΦv0 hΦw0 hΦvd hΦwd
  have hQklvval := expJet2Fund_value_bound_Icc g gi hC p v Φv k l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qklv hQklv0 hQklvd
  have hQhlvval := expJet2Fund_value_bound_Icc g gi hC p v Φv h l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhlv hQhlv0 hQhlvd
  have hQhkvval := expJet2Fund_value_bound_Icc g gi hC p v Φv h k Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhkv hQhkv0 hQhkvd
  have hQklwval := expJet2Fund_value_bound_Icc g gi hC p w Φw k l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qklw hQklw0 hQklwd
  have hQhlwval := expJet2Fund_value_bound_Icc g gi hC p w Φw h l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhlw hQhlw0 hQhlwd
  have hQhkwval := expJet2Fund_value_bound_Icc g gi hC p w Φw h k Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhkw hQhkw0 hQhkwd
  have hQkldiff := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qklv Qklw k l hQklv0 hQklw0 hQklvd hQklwd
  have hQhldiff := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhlv Qhlw h l hQhlv0 hQhlw0 hQhlvd hQhlwd
  have hQhkdiff := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhkw h k hQhkv0 hQhkw0 hQhkvd hQhkwd
  have hRwvalRaw := expJet3Fund_value_bound_Icc g gi hC p w Φw Qklw Qhlw Qhkw h k l
    Kstar Kstar3 Kstar2 (Real.exp Kstar)
    ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
    ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
    ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
    hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
    hQklwval hQhlwval hQhkwval Rw hRw0 hRwd
  have hRwval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Rw t‖
      ≤ ((Kstar3 * Real.exp Kstar ^ 3
            + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ :=
    fun t ht => (hRwvalRaw t ht).trans (le_of_eq (by ring))
  set ρval : ℝ := (((Kstar3 * Real.exp Kstar ^ 3
            + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          * Real.exp Kstar) * ((Ldf : ℝ) * Real.exp (Kf : ℝ))
      + 3 * (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * Real.exp Kstar ^ 2)
      + (Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 3
      + 3 * (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
      + 3 * (Kstar2 * Real.exp Kstar * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
      + 3 * ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)))
    * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ with hρvaldef
  have hρval0 : 0 ≤ ρval := by
    have hCe : 0 ≤ expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 :=
      expJet2VtpConst_nonneg _ _ _ _ _ Ldf.2 Ld2f.2 hKstar20
    rw [hρvaldef]; positivity
  have hrbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
         + (expJet3Rhs g gi hC p v Φv Qklv Qhlv Qhkv h k l t
            - expJet3Rhs g gi hC p w Φw Qklw Qhlw Qhkw h k l t)‖ ≤ ρval := by
    intro t ht
    simp only [expJet3Rhs_apply]
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p w t with hywE
    set dv := fderiv ℝ (geodesicField g gi) yv with hdvE
    set dw := fderiv ℝ (geodesicField g gi) yw with hdwE
    set d2v := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yv with hd2vE
    set d2w := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yw with hd2wE
    set d3v := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yv with hd3vE
    set d3w := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yw with hd3wE
    set ph := Φv t (expJetIota h) with hphE
    set ph' := Φw t (expJetIota h) with hph'E
    set pk := Φv t (expJetIota k) with hpkE
    set pk' := Φw t (expJetIota k) with hpk'E
    set pl := Φv t (expJetIota l) with hplE
    set pl' := Φw t (expJetIota l) with hpl'E
    set qklv := Qklv t with hqklvE
    set qklw := Qklw t with hqklwE
    set qhlv := Qhlv t with hqhlvE
    set qhlw := Qhlw t with hqhlwE
    set qhkv := Qhkv t with hqhkvE
    set qhkw := Qhkw t with hqhkwE
    set rw := Rw t with hrwE
    have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
    have hd3n : ‖d3v‖ ≤ Kstar3 := hKstar3f v hv t ht
    have hphn : ‖ph‖ ≤ Real.exp Kstar * ‖h‖ :=
      clmApply_norm_le (Φv t) (expJetIota h) (Real.exp_pos _).le (hΦvnorm t ht) hιh
    have hpkn : ‖pk‖ ≤ Real.exp Kstar * ‖k‖ :=
      clmApply_norm_le (Φv t) (expJetIota k) (Real.exp_pos _).le (hΦvnorm t ht) hιk
    have hpln : ‖pl‖ ≤ Real.exp Kstar * ‖l‖ :=
      clmApply_norm_le (Φv t) (expJetIota l) (Real.exp_pos _).le (hΦvnorm t ht) hιl
    have hph'n : ‖ph'‖ ≤ Real.exp Kstar * ‖h‖ :=
      clmApply_norm_le (Φw t) (expJetIota h) (Real.exp_pos _).le (hΦwnorm t ht) hιh
    have hpk'n : ‖pk'‖ ≤ Real.exp Kstar * ‖k‖ :=
      clmApply_norm_le (Φw t) (expJetIota k) (Real.exp_pos _).le (hΦwnorm t ht) hιk
    have hpl'n : ‖pl'‖ ≤ Real.exp Kstar * ‖l‖ :=
      clmApply_norm_le (Φw t) (expJetIota l) (Real.exp_pos _).le (hΦwnorm t ht) hιl
    have hphd : ‖ph - ph'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖ := by
      rw [hphE, hph'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota h)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) h‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖h‖ :=
            mul_le_mul (hΦdiff t ht) hιh (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖ := by
            ring
    have hpkd : ‖pk - pk'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖ := by
      rw [hpkE, hpk'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota k)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) k‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖k‖ :=
            mul_le_mul (hΦdiff t ht) hιk (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖ := by
            ring
    have hpld : ‖pl - pl'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖l‖ := by
      rw [hplE, hpl'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota l)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) l‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖l‖ :=
            mul_le_mul (hΦdiff t ht) hιl (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖l‖ := by
            ring
    have heq :
        (dv - dw) rw
          + (d3v ph pk pl + d2v ph qklv + d2v pk qhlv + d2v pl qhkv
             - (d3w ph' pk' pl' + d2w ph' qklw + d2w pk' qhlw + d2w pl' qhkw))
        = (dv - dw) rw
          + d3v (ph - ph') pk pl + d3v ph' (pk - pk') pl + d3v ph' pk' (pl - pl')
          + (d3v - d3w) ph' pk' pl'
          + d2v (ph - ph') qklv + d2v ph' (qklv - qklw) + (d2v - d2w) ph' qklw
          + d2v (pk - pk') qhlv + d2v pk' (qhlv - qhlw) + (d2v - d2w) pk' qhlw
          + d2v (pl - pl') qhkv + d2v pl' (qhkv - qhkw) + (d2v - d2w) pl' qhkw := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [heq]
    have hbDF : ‖(dv - dw) rw‖
        ≤ ((Kstar3 * Real.exp Kstar ^ 3
              + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
            * Real.exp Kstar) * ((Ldf : ℝ) * Real.exp (Kf : ℝ))
          * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply_norm_le (dv - dw) rw (by positivity) (hDFdiff t ht) (hRwval t ht)).trans
        (le_of_eq (by ring))
    have hbA1 : ‖d3v (ph - ph') pk pl‖
        ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply3_norm_le d3v (ph - ph') pk pl hKstar30 (by positivity) (by positivity)
        hd3n hphd hpkn hpln).trans (le_of_eq (by ring))
    have hbA2 : ‖d3v ph' (pk - pk') pl‖
        ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply3_norm_le d3v ph' (pk - pk') pl hKstar30 (by positivity) (by positivity)
        hd3n hph'n hpkd hpln).trans (le_of_eq (by ring))
    have hbA3 : ‖d3v ph' pk' (pl - pl')‖
        ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply3_norm_le d3v ph' pk' (pl - pl') hKstar30 (by positivity) (by positivity)
        hd3n hph'n hpk'n hpld).trans (le_of_eq (by ring))
    have hbA4 : ‖(d3v - d3w) ph' pk' pl'‖
        ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply3_norm_le (d3v - d3w) ph' pk' pl' (by positivity) (by positivity) (by positivity)
        (hD3diff t ht) hph'n hpk'n hpl'n).trans (le_of_eq (by ring))
    have hbB1 : ‖d2v (ph - ph') qklv‖
        ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v (ph - ph') qklv hKstar20 (by positivity) hd2n hphd
        (hQklvval t ht)).trans (le_of_eq (by ring))
    have hbB2 : ‖d2v ph' (qklv - qklw)‖
        ≤ (Kstar2 * Real.exp Kstar
            * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
          * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v ph' (qklv - qklw) hKstar20 (by positivity) hd2n hph'n
        (hQkldiff t ht)).trans (le_of_eq (by ring))
    have hbB3 : ‖(d2v - d2w) ph' qklw‖
        ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le (d2v - d2w) ph' qklw (by positivity) (by positivity) (hD2diff t ht)
        hph'n (hQklwval t ht)).trans (le_of_eq (by ring))
    have hbC1 : ‖d2v (pk - pk') qhlv‖
        ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v (pk - pk') qhlv hKstar20 (by positivity) hd2n hpkd
        (hQhlvval t ht)).trans (le_of_eq (by ring))
    have hbC2 : ‖d2v pk' (qhlv - qhlw)‖
        ≤ (Kstar2 * Real.exp Kstar
            * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
          * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v pk' (qhlv - qhlw) hKstar20 (by positivity) hd2n hpk'n
        (hQhldiff t ht)).trans (le_of_eq (by ring))
    have hbC3 : ‖(d2v - d2w) pk' qhlw‖
        ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le (d2v - d2w) pk' qhlw (by positivity) (by positivity) (hD2diff t ht)
        hpk'n (hQhlwval t ht)).trans (le_of_eq (by ring))
    have hbD1 : ‖d2v (pl - pl') qhkv‖
        ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v (pl - pl') qhkv hKstar20 (by positivity) hd2n hpld
        (hQhkvval t ht)).trans (le_of_eq (by ring))
    have hbD2 : ‖d2v pl' (qhkv - qhkw)‖
        ≤ (Kstar2 * Real.exp Kstar
            * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
          * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le d2v pl' (qhkv - qhkw) hKstar20 (by positivity) hd2n hpl'n
        (hQhkdiff t ht)).trans (le_of_eq (by ring))
    have hbD3 : ‖(d2v - d2w) pl' qhkw‖
        ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ :=
      (clmApply2_norm_le (d2v - d2w) pl' qhkw (by positivity) (by positivity) (hD2diff t ht)
        hpl'n (hQhkwval t ht)).trans (le_of_eq (by ring))
    rw [show ρval
        = ((Kstar3 * Real.exp Kstar ^ 3
              + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
            * Real.exp Kstar) * ((Ldf : ℝ) * Real.exp (Kf : ℝ))
            * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * Real.exp Kstar ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * Real.exp Kstar
              * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
            * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * Real.exp Kstar
              * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
            * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar)
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + (Kstar2 * Real.exp Kstar
              * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2)
            * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
          + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar
              * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖
        from by rw [hρvaldef]; ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hbD3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbD2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbD1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbC3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbC2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbC1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbB3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbB2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbB1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbA4)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbA3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hbA2)
    exact (norm_add_le _ _).trans (add_le_add hbDF hbA1)
  have hgron := gronwall_vec_residual_Icc (fun s => Rv s - Rw s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
      + (expJet3Rhs g gi hC p v Φv Qklv Qhlv Qhkv h k l t
         - expJet3Rhs g gi hC p w Φw Qklw Qhlw Qhkw h k l t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar ρval hKstar0 hρval0
    (by simp only [hRv0, hRw0, sub_zero])
    (fun t ht => expJet3_v_residual_hasDerivWithinAt g gi hC p v w Φv Φw
      Qklv Qhlv Qhkv Qklw Qhlw Qhkw Rv Rw h k l hRvd hRwd t ht)
    (fun t ht => hKstarv t ht)
    (fun t ht => hrbound t ht)
  intro t ht
  refine (hgron t ht).trans (le_of_eq ?_)
  rw [hρvaldef]
  unfold expJet3VtpConst
  ring

/-! ### The Jet₄ residual ODE identity -/

set_option maxHeartbeats 1000000 in
/-- **The Jet₄ `R_v − R_w` parameter-residual ODE (residual identity).**  With `Rv`,`Rw` the Jet₄
    fourth-variation witnesses for base parameters `v`,`w` (each with its own first-variation
    propagator `Φ·`, second variations `Q^{··}·`, third variations `Q^{···}·`, and derivative law
    `R'_· = DF(Y_· t)(R_·) + Θ₄^{hklm}_·(t)`), the parameter residual `D(t) = Rv(t) − Rw(t)` obeys, on
    `[0,1]`,
    `D'(t) = DF(Y_v t)(D t) + ([DF(Y_v t) − DF(Y_w t)](Rw t) + (Θ₄^{hklm}_v(t) − Θ₄^{hklm}_w(t)))`.
    The exact mirror of `expJet3_v_residual_hasDerivWithinAt`, one Fréchet order up. -/
theorem expJet4_v_residual_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv : ℝ → (Point n × Point n))
    (Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw : ℝ → (Point n × Point n))
    (Rv Rw : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hRvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t)
        + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
            h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
        + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
            h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => Rv s - Rw s)
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t - Rw t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
           + (expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
                h k l m t
              - expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
                  h k l m t)))
      (Set.Icc (0 : ℝ) 1) t := by
  have hcomb := (hRvd t ht).sub (hRwd t ht)
  have heq :
      (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t - Rw t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
           + (expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
                h k l m t
              - expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
                  h k l m t))
      = ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t)
          + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
              h k l m t)
        - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
          + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
              h k l m t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact hcomb

/-! ### The residual-Grönwall application (carried `ρ₄`-bound) -/

set_option maxHeartbeats 1000000 in
/-- **The jet-4 value two-point difference — residual-Grönwall application.**  Given the Jet₄
    fourth-variation witnesses `Rv`, `Rw` (each solving its `R'_· = DF(Y_·)(R_·) + Θ₄^{hklm}_·` ODE
    with `R_·(0) = 0`), the `[0,1]`-bound `Kstar` on `‖DF(Y_v t)‖`, and — carried as an explicit,
    genuine hypothesis — the `ρ₄`-residual bound
    `‖[DF(Y_v)−DF(Y_w)](R_w) + (Θ₄_v − Θ₄_w)‖ ≤ ρ₄` on `[0,1]`, the parameter residual `Rv − Rw`
    (which solves `D' = DF(Y_v)(D) + ρ₄`, `expJet4_v_residual_hasDerivWithinAt`) satisfies, via the
    vector Grönwall (`gronwall_vec_residual`),
    `‖Rv 1 − Rw 1‖ ≤ ρ₄·e^{Kstar}`.  This is `expJet4Val_v_two_pt_diff` MINUS the fifty-one-term
    algebraic `ρ₄`-telescope that discharges `hrbound` with the concrete `ρ₄`. -/
theorem expJet4Val_v_two_pt_diff_gronwall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (Kstar : ℝ) (hKstar0 : 0 ≤ Kstar)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv : ℝ → (Point n × Point n))
    (Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw : ℝ → (Point n × Point n))
    (Rv Rw : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hRv0 : Rv 0 = 0) (hRw0 : Rw 0 = 0)
    (hRvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t)
        + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
            h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
        + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
            h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (ρ4 : ℝ) (hρ40 : 0 ≤ ρ4)
    (hrbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
         + (expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
              h k l m t
            - expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
                h k l m t)‖ ≤ ρ4) :
    ‖Rv 1 - Rw 1‖ ≤ ρ4 * Real.exp Kstar :=
  gronwall_vec_residual (fun s => Rv s - Rw s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
      + (expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv h k l m t
         - expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
             h k l m t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
    Kstar ρ4 hKstar0 hρ40
    (by simp only [hRv0, hRw0, sub_zero])
    (fun t ht => expJet4_v_residual_hasDerivWithinAt g gi hC p v w Φv Φw
      Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
      Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw Rv Rw h k l m hRvd hRwd t ht)
    (fun t ht => hKstarv t ht)
    (fun t ht => hrbound t ht)

end QIQTH.ExpMap
