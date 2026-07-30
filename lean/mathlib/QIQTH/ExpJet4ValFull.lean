/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Val
import QIQTH.ExpJet4FundBounds
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# The Jet₄ two-point analytic heart — full 51-term ρ₄-telescope (J4-3-remainder)

This file closes the analytic heart `expJet4Val_v_two_pt_diff` of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`) toward the truly-unconditional `a₁ = R/6`: the two-point
Lipschitz bound `‖R⁴_v(1) − R⁴_w(1)‖ ≤ expJet4VtpConst·‖v−w‖·‖h‖‖k‖‖l‖‖m‖`, a FAITHFUL MIRROR one
Fréchet order up of `expJet3Val_v_two_pt_diff` (`ExpMapContDiff3.lean`).

The `ρ₄`-residual `[DF(Y_v)−DF(Y_w)]R_w + (Θ₄^v − Θ₄^w)` telescopes into **fifty-one** differenced
sub-terms — the `[DF]R_w` term, the five-way peel of the `D⁴F` `(1+1+1+1)` block, the four-way peel of
each of the six `D³F` `(2+1+1)` blocks, the three-way peel of each of the three `D²F` `(2+2)` blocks and
each of the four `D²F` `(3+1)` blocks — each bounded (via `clmApply{2,3,4}_norm_le`, the
`DF`/`D²F`/`D³F`/`D⁴F` Lipschitz differences along the tube, the `Φ` two-point and value bounds, the
second/third-variation two-point bounds `expJet2_v_two_pt_Icc_const` / `expJet3Val_v_two_pt_Icc_const`
and value bounds) by a concrete constant times `‖v−w‖‖h‖‖k‖‖l‖‖m‖`; the aggregate feeds
`expJet4Val_v_two_pt_diff_gronwall`.

The 4th-derivative Lipschitz `hLipD4F` and tube bound `hKstar4f` are carried as genuine hypotheses
(satisfied by the smooth geodesic field), exactly as the jet-3 crux carried its `Ld3f`/`Kstar3`.

## Honest firewall (binding)

This does NOT discharge `hfd3` / `ContDiff¹ (fderiv³ exp_p)`, does NOT establish `exp_p ∈ C⁴`, does
NOT reach `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`, and is NOT numerical-`G` / the
conjecture / QG.  It is one green algebraic rung (J4-3-remainder) of the jet-4 tower.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### Generic multilinear CLM-application norm bounds (local private copies) -/

private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

private theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
  clmApply2_norm_le (B a) b c (mul_nonneg hKB hKa) hKb (clmApply_norm_le B a hKB hB ha) hb hc

private theorem clmApply4_norm_le {E F G H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I) (a : E) (b : F) (c : G) (d : H)
    {KB Ka Kb Kc Kd : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) (hd : ‖d‖ ≤ Kd) :
    ‖B a b c d‖ ≤ KB * Ka * Kb * Kc * Kd :=
  clmApply3_norm_le (B a) b c d (mul_nonneg hKB hKa) hKb hKc
    (clmApply_norm_le B a hKB hB ha) hb hc hd

/-! ### Generic multilinear-difference telescoping identities

Proven at abstract type variables so the `map_sub` / `sub_apply` linearisation never `whnf`s a
concrete nested `Point n × Point n →L …` codomain. -/

private theorem clm2_diff_eq {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B B' : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) (a' : E) (b' : F) :
    B a b - B' a' b' = B (a - a') b + B a' (b - b') + (B - B') a' b' := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]; abel

private theorem clm3_diff_eq {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) (a' : E) (b' : F) (c' : G) :
    B a b c - B' a' b' c'
      = B (a - a') b c + B a' (b - b') c + B a' b' (c - c') + (B - B') a' b' c' := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]; abel

private theorem clm4_diff_eq {E F G H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I) (a : E) (b : F) (c : G) (d : H)
    (a' : E) (b' : F) (c' : G) (d' : H) :
    B a b c d - B' a' b' c' d'
      = B (a - a') b c d + B a' (b - b') c d + B a' b' (c - c') d + B a' b' c' (d - d')
        + (B - B') a' b' c' d' := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]; abel

/-- **Fourteen-term regroup** (abstract atoms): `c + ((∑aᵢ) − (∑bᵢ)) = c + ∑(aᵢ − bᵢ)`, fully
    left-associated, proven once on abstract group atoms so the concrete `abel` (28 nested-CLM atoms)
    never runs. -/
private theorem regroup14 {G : Type*} [AddCommGroup G]
    (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
       b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : G) :
    c + ((a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14)
          - (b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14))
      = c + (a1 - b1) + (a2 - b2) + (a3 - b3) + (a4 - b4) + (a5 - b5) + (a6 - b6) + (a7 - b7)
          + (a8 - b8) + (a9 - b9) + (a10 - b10) + (a11 - b11) + (a12 - b12) + (a13 - b13)
          + (a14 - b14) := by
  abel

/-! ### The aggregate `ρ₄`-telescope constant -/

/-- **The assembled Jet₄ two-point Lipschitz constant** for `v ↦ R⁴_v(1)` (the fourth derivative):
    the aggregate of the fifty-one `ρ₄`-telescope sub-term coefficients, times the outer Grönwall
    factor `e^{Kstar}`. -/
noncomputable def expJet4VtpConst (Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4 : ℝ) : ℝ :=
  (Ldf * Real.exp Kf * ((Kstar4 * Real.exp Kstar ^ 4
        + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)
        + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2
        + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3
            + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          * Real.exp Kstar)) * Real.exp Kstar)
    + 4 * (Kstar4 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3)
    + Ld4f * Real.exp Kf * Real.exp Kstar ^ 4
    + 12 * (Kstar3 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 6 * (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2)
    + 6 * (Ld3f * Real.exp Kf * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 6 * (Kstar2 * expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 3 * (Ld2f * Real.exp Kf * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2)
    + 4 * (Kstar2 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar)
        * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar
            * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar))
    + 4 * (Kstar2 * Real.exp Kstar * expJet3VtpConst Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3)
    + 4 * (Ld2f * Real.exp Kf * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3
        + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
      * Real.exp Kstar))) * Real.exp Kstar

theorem expJet4VtpConst_nonneg (Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4 : ℝ)
    (hLdf : 0 ≤ Ldf) (hLd2f : 0 ≤ Ld2f) (hLd3f : 0 ≤ Ld3f) (hLd4f : 0 ≤ Ld4f)
    (hKstar2 : 0 ≤ Kstar2) (hKstar3 : 0 ≤ Kstar3) (hKstar4 : 0 ≤ Kstar4) :
    0 ≤ expJet4VtpConst Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4 := by
  have hCe2 : 0 ≤ expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2 :=
    expJet2VtpConst_nonneg _ _ _ _ _ hLdf hLd2f hKstar2
  have hCe3 : 0 ≤ expJet3VtpConst Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3 :=
    expJet3VtpConst_nonneg _ _ _ _ _ _ _ hLdf hLd2f hLd3f hKstar2 hKstar3
  unfold expJet4VtpConst
  positivity

set_option maxHeartbeats 6400000 in
/-- **The (D) core, Rung 4 — the `v`-two-point Lipschitz bound of the fourth-variation value.**
    `‖Rv 1 − Rw 1‖ ≤ expJet4VtpConst·‖v−w‖·‖h‖·‖k‖·‖l‖·‖m‖`.  The residual `D = Rv − Rw` solves
    `D' = DF(Y_v)(D) + ρ₄`; the `ρ₄`-residual telescopes into fifty-one sub-terms, each
    `≤ C·‖v−w‖‖h‖‖k‖‖l‖‖m‖`; then the residual Grönwall (`expJet4Val_v_two_pt_diff_gronwall`). -/
theorem expJet4Val_v_two_pt_diff
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f Ld3f Ld4f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi)) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD3F : LipschitzOnWith Ld3f (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD4F : LipschitzOnWith Ld4f (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar2f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar2)
    (hKstar3f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p u t)‖ ≤ Kstar3)
    (hKstar4f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p u t)‖ ≤ Kstar4)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (Qhkv Qhlv Qhmv Qklv Qkmv Qlmv : ℝ → (Point n × Point n))
    (Qhkw Qhlw Qhmw Qklw Qkmw Qlmw : ℝ → (Point n × Point n))
    (Qhklv Qhkmv Qhlmv Qklmv : ℝ → (Point n × Point n))
    (Qhklw Qhkmw Qhlmw Qklmw : ℝ → (Point n × Point n))
    (Rv Rw : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hQhkv0 : Qhkv 0 = 0)
    (hQhlv0 : Qhlv 0 = 0)
    (hQhmv0 : Qhmv 0 = 0)
    (hQklv0 : Qklv 0 = 0)
    (hQkmv0 : Qkmv 0 = 0)
    (hQlmv0 : Qlmv 0 = 0)
    (hQhkw0 : Qhkw 0 = 0)
    (hQhlw0 : Qhlw 0 = 0)
    (hQhmw0 : Qhmw 0 = 0)
    (hQklw0 : Qklw 0 = 0)
    (hQkmw0 : Qkmw 0 = 0)
    (hQlmw0 : Qlmw 0 = 0)
    (hQhklv0 : Qhklv 0 = 0)
    (hQhkmv0 : Qhkmv 0 = 0)
    (hQhlmv0 : Qhlmv 0 = 0)
    (hQklmv0 : Qklmv 0 = 0)
    (hQhklw0 : Qhklw 0 = 0)
    (hQhkmw0 : Qhkmw 0 = 0)
    (hQhlmw0 : Qhlmw 0 = 0)
    (hQklmw0 : Qklmw 0 = 0)
    (hRv0 : Rv 0 = 0) (hRw0 : Rw 0 = 0)
    (hQhkvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkv t) + expJet2Rhs g gi hC p v Φv h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlv t) + expJet2Rhs g gi hC p v Φv h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhmv t) + expJet2Rhs g gi hC p v Φv h m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklv t) + expJet2Rhs g gi hC p v Φv k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qkmv t) + expJet2Rhs g gi hC p v Φv k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qlmv t) + expJet2Rhs g gi hC p v Φv l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkw t) + expJet2Rhs g gi hC p w Φw h k t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlw t) + expJet2Rhs g gi hC p w Φw h l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhmw t) + expJet2Rhs g gi hC p w Φw h m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklw t) + expJet2Rhs g gi hC p w Φw k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQkmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qkmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qkmw t) + expJet2Rhs g gi hC p w Φw k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQlmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qlmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qlmw t) + expJet2Rhs g gi hC p w Φw l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhklv t) + expJet3Rhs g gi hC p v Φv Qklv Qhlv Qhkv h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhkmv t) + expJet3Rhs g gi hC p v Φv Qkmv Qhmv Qhkv h k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qhlmv t) + expJet3Rhs g gi hC p v Φv Qlmv Qhmv Qhlv h l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qklmv t) + expJet3Rhs g gi hC p v Φv Qlmv Qkmv Qklv k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhklwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhklw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhklw t) + expJet3Rhs g gi hC p w Φw Qklw Qhlw Qhkw h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQhkmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhkmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhkmw t) + expJet3Rhs g gi hC p w Φw Qkmw Qhmw Qhkw h k m t) (Set.Icc (0 : ℝ) 1) t)
    (hQhlmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qhlmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qhlmw t) + expJet3Rhs g gi hC p w Φw Qlmw Qhmw Qhlw h l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQklmwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Qklmw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qklmw t) + expJet3Rhs g gi hC p w Φw Qlmw Qkmw Qklw k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRvd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rv
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Rv t) + expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRwd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Rw
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t) + expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw h k l m t) (Set.Icc (0 : ℝ) 1) t) :
    ‖Rv 1 - Rw 1‖
      ≤ expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ)
          Kstar Kstar2 Kstar3 Kstar4 * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
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
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD2diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p w t)‖
        ≤ (Ld2f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD2F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD3diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t) - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p w t)‖
        ≤ (Ld3f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD3F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hD4diff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t) - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p w t)‖
        ≤ (Ld4f : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipD4F.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  have hΦdiff := expFund_two_pt_diff_Icc g gi hC p v w Kf Ldf Kstar hKstar0 hLipF hLipDF
    hKstarv hKstarw hv hw Φv Φw hΦv0 hΦw0 hΦvd hΦwd
  have hval_hkv := expJet2Fund_value_bound_Icc g gi hC p v Φv h k Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhkv hQhkv0 hQhkvd
  have hval_hlv := expJet2Fund_value_bound_Icc g gi hC p v Φv h l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhlv hQhlv0 hQhlvd
  have hval_hmv := expJet2Fund_value_bound_Icc g gi hC p v Φv h m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qhmv hQhmv0 hQhmvd
  have hval_klv := expJet2Fund_value_bound_Icc g gi hC p v Φv k l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qklv hQklv0 hQklvd
  have hval_kmv := expJet2Fund_value_bound_Icc g gi hC p v Φv k m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qkmv hQkmv0 hQkmvd
  have hval_lmv := expJet2Fund_value_bound_Icc g gi hC p v Φv l m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarv hK2v hΦvnorm Qlmv hQlmv0 hQlmvd
  have hval_hkw := expJet2Fund_value_bound_Icc g gi hC p w Φw h k Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhkw hQhkw0 hQhkwd
  have hval_hlw := expJet2Fund_value_bound_Icc g gi hC p w Φw h l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhlw hQhlw0 hQhlwd
  have hval_hmw := expJet2Fund_value_bound_Icc g gi hC p w Φw h m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qhmw hQhmw0 hQhmwd
  have hval_klw := expJet2Fund_value_bound_Icc g gi hC p w Φw k l Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qklw hQklw0 hQklwd
  have hval_kmw := expJet2Fund_value_bound_Icc g gi hC p w Φw k m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qkmw hQkmw0 hQkmwd
  have hval_lmw := expJet2Fund_value_bound_Icc g gi hC p w Φw l m Kstar Kstar2 (Real.exp Kstar)
    hKstar0 hKstar20 (Real.exp_pos _).le hKstarw hK2w hΦwnorm Qlmw hQlmw0 hQlmwd
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
  have hval3_hlmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlmv Qhmv Qhlv h l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lmv hval_hmv hval_hlv Qhlmv hQhlmv0 hQhlmvd t ht).trans (le_of_eq (by ring))
  have hval3_klmv : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmv t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p v Φv Qlmv Qkmv Qklv k l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarv hK3v hK2v hΦvnorm
      hval_lmv hval_kmv hval_klv Qklmv hQklmv0 hQklmvd t ht).trans (le_of_eq (by ring))
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
  have hval3_hlmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlmw Qhmw Qhlw h l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lmw hval_hmw hval_hlw Qhlmw hQhlmw0 hQhlmwd t ht).trans (le_of_eq (by ring))
  have hval3_klmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmw t‖ ≤ ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet3Fund_value_bound_Icc g gi hC p w Φw Qlmw Qkmw Qklw k l m
      Kstar Kstar3 Kstar2 (Real.exp Kstar) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
      hKstar0 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK3w hK2w hΦwnorm
      hval_lmw hval_kmw hval_klw Qklmw hQklmw0 hQklmwd t ht).trans (le_of_eq (by ring))
  have htp_hk := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhkv Qhkw h k hQhkv0 hQhkw0 hQhkvd hQhkwd
  have htp_hl := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhlv Qhlw h l hQhlv0 hQhlw0 hQhlvd hQhlwd
  have htp_hm := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qhmv Qhmw h m hQhmv0 hQhmw0 hQhmvd hQhmwd
  have htp_kl := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qklv Qklw k l hQklv0 hQklw0 hQklvd hQklwd
  have htp_km := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qkmv Qkmw k m hQkmv0 hQkmw0 hQkmvd hQkmwd
  have htp_lm := expJet2_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Kstar Kstar2
    hKstar0 hKstar20 hLipF hLipDF hLipD2F hKstar hKstar2f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qlmw l m hQlmv0 hQlmw0 hQlmvd hQlmwd
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
  have htp3_hlm := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qhmv Qhlv Qlmw Qhmw Qhlw Qhlmv Qhlmw h l m
    hQlmv0 hQhmv0 hQhlv0 hQlmw0 hQhmw0 hQhlw0 hQhlmv0 hQhlmw0
    hQlmvd hQhmvd hQhlvd hQlmwd hQhmwd hQhlwd hQhlmvd hQhlmwd
  have htp3_klm := expJet3Val_v_two_pt_Icc_const g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
    hKstar0 hKstar20 hKstar30 hLipF hLipDF hLipD2F hLipD3F hKstar hKstar2f hKstar3f Φv Φw hΦv0 hΦw0 hΦvd hΦwd
    Qlmv Qkmv Qklv Qlmw Qkmw Qklw Qklmv Qklmw k l m
    hQlmv0 hQkmv0 hQklv0 hQlmw0 hQkmw0 hQklw0 hQklmv0 hQklmw0
    hQlmvd hQkmvd hQklvd hQlmwd hQkmwd hQklwd hQklmvd hQklmwd
  have hRwval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Rw t‖ ≤ ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
    fun t ht => (expJet4Fund_value_bound_Icc g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw
      Qhklw Qhkmw Qhlmw Qklmw h k l m Kstar Kstar4 Kstar3 Kstar2 (Real.exp Kstar)
      ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖) ((Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
      (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖) (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖) (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖) (((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
      hKstar0 hKstar40 hKstar30 hKstar20 (Real.exp_pos _).le hKstarw hK4w hK3w hK2w hΦwnorm
      hval_hkw hval_hlw hval_hmw hval_klw hval_kmw hval_lmw hval3_hklw hval3_hkmw hval3_hlmw hval3_klmw
      Rw hRw0 hRwd t ht).trans (le_of_eq (by ring))
  set ρ4 : ℝ := ((Ldf : ℝ) * Real.exp (Kf : ℝ) * ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld4f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 4) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) + ((Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) with hρ4def
  have hCe2 : 0 ≤ expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 :=
    expJet2VtpConst_nonneg _ _ _ _ _ Ldf.2 Ld2f.2 hKstar20
  have hCe3 : 0 ≤ expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3 :=
    expJet3VtpConst_nonneg _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 hKstar20 hKstar30
  have hρ40 : 0 ≤ ρ4 := by rw [hρ4def]; positivity
  have hrbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Rw t)
         + (expJet4Rhs g gi hC p v Φv Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
              h k l m t
            - expJet4Rhs g gi hC p w Φw Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw
                h k l m t)‖ ≤ ρ4 := by
    intro t ht
    simp only [expJet4Rhs_apply]
    set yv := expTube g gi hC p v t with hyvE
    set yw := expTube g gi hC p w t with hywE
    set dv := fderiv ℝ (geodesicField g gi) yv with hdvE
    set dw := fderiv ℝ (geodesicField g gi) yw with hdwE
    set d2v := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yv with hd2vE
    set d2w := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yw with hd2wE
    set d3v := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yv with hd3vE
    set d3w := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yw with hd3wE
    set d4v := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) yv with hd4vE
    set d4w := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) yw with hd4wE
    set ph := Φv t (expJetIota h) with hphE
    set ph' := Φw t (expJetIota h) with hph'E
    set pk := Φv t (expJetIota k) with hpkE
    set pk' := Φw t (expJetIota k) with hpk'E
    set pl := Φv t (expJetIota l) with hplE
    set pl' := Φw t (expJetIota l) with hpl'E
    set pm := Φv t (expJetIota m) with hpmE
    set pm' := Φw t (expJetIota m) with hpm'E
    set qhkv := Qhkv t with hqhkvE
    set qhkw := Qhkw t with hqhkwE
    set qhlv := Qhlv t with hqhlvE
    set qhlw := Qhlw t with hqhlwE
    set qhmv := Qhmv t with hqhmvE
    set qhmw := Qhmw t with hqhmwE
    set qklv := Qklv t with hqklvE
    set qklw := Qklw t with hqklwE
    set qkmv := Qkmv t with hqkmvE
    set qkmw := Qkmw t with hqkmwE
    set qlmv := Qlmv t with hqlmvE
    set qlmw := Qlmw t with hqlmwE
    set qhklv := Qhklv t with hqhklvE
    set qhklw := Qhklw t with hqhklwE
    set qhkmv := Qhkmv t with hqhkmvE
    set qhkmw := Qhkmw t with hqhkmwE
    set qhlmv := Qhlmv t with hqhlmvE
    set qhlmw := Qhlmw t with hqhlmwE
    set qklmv := Qklmv t with hqklmvE
    set qklmw := Qklmw t with hqklmwE
    set rw := Rw t with hrwE
    have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
    have hd3n : ‖d3v‖ ≤ Kstar3 := hK3v t ht
    have hd4n : ‖d4v‖ ≤ Kstar4 := hK4v t ht
    have hpn_h : ‖ph‖ ≤ Real.exp Kstar * ‖h‖ :=
      clmApply_norm_le (Φv t) (expJetIota h) (Real.exp_pos _).le (hΦvnorm t ht) hιh
    have hpn'_h : ‖ph'‖ ≤ Real.exp Kstar * ‖h‖ :=
      clmApply_norm_le (Φw t) (expJetIota h) (Real.exp_pos _).le (hΦwnorm t ht) hιh
    have hpn_k : ‖pk‖ ≤ Real.exp Kstar * ‖k‖ :=
      clmApply_norm_le (Φv t) (expJetIota k) (Real.exp_pos _).le (hΦvnorm t ht) hιk
    have hpn'_k : ‖pk'‖ ≤ Real.exp Kstar * ‖k‖ :=
      clmApply_norm_le (Φw t) (expJetIota k) (Real.exp_pos _).le (hΦwnorm t ht) hιk
    have hpn_l : ‖pl‖ ≤ Real.exp Kstar * ‖l‖ :=
      clmApply_norm_le (Φv t) (expJetIota l) (Real.exp_pos _).le (hΦvnorm t ht) hιl
    have hpn'_l : ‖pl'‖ ≤ Real.exp Kstar * ‖l‖ :=
      clmApply_norm_le (Φw t) (expJetIota l) (Real.exp_pos _).le (hΦwnorm t ht) hιl
    have hpn_m : ‖pm‖ ≤ Real.exp Kstar * ‖m‖ :=
      clmApply_norm_le (Φv t) (expJetIota m) (Real.exp_pos _).le (hΦvnorm t ht) hιm
    have hpn'_m : ‖pm'‖ ≤ Real.exp Kstar * ‖m‖ :=
      clmApply_norm_le (Φw t) (expJetIota m) (Real.exp_pos _).le (hΦwnorm t ht) hιm
    have hpd_h : ‖ph - ph'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖ := by
      rw [hphE, hph'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota h)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) h‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖h‖ :=
            mul_le_mul (hΦdiff t ht) hιh (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖h‖ := by ring
    have hpd_k : ‖pk - pk'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖ := by
      rw [hpkE, hpk'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota k)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) k‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖k‖ :=
            mul_le_mul (hΦdiff t ht) hιk (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖k‖ := by ring
    have hpd_l : ‖pl - pl'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖l‖ := by
      rw [hplE, hpl'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota l)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) l‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖l‖ :=
            mul_le_mul (hΦdiff t ht) hιl (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖l‖ := by ring
    have hpd_m : ‖pm - pm'‖
        ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖m‖ := by
      rw [hpmE, hpm'E, ← ContinuousLinearMap.sub_apply]
      calc ‖(Φv t - Φw t) (expJetIota m)‖
          ≤ ‖Φv t - Φw t‖ * ‖expJetIota (n := n) m‖ := (Φv t - Φw t).le_opNorm _
        _ ≤ (((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖) * ‖m‖ :=
            mul_le_mul (hΦdiff t ht) hιm (norm_nonneg _) (by positivity)
        _ = ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ * ‖m‖ := by ring
    have hG0 : ‖(dv - dw) rw‖ ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * ((Kstar4 * Real.exp Kstar ^ 4 + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2 + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
      (clmApply_norm_le (dv - dw) rw (by positivity) (hDFdiff t ht) (hRwval t ht)).trans (le_of_eq (by ring))
    have hD1 : ‖d4v ph pk pl pm - d4w ph' pk' pl' pm'‖ ≤ (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld4f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 4) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm4_diff_eq d4v d4w ph pk pl pm ph' pk' pl' pm']
      have b1 : ‖d4v (ph - ph') pk pl pm‖ ≤ (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply4_norm_le d4v (ph - ph') pk pl pm hKstar40 (by positivity) (by positivity) (by positivity) hd4n hpd_h hpn_k hpn_l hpn_m).trans (le_of_eq (by ring))
      have b2 : ‖d4v ph' (pk - pk') pl pm‖ ≤ (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply4_norm_le d4v ph' (pk - pk') pl pm hKstar40 (by positivity) (by positivity) (by positivity) hd4n hpn'_h hpd_k hpn_l hpn_m).trans (le_of_eq (by ring))
      have b3 : ‖d4v ph' pk' (pl - pl') pm‖ ≤ (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply4_norm_le d4v ph' pk' (pl - pl') pm hKstar40 (by positivity) (by positivity) (by positivity) hd4n hpn'_h hpn'_k hpd_l hpn_m).trans (le_of_eq (by ring))
      have b4 : ‖d4v ph' pk' pl' (pm - pm')‖ ≤ (Kstar4 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply4_norm_le d4v ph' pk' pl' (pm - pm') hKstar40 (by positivity) (by positivity) (by positivity) hd4n hpn'_h hpn'_k hpn'_l hpd_m).trans (le_of_eq (by ring))
      have b5 : ‖(d4v - d4w) ph' pk' pl' pm'‖ ≤ ((Ld4f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 4) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply4_norm_le (d4v - d4w) ph' pk' pl' pm' (by positivity) (by positivity) (by positivity) (by positivity) (hD4diff t ht) hpn'_h hpn'_k hpn'_l hpn'_m).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b5)
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD2 : ‖d3v pl pm qhkv - d3w pl' pm' qhkw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w pl pm qhkv pl' pm' qhkw]
      have b1 : ‖d3v (pl - pl') pm qhkv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (pl - pl') pm qhkv hKstar30 (by positivity) (by positivity) hd3n hpd_l hpn_m (hval_hkv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v pl' (pm - pm') qhkv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pl' (pm - pm') qhkv hKstar30 (by positivity) (by positivity) hd3n hpn'_l hpd_m (hval_hkv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v pl' pm' (qhkv - qhkw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pl' pm' (qhkv - qhkw) hKstar30 (by positivity) (by positivity) hd3n hpn'_l hpn'_m (htp_hk t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) pl' pm' qhkw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) pl' pm' qhkw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_l hpn'_m (hval_hkw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD3 : ‖d3v pk pm qhlv - d3w pk' pm' qhlw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w pk pm qhlv pk' pm' qhlw]
      have b1 : ‖d3v (pk - pk') pm qhlv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (pk - pk') pm qhlv hKstar30 (by positivity) (by positivity) hd3n hpd_k hpn_m (hval_hlv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v pk' (pm - pm') qhlv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pk' (pm - pm') qhlv hKstar30 (by positivity) (by positivity) hd3n hpn'_k hpd_m (hval_hlv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v pk' pm' (qhlv - qhlw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pk' pm' (qhlv - qhlw) hKstar30 (by positivity) (by positivity) hd3n hpn'_k hpn'_m (htp_hl t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) pk' pm' qhlw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) pk' pm' qhlw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_k hpn'_m (hval_hlw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD4 : ‖d3v pk pl qhmv - d3w pk' pl' qhmw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w pk pl qhmv pk' pl' qhmw]
      have b1 : ‖d3v (pk - pk') pl qhmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (pk - pk') pl qhmv hKstar30 (by positivity) (by positivity) hd3n hpd_k hpn_l (hval_hmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v pk' (pl - pl') qhmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pk' (pl - pl') qhmv hKstar30 (by positivity) (by positivity) hd3n hpn'_k hpd_l (hval_hmv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v pk' pl' (qhmv - qhmw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v pk' pl' (qhmv - qhmw) hKstar30 (by positivity) (by positivity) hd3n hpn'_k hpn'_l (htp_hm t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) pk' pl' qhmw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) pk' pl' qhmw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_k hpn'_l (hval_hmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD5 : ‖d3v ph pm qklv - d3w ph' pm' qklw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w ph pm qklv ph' pm' qklw]
      have b1 : ‖d3v (ph - ph') pm qklv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (ph - ph') pm qklv hKstar30 (by positivity) (by positivity) hd3n hpd_h hpn_m (hval_klv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v ph' (pm - pm') qklv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' (pm - pm') qklv hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpd_m (hval_klv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v ph' pm' (qklv - qklw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' pm' (qklv - qklw) hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpn'_m (htp_kl t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) ph' pm' qklw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) ph' pm' qklw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_h hpn'_m (hval_klw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD6 : ‖d3v ph pl qkmv - d3w ph' pl' qkmw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w ph pl qkmv ph' pl' qkmw]
      have b1 : ‖d3v (ph - ph') pl qkmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (ph - ph') pl qkmv hKstar30 (by positivity) (by positivity) hd3n hpd_h hpn_l (hval_kmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v ph' (pl - pl') qkmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' (pl - pl') qkmv hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpd_l (hval_kmv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v ph' pl' (qkmv - qkmw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' pl' (qkmv - qkmw) hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpn'_l (htp_km t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) ph' pl' qkmw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) ph' pl' qkmw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_h hpn'_l (hval_kmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD7 : ‖d3v ph pk qlmv - d3w ph' pk' qlmw‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm3_diff_eq d3v d3w ph pk qlmv ph' pk' qlmw]
      have b1 : ‖d3v (ph - ph') pk qlmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v (ph - ph') pk qlmv hKstar30 (by positivity) (by positivity) hd3n hpd_h hpn_k (hval_lmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d3v ph' (pk - pk') qlmv‖ ≤ (Kstar3 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' (pk - pk') qlmv hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpd_k (hval_lmv t ht)).trans (le_of_eq (by ring))
      have b3 : ‖d3v ph' pk' (qlmv - qlmw)‖ ≤ (Kstar3 * Real.exp Kstar ^ 2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le d3v ph' pk' (qlmv - qlmw) hKstar30 (by positivity) (by positivity) hd3n hpn'_h hpn'_k (htp_lm t ht)).trans (le_of_eq (by ring))
      have b4 : ‖(d3v - d3w) ph' pk' qlmw‖ ≤ ((Ld3f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply3_norm_le (d3v - d3w) ph' pk' qlmw (by positivity) (by positivity) (by positivity) (hD3diff t ht) hpn'_h hpn'_k (hval_lmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b4)
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD8 : ‖d2v qhkv qlmv - d2w qhkw qlmw‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w qhkv qlmv qhkw qlmw]
      have b1 : ‖d2v (qhkv - qhkw) qlmv‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (qhkv - qhkw) qlmv hKstar20 (by positivity) hd2n (htp_hk t ht) (hval_lmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v qhkw (qlmv - qlmw)‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v qhkw (qlmv - qlmw) hKstar20 (by positivity) hd2n (hval_hkw t ht) (htp_lm t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) qhkw qlmw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) qhkw qlmw (by positivity) (by positivity) (hD2diff t ht) (hval_hkw t ht) (hval_lmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD9 : ‖d2v qhlv qkmv - d2w qhlw qkmw‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w qhlv qkmv qhlw qkmw]
      have b1 : ‖d2v (qhlv - qhlw) qkmv‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (qhlv - qhlw) qkmv hKstar20 (by positivity) hd2n (htp_hl t ht) (hval_kmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v qhlw (qkmv - qkmw)‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v qhlw (qkmv - qkmw) hKstar20 (by positivity) hd2n (hval_hlw t ht) (htp_km t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) qhlw qkmw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) qhlw qkmw (by positivity) (by positivity) (hD2diff t ht) (hval_hlw t ht) (hval_kmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD10 : ‖d2v qhmv qklv - d2w qhmw qklw‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w qhmv qklv qhmw qklw]
      have b1 : ‖d2v (qhmv - qhmw) qklv‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (qhmv - qhmw) qklv hKstar20 (by positivity) hd2n (htp_hm t ht) (hval_klv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v qhmw (qklv - qklw)‖ ≤ (Kstar2 * expJet2VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) Kstar Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v qhmw (qklv - qklw) hKstar20 (by positivity) hd2n (hval_hmw t ht) (htp_kl t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) qhmw qklw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) qhmw qklw (by positivity) (by positivity) (hD2diff t ht) (hval_hmw t ht) (hval_klw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD11 : ‖d2v ph qklmv - d2w ph' qklmw‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w ph qklmv ph' qklmw]
      have b1 : ‖d2v (ph - ph') qklmv‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (ph - ph') qklmv hKstar20 (by positivity) hd2n hpd_h (hval3_klmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v ph' (qklmv - qklmw)‖ ≤ (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v ph' (qklmv - qklmw) hKstar20 (by positivity) hd2n hpn'_h (htp3_klm t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) ph' qklmw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) ph' qklmw (by positivity) (by positivity) (hD2diff t ht) hpn'_h (hval3_klmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD12 : ‖d2v pk qhlmv - d2w pk' qhlmw‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w pk qhlmv pk' qhlmw]
      have b1 : ‖d2v (pk - pk') qhlmv‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (pk - pk') qhlmv hKstar20 (by positivity) hd2n hpd_k (hval3_hlmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v pk' (qhlmv - qhlmw)‖ ≤ (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v pk' (qhlmv - qhlmw) hKstar20 (by positivity) hd2n hpn'_k (htp3_hlm t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) pk' qhlmw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) pk' qhlmw (by positivity) (by positivity) (hD2diff t ht) hpn'_k (hval3_hlmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD13 : ‖d2v pl qhkmv - d2w pl' qhkmw‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w pl qhkmv pl' qhkmw]
      have b1 : ‖d2v (pl - pl') qhkmv‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (pl - pl') qhkmv hKstar20 (by positivity) hd2n hpd_l (hval3_hkmv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v pl' (qhkmv - qhkmw)‖ ≤ (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v pl' (qhkmv - qhkmw) hKstar20 (by positivity) hd2n hpn'_l (htp3_hkm t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) pl' qhkmw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) pl' qhkmw (by positivity) (by positivity) (hD2diff t ht) hpn'_l (hval3_hkmw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    have hD14 : ‖d2v pm qhklv - d2w pm' qhklw‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ + ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
      rw [clm2_diff_eq d2v d2w pm qhklv pm' qhklw]
      have b1 : ‖d2v (pm - pm') qhklv‖ ≤ (Kstar2 * ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v (pm - pm') qhklv hKstar20 (by positivity) hd2n hpd_m (hval3_hklv t ht)).trans (le_of_eq (by ring))
      have b2 : ‖d2v pm' (qhklv - qhklw)‖ ≤ (Kstar2 * Real.exp Kstar * expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le d2v pm' (qhklv - qhklw) hKstar20 (by positivity) hd2n hpn'_m (htp3_hkl t ht)).trans (le_of_eq (by ring))
      have b3 : ‖(d2v - d2w) pm' qhklw‖ ≤ ((Ld2f : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3 + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar)) * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
        (clmApply2_norm_le (d2v - d2w) pm' qhklw (by positivity) (by positivity) (hD2diff t ht) hpn'_m (hval3_hklw t ht)).trans (le_of_eq (by ring))
      refine (norm_add_le _ _).trans (add_le_add ?_ b3)
      exact (norm_add_le _ _).trans (add_le_add b1 b2)
    rw [regroup14 ((dv - dw) rw) (d4v ph pk pl pm) (d3v pl pm qhkv) (d3v pk pm qhlv) (d3v pk pl qhmv) (d3v ph pm qklv) (d3v ph pl qkmv) (d3v ph pk qlmv) (d2v qhkv qlmv) (d2v qhlv qkmv) (d2v qhmv qklv) (d2v ph qklmv) (d2v pk qhlmv) (d2v pl qhkmv) (d2v pm qhklv) (d4w ph' pk' pl' pm') (d3w pl' pm' qhkw) (d3w pk' pm' qhlw) (d3w pk' pl' qhmw) (d3w ph' pm' qklw) (d3w ph' pl' qkmw) (d3w ph' pk' qlmw) (d2w qhkw qlmw) (d2w qhlw qkmw) (d2w qhmw qklw) (d2w ph' qklmw) (d2w pk' qhlmw) (d2w pl' qhkmw) (d2w pm' qhklw)]
    rw [hρ4def]
    refine (norm_add_le _ _).trans (add_le_add ?_ hD14)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD13)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD12)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD11)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD10)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD9)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD8)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD7)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD6)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD5)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD4)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD3)
    refine (norm_add_le _ _).trans (add_le_add ?_ hD2)
    exact (norm_add_le _ _).trans (add_le_add hG0 hD1)
  have hfin := expJet4Val_v_two_pt_diff_gronwall g gi hC p v w Kstar hKstar0
    Φv Φw Qhkv Qhlv Qhmv Qklv Qkmv Qlmv Qhklv Qhkmv Qhlmv Qklmv
    Qhkw Qhlw Qhmw Qklw Qkmw Qlmw Qhklw Qhkmw Qhlmw Qklmw Rv Rw h k l m
    hRv0 hRw0 hRvd hRwd hKstarv ρ4 hρ40 hrbound
  refine hfin.trans (le_of_eq ?_)
  rw [hρ4def]
  unfold expJet4VtpConst
  ring

end QIQTH.ExpMap
