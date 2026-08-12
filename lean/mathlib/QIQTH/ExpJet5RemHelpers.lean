/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Residual

/-!
# Jet₅ quadratic-remainder helper layer — rung J5-5b (prefix)

Reusable, whnf-safe building blocks for the order-5 parameter quadratic-remainder cancellation
`expJet5_remainder_quadratic_bound` (the killer feeder of the J5-5 tower, still to be assembled).
This is a FAITHFUL one-Fréchet-order-up mirror of the order-4 remainder infrastructure
(`ExpJet4Remainder.lean`), factored into small standalone lemmas so the quintuply-nested-CLM `whnf`
never fires inside a monolithic proof.

Contents:
* the generic multilinear CLM-application norm bounds `clmApply_norm_le` … `clmApply5_norm_le`
  (the order-4 `clmApply≤4` helpers plus the new quintilinear `clmApply5_norm_le` the order-5
  pure/top block needs) — abstract normed spaces, no tube atoms, so they elaborate fast;
* `remBlk0_bound` — the **abstract Block-0 telescoping bound**, a pure multilinear-algebra lemma:
  the `(dw − dv)·qw − D²·Pr·qv` head term of the order-5 master identity telescopes into three
  grouped residuals each bounded by `C·nr²`.  This is the direct mirror of the order-4 Block-0
  argument (`ExpJet4Remainder.lean:391`), with the perturbation direction `m ↦ r` (`nr = ‖r‖`) and
  the order-3 solution replaced by the order-4 fundamental solution.  Stated over an abstract normed
  space with the residual bounds carried as hypotheses, so it is reusable by the concrete assembly
  (which instantiates `D² := fderiv² F (Y_v t)`, `dw/dv := DF (Y_{w/v} t)`, and supplies the tube
  Taylor / accuracy / Lipschitz / value bounds).

## Honest firewall (binding)

Helper/prefix layer of J5-5 brick (b) ONLY.  These lemmas are pure functional-analysis norm
estimates and an algebraic telescoping; they do NOT by themselves prove
`expJet5_remainder_quadratic_bound` (which additionally needs the top block, the fourteen cross
blocks, and the final assembly), do NOT prove `expJet5_remainder_quadratic_bound_P` / `_unif`, do NOT
reach `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`
(CONDITIONAL).
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

-- The quintuply-nested continuous-linear-map spaces (`E →L F →L G →L H →L I →L J`) chain their
-- normed-group / norm instances one level deeper than the order-4 case, so raise the
-- pending-instance synthesis depth exactly as the order-4/order-5 prerequisite files do.
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

/-! ### Generic multilinear CLM-application norm bounds

Order-4 helpers (`clmApply≤4`) plus the quintilinear `clmApply5_norm_le`.  Kept fully generic
(abstract normed spaces, no tube atoms) so the deeply-nested-CLM `whnf` never fires here. -/

/-- **CLM-application norm bound with an explicit factored constant.**  `‖C a‖ ≤ KC · Ka`. -/
theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

/-- **Generic bilinear CLM-application norm bound.**  `‖B a b‖ ≤ KB · Ka · Kb`. -/
theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

/-- **Generic trilinear CLM-application norm bound.**  `‖B a b c‖ ≤ KB · Ka · Kb · Kc`. -/
theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
  clmApply2_norm_le (B a) b c (mul_nonneg hKB hKa) hKb (clmApply_norm_le B a hKB hB ha) hb hc

/-- **Generic quadrilinear CLM-application norm bound.**  `‖B a b c d‖ ≤ KB · Ka · Kb · Kc · Kd`. -/
theorem clmApply4_norm_le {E F G H I : Type*}
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

-- (the quintilinear helper `clmApply5_norm_le`, which the order-5 pure/top block needs, is already
-- banked publicly in `ExpJet5Phase2.lean` and re-exported here by import.)

/-! ### Abstract Block-0 telescoping bound -/

/-- **Abstract Block-0 quadratic bound** (mirror of the order-4 Block-0 argument
    `ExpJet4Remainder.lean:391`, one Fréchet order up: perturbation `m ↦ r`, `nr = ‖r‖`, the
    third-variation solution replaced by the order-4 fundamental solution).

    In the order-5 master identity the head term `(dw − dv) qw − D²·Pr·qv` (where `dw = DF(Y_w t)`,
    `dv = DF(Y_v t)`, `D² = fderiv² F (Y_v t)`, `qw`/`qv` are the order-4 fundamental solutions for
    `w = v + r`/`v`, `Pr = Φ t (ι r)`) telescopes exactly into three grouped residuals:
    `(dw − dv − D²(yw − yv)) qw`  (a `DF` second-order Taylor remainder),
    `D²(yw − yv − Pr) qw`         (a first-variation accuracy residual), and
    `D² Pr (qw − qv)`             (a solution-Lipschitz residual),
    each `O(nr²)` given the carried bounds.  Stated abstractly so the concrete assembly instantiates
    the fderiv atoms and feeds the tube Taylor / accuracy / Lipschitz / value bounds. -/
theorem remBlk0_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D2 : E →L[ℝ] E →L[ℝ] E) (dw dv : E →L[ℝ] E) (yw yv qw qv Pr : E)
    (nr L2 eKf M4 C2 Ce eKs Kstar2 : ℝ)
    (hnr : 0 ≤ nr)
    (hL2 : 0 ≤ L2) (hM4 : 0 ≤ M4) (hC2 : 0 ≤ C2) (hCe : 0 ≤ Ce) (heKs : 0 ≤ eKs)
    (hKstar2 : 0 ≤ Kstar2)
    (htay : ‖dw - dv - D2 (yw - yv)‖ ≤ L2 * (nr * eKf) ^ 2)
    (hqw : ‖qw‖ ≤ M4)
    (hd2 : ‖D2‖ ≤ Kstar2)
    (hacc : ‖yw - yv - Pr‖ ≤ C2 * nr ^ 2)
    (hPr : ‖Pr‖ ≤ eKs * nr)
    (hQlip : ‖qw - qv‖ ≤ Ce * nr) :
    ‖(dw - dv) qw - D2 Pr qv‖
      ≤ (L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce) * nr ^ 2 := by
  -- exact telescoping identity (validated numerically; closes by `abel`).
  have heq0 : (dw - dv) qw - D2 Pr qv
      = (dw - dv - D2 (yw - yv)) qw + D2 (yw - yv - Pr) qw + D2 Pr (qw - qv) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq0]
  -- term A: the `DF` second-order Taylor remainder against `qw`.
  have hA0 : ‖(dw - dv - D2 (yw - yv)) qw‖ ≤ (L2 * eKf ^ 2 * M4) * nr ^ 2 := by
    calc ‖(dw - dv - D2 (yw - yv)) qw‖
        ≤ ‖dw - dv - D2 (yw - yv)‖ * ‖qw‖ := (dw - dv - D2 (yw - yv)).le_opNorm _
      _ ≤ (L2 * (nr * eKf) ^ 2) * M4 :=
          mul_le_mul htay hqw (norm_nonneg _) (by positivity)
      _ = (L2 * eKf ^ 2 * M4) * nr ^ 2 := by ring
  -- term B: the accuracy residual against `qw`.
  have hB0 : ‖D2 (yw - yv - Pr) qw‖ ≤ (Kstar2 * C2 * M4) * nr ^ 2 :=
    (clmApply2_norm_le D2 (yw - yv - Pr) qw hKstar2 (mul_nonneg hC2 (sq_nonneg nr)) hd2 hacc
      hqw).trans (le_of_eq (by ring))
  -- term C: the solution-Lipschitz residual.
  have hC0 : ‖D2 Pr (qw - qv)‖ ≤ (Kstar2 * eKs * Ce) * nr ^ 2 :=
    (clmApply2_norm_le D2 Pr (qw - qv) hKstar2 (mul_nonneg heKs hnr) hd2 hPr hQlip).trans
      (le_of_eq (by ring))
  rw [show (L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce) * nr ^ 2
    = (L2 * eKf ^ 2 * M4) * nr ^ 2 + (Kstar2 * C2 * M4) * nr ^ 2
      + (Kstar2 * eKs * Ce) * nr ^ 2 from by ring]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hA0 hB0)) hC0)

end QIQTH.ExpMap
