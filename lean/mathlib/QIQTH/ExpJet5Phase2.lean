/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase1
import QIQTH.CurvedA1CenterAmp
import Mathlib

/-!
# JET-5 TOWER — phase 2 (brick J4-646, J5-2): the 51-term norm bound + compactness clones +
# the `[0,1]` global fundamental-solution existence `expJet5Fund`

Toward discharging `hch5` (chart ∈ C⁵, the sole remaining K1 regularity input): this file lands
phase J5-2 of the Jet-5 campaign — the D5 well-posedness layer the D5 Grönwall crux (J5-3)
consumes, the faithful one-Fréchet-order-up mirror of `ExpJet4Rhs.expJet4Rhs_norm_le` +
`ExpJet4FundGlobal` (`expJet4Fund_shifted` → `_shifted_integral` → `_glue` → `expJet4Fund`) and
of the Jet-4 compactness pair (`expJet_fderiv4_tube_bddAbove_unif`,
`expJet_fderiv4_lipschitzOnWith`):

* `clmApply5_norm_le` — the generic quintilinear CLM-application norm bound
  `‖B a b c d e‖ ≤ KB·Ka·Kb·Kc·Kd·Ke` (one order above `clmApply4_norm_le`; mechanical).
* ★ `expJet5Rhs_norm_le` — the **uniform `[0,1]` norm bound of the 51-term source `Θ₅^{hklmr}`**:
  given the `D⁵F/D⁴F/D³F/D²F` tube bounds `Kstar5/4/3/2`, a `[0,1]` bound `Cphi` on `‖Φ‖` and
  `[0,1]` bounds on the 25 abstract `Q`-variations, each of the 51 Faà-di-Bruno terms is bounded
  by the corresponding product (script-generated enumeration, EXACTLY the `expJet5Rhs` term
  order); triangle inequality assembles the 51-term polynomial bound.
* `expJet_fderiv5_tube_bddAbove_unif` — `D⁵F` uniformly tube-bounded on `[0,1]` (a single
  `Kstar5` for ALL admissible `v`; compactness of the confined tube ball).
* `expJet_fderiv5_lipschitzOnWith` — `D⁵F` Lipschitz on the confined tube ball (`C¹` on a
  compact convex set; the `hLipD5F` datum of the J5-3 crux).
* ★ `expJet5Fund` — the **`[0,1]` GLOBAL fifth-variation fundamental solution**: the affine field
  `F₅ t R := DF(Y_v t)(R) + Θ₅^{hklmr}(t)` has the SAME homogeneous linear part as every lower
  jet order (only the source changes), so the existence chain is a verbatim one-order-up mirror:
  `expJet5Field_continuousOn` → `expJet5Fund_shifted` (local Picard–Lindelöf at arbitrary IC) →
  `expJet5Fund_shifted_integral` (FTC-2 integral form) → `expJet5Fund_glue` (endpoint-matching
  concatenation of `N ≥ 2(KdF+1)` shifted solvers) → `expJet5Fund` (global integral equation +
  inhomogeneous derivative law).
* `expJet5FundSol_exists` — packaging: `IsExpJet5FundSol` (the phase-1 SHAPE) is INHABITED.
* Non-vacuity gates (cp466 discipline — antecedent inhabitance, not just conclusion shape):
  `expJet5Fund_gate_curved` instantiates the existence at the GENUINELY CURVED polynomial
  witness `g^κ = curvedRNCMetric (−1)` (with `hC` supplied by `curvedRNC_hChr`, `p = v = 0`,
  `hv` from `expRho_pos`) — every antecedent is DISCHARGED, the conclusion is inhabited;
  `expJet5Rhs_norm_le_gate` runs the 51-term bound end-to-end at the same witness with the tube
  bounds supplied by the four `_unif` compactness lemmas (all antecedents discharged).

## Honest firewall (binding)

**What is proven here:** the 51-term source norm bound, the order-5 compactness pair, and the
`[0,1]` global existence of the D5 fundamental solution (with `Φ`/`Q` abstract, exactly as at
order 4) — the prerequisites of the D5 Grönwall crux.  **What is NOT closed:** the remaining
Jet-5 phases — (J5-3) the order-5 two-point Grönwall crux `expJet5Val_v_two_pt_diff` carrying
`hLipD5F`/`Kstar5`; (J5-4) the quintilinear CLM packaging `expJetD5`(+`_two_pt_diff`); (J5-5)
`expMap_fderiv4_hasFDerivAt` + assembly discharging `hfd4` (⟹ `expMap_contDiffOn_five`
UNCONDITIONAL); (J5-6) the chart weld `uniformFlowExp_contDiffAt_five` = `hch5`.  `hfd4`/`hch5`
are NOT discharged; `exp_p ∈ C⁵` is NOT established.  `a₁ = R/6` remains CONDITIONAL (flat
tower non-vacuous; curved owes the Jet-5 completion + the Duhamel carry + fat-K carriers +
capstone co-instantiation at the corrected witness + prior piles).  NOT κ = 1/6, NOT the
heat-kernel parametrix, NOT numerical-`G` / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁵F` is a QUINTUPLY-nested continuous-linear-map space; raise the
-- pending-instance synthesis depth one level above the Jet-4 files (as in `ExpJet5Phase1`).
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
-- The 51-term source: elaborating the sum tree recurses deeper than the default 512.
set_option maxRecDepth 16384

variable {n : ℕ}

/-! ### §1. Generic multilinear CLM-application norm bounds (local copies + one order up) -/

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

/-- **Generic quadrilinear CLM-application norm bound.**  `‖B a b c d‖ ≤ KB·Ka·Kb·Kc·Kd`
    (local copy of the `ExpJet4Rhs` private helper). -/
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

/-- **Generic quintilinear CLM-application norm bound.**  `‖B a b c d e‖ ≤ KB·Ka·Kb·Kc·Kd·Ke`.
    The direct one-order-higher analog of `clmApply4_norm_le`: peel the outer application
    (`clmApply_norm_le`), then bound the resulting quadrilinear CLM `B a` on `b, c, d, e`.
    Kept fully generic (abstract normed spaces) so the quintuply-nested-CLM `whnf` never
    fires here. -/
theorem clmApply5_norm_le {E F G H I J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup J] [NormedSpace ℝ J]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I →L[ℝ] J) (a : E) (b : F) (c : G) (d : H) (e : I)
    {KB Ka Kb Kc Kd Ke : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc) (hKd : 0 ≤ Kd)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) (hd : ‖d‖ ≤ Kd)
    (he : ‖e‖ ≤ Ke) :
    ‖B a b c d e‖ ≤ KB * Ka * Kb * Kc * Kd * Ke :=
  clmApply4_norm_le (B a) b c d e (mul_nonneg hKB hKa) hKb hKc hKd
    (clmApply_norm_le B a hKB hB ha) hb hc hd he

/-! ### §2. The uniform `[0,1]` norm bound of the 51-term source `Θ₅^{hklmr}` -/

set_option maxHeartbeats 12800000 in
/-- **Uniform `[0,1]` norm bound of `Θ₅^{hklmr}`.**  Given the `D⁵F/D⁴F/D³F/D²F` tube bounds
    `Kstar5/4/3/2`, a `[0,1]` bound `Cphi` on `‖Φ t‖`, and `[0,1]` bounds on the 25 abstract
    second/third/fourth variations, the 51 Faà-di-Bruno terms are bounded term-by-term
    (quintuple `le_opNorm` via `clmApply5_norm_le` for the `D⁵F` term, quadruple for the ten
    `D⁴F` terms, triple for the twenty-five `D³F` terms, double for the fifteen `D²F` terms,
    with `‖Φ t (ιx)‖ ≤ Cphi·‖x‖` from `expJetIota_opNorm_le`), and the triangle inequality
    assembles the 51-term polynomial bound.  Mirror of `expJet4Rhs_norm_le` one order up;
    the enumeration is SCRIPT-GENERATED in exactly the `expJet5Rhs` term order (no-false-bound
    discipline).  The nonnegativity of the `Q`-bounds consumed in non-final CLM slots is derived
    from the bound hypotheses at the given `t`.  The D5 well-posedness bound the J5-3 crux
    consumes. -/
theorem expJet5Rhs_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (h k l m r : Point n)
    (Kstar5 Kstar4 Kstar3 Kstar2 Cphi : ℝ)
    (Cq_hk Cq_hl Cq_hm Cq_hr Cq_kl Cq_km Cq_kr Cq_lm Cq_lr Cq_mr : ℝ)
    (Cq_hkl Cq_hkm Cq_hkr Cq_hlm Cq_hlr Cq_hmr Cq_klm Cq_klr Cq_kmr Cq_lmr : ℝ)
    (Cq_hklm Cq_hklr Cq_hkmr Cq_hlmr Cq_klmr : ℝ)
    (hKstar50 : 0 ≤ Kstar5) (hKstar40 : 0 ≤ Kstar4) (hKstar30 : 0 ≤ Kstar3)
    (hKstar20 : 0 ≤ Kstar2) (hCphi0 : 0 ≤ Cphi)
    (hKstar5 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar5)
    (hKstar4 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4)
    (hKstar3 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3)
    (hKstar2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2)
    (hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi)
    (hCqhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq_hk)
    (hCqhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq_hl)
    (hCqhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhm t‖ ≤ Cq_hm)
    (hCqhr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhr t‖ ≤ Cq_hr)
    (hCqkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq_kl)
    (hCqkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq_km)
    (hCqkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkr t‖ ≤ Cq_kr)
    (hCqlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq_lm)
    (hCqlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlr t‖ ≤ Cq_lr)
    (hCqmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmr t‖ ≤ Cq_mr)
    (hCqhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq_hkl)
    (hCqhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq_hkm)
    (hCqhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Cq_hkr)
    (hCqhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq_hlm)
    (hCqhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Cq_hlr)
    (hCqhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Cq_hmr)
    (hCqklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq_klm)
    (hCqklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Cq_klr)
    (hCqkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Cq_kmr)
    (hCqlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Cq_lmr)
    (hCqhklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklm t‖ ≤ Cq_hklm)
    (hCqhklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhklr t‖ ≤ Cq_hklr)
    (hCqhkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkmr t‖ ≤ Cq_hkmr)
    (hCqhlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlmr t‖ ≤ Cq_hlmr)
    (hCqklmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklmr t‖ ≤ Cq_klmr)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖
      ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖)
        + Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm
        + Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr
        + Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr
        + Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr
        + Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm
        + Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr
        + Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm
        + Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr
        + Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km
        + Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr
        + Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl
        + Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm
        + Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km
        + Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl
        + Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm
        + Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr
        + Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr
        + Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr
        + Kstar2 * Cq_hkl * Cq_mr
        + Kstar2 * Cq_hkm * Cq_lr
        + Kstar2 * Cq_hkr * Cq_lm
        + Kstar2 * Cq_hlm * Cq_kr
        + Kstar2 * Cq_hlr * Cq_km
        + Kstar2 * Cq_hmr * Cq_kl
        + Kstar2 * Cq_klm * Cq_hr
        + Kstar2 * Cq_klr * Cq_hm
        + Kstar2 * Cq_kmr * Cq_hl
        + Kstar2 * Cq_lmr * Cq_hk
        + Kstar2 * (Cphi * ‖h‖) * Cq_klmr
        + Kstar2 * (Cphi * ‖k‖) * Cq_hlmr
        + Kstar2 * (Cphi * ‖l‖) * Cq_hkmr
        + Kstar2 * (Cphi * ‖m‖) * Cq_hklr
        + Kstar2 * (Cphi * ‖r‖) * Cq_hklm := by
  set D5 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
    (expTube g gi hC p v t) with hD5
  set D4 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)
    with hD4
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t) with hD3
  set D2 := fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t) with hD2
  -- first-variation vector bounds `‖Φ t (ι x)‖ ≤ Cphi·‖x‖`.
  have hP : ∀ x : Point n, ‖Φ t (expJetIota x)‖ ≤ Cphi * ‖x‖ := by
    intro x
    have hιx : ‖expJetIota (n := n) x‖ ≤ ‖x‖ := by
      refine ((expJetIota (n := n)).le_opNorm x).trans ?_
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg x)
    calc ‖Φ t (expJetIota x)‖ ≤ ‖Φ t‖ * ‖expJetIota (n := n) x‖ := (Φ t).le_opNorm _
      _ ≤ Cphi * ‖x‖ := mul_le_mul (hCphi t ht) hιx (norm_nonneg _) hCphi0
  have hnn : ∀ x : Point n, 0 ≤ Cphi * ‖x‖ := fun x => mul_nonneg hCphi0 (norm_nonneg _)
  -- nonnegativity of the `Q`-bounds (consumed in non-final CLM slots).
  have hCqhk0 : 0 ≤ Cq_hk := (norm_nonneg _).trans (hCqhk t ht)
  have hCqhl0 : 0 ≤ Cq_hl := (norm_nonneg _).trans (hCqhl t ht)
  have hCqhm0 : 0 ≤ Cq_hm := (norm_nonneg _).trans (hCqhm t ht)
  have hCqhr0 : 0 ≤ Cq_hr := (norm_nonneg _).trans (hCqhr t ht)
  have hCqkl0 : 0 ≤ Cq_kl := (norm_nonneg _).trans (hCqkl t ht)
  have hCqkm0 : 0 ≤ Cq_km := (norm_nonneg _).trans (hCqkm t ht)
  have hCqkr0 : 0 ≤ Cq_kr := (norm_nonneg _).trans (hCqkr t ht)
  have hCqlm0 : 0 ≤ Cq_lm := (norm_nonneg _).trans (hCqlm t ht)
  have hCqlr0 : 0 ≤ Cq_lr := (norm_nonneg _).trans (hCqlr t ht)
  have hCqmr0 : 0 ≤ Cq_mr := (norm_nonneg _).trans (hCqmr t ht)
  have hCqhkl0 : 0 ≤ Cq_hkl := (norm_nonneg _).trans (hCqhkl t ht)
  have hCqhkm0 : 0 ≤ Cq_hkm := (norm_nonneg _).trans (hCqhkm t ht)
  have hCqhkr0 : 0 ≤ Cq_hkr := (norm_nonneg _).trans (hCqhkr t ht)
  have hCqhlm0 : 0 ≤ Cq_hlm := (norm_nonneg _).trans (hCqhlm t ht)
  have hCqhlr0 : 0 ≤ Cq_hlr := (norm_nonneg _).trans (hCqhlr t ht)
  have hCqhmr0 : 0 ≤ Cq_hmr := (norm_nonneg _).trans (hCqhmr t ht)
  have hCqklm0 : 0 ≤ Cq_klm := (norm_nonneg _).trans (hCqklm t ht)
  have hCqklr0 : 0 ≤ Cq_klr := (norm_nonneg _).trans (hCqklr t ht)
  have hCqkmr0 : 0 ≤ Cq_kmr := (norm_nonneg _).trans (hCqkmr t ht)
  have hCqlmr0 : 0 ≤ Cq_lmr := (norm_nonneg _).trans (hCqlmr t ht)
  have hCqhklm0 : 0 ≤ Cq_hklm := (norm_nonneg _).trans (hCqhklm t ht)
  have hCqhklr0 : 0 ≤ Cq_hklr := (norm_nonneg _).trans (hCqhklr t ht)
  have hCqhkmr0 : 0 ≤ Cq_hkmr := (norm_nonneg _).trans (hCqhkmr t ht)
  have hCqhlmr0 : 0 ≤ Cq_hlmr := (norm_nonneg _).trans (hCqhlmr t ht)
  have hCqklmr0 : 0 ≤ Cq_klmr := (norm_nonneg _).trans (hCqklmr t ht)
  -- the 51 term-wise bounds (script-generated, exact `expJet5Rhs` order).
  have hb1 : ‖D5 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r))‖
      ≤ Kstar5 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) :=
    clmApply5_norm_le D5 _ _ _ _ _ hKstar50 (hnn h) (hnn k) (hnn l) (hnn m)
      (hKstar5 t ht) (hP h) (hP k) (hP l) (hP m) (hP r)
  have hb2 : ‖D4 (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t)‖
      ≤ Kstar4 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hk :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn l) (hnn m) (hnn r)
      (hKstar4 t ht) (hP l) (hP m) (hP r) (hCqhk t ht)
  have hb3 : ‖D4 (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t)‖
      ≤ Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hl :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn k) (hnn m) (hnn r)
      (hKstar4 t ht) (hP k) (hP m) (hP r) (hCqhl t ht)
  have hb4 : ‖D4 (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t)‖
      ≤ Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hm :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn k) (hnn l) (hnn r)
      (hKstar4 t ht) (hP k) (hP l) (hP r) (hCqhm t ht)
  have hb5 : ‖D4 (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t)‖
      ≤ Kstar4 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hr :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn k) (hnn l) (hnn m)
      (hKstar4 t ht) (hP k) (hP l) (hP m) (hCqhr t ht)
  have hb6 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_kl :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn m) (hnn r)
      (hKstar4 t ht) (hP h) (hP m) (hP r) (hCqkl t ht)
  have hb7 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_km :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn l) (hnn r)
      (hKstar4 t ht) (hP h) (hP l) (hP r) (hCqkm t ht)
  have hb8 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_kr :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn l) (hnn m)
      (hKstar4 t ht) (hP h) (hP l) (hP m) (hCqkr t ht)
  have hb9 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_lm :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn k) (hnn r)
      (hKstar4 t ht) (hP h) (hP k) (hP r) (hCqlm t ht)
  have hb10 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_lr :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn k) (hnn m)
      (hKstar4 t ht) (hP h) (hP k) (hP m) (hCqlr t ht)
  have hb11 : ‖D4 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qmr t)‖
      ≤ Kstar4 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_mr :=
    clmApply4_norm_le D4 _ _ _ _ hKstar40 (hnn h) (hnn k) (hnn l)
      (hKstar4 t ht) (hP h) (hP k) (hP l) (hCqmr t ht)
  have hb12 : ‖D3 (Φ t (expJetIota h)) (Qkl t) (Qmr t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * Cq_kl * Cq_mr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) hCqkl0
      (hKstar3 t ht) (hP h) (hCqkl t ht) (hCqmr t ht)
  have hb13 : ‖D3 (Φ t (expJetIota h)) (Qkm t) (Qlr t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * Cq_km * Cq_lr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) hCqkm0
      (hKstar3 t ht) (hP h) (hCqkm t ht) (hCqlr t ht)
  have hb14 : ‖D3 (Φ t (expJetIota h)) (Qkr t) (Qlm t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * Cq_kr * Cq_lm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) hCqkr0
      (hKstar3 t ht) (hP h) (hCqkr t ht) (hCqlm t ht)
  have hb15 : ‖D3 (Φ t (expJetIota k)) (Qhl t) (Qmr t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * Cq_hl * Cq_mr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) hCqhl0
      (hKstar3 t ht) (hP k) (hCqhl t ht) (hCqmr t ht)
  have hb16 : ‖D3 (Φ t (expJetIota k)) (Qhm t) (Qlr t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * Cq_hm * Cq_lr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) hCqhm0
      (hKstar3 t ht) (hP k) (hCqhm t ht) (hCqlr t ht)
  have hb17 : ‖D3 (Φ t (expJetIota k)) (Qhr t) (Qlm t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * Cq_hr * Cq_lm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) hCqhr0
      (hKstar3 t ht) (hP k) (hCqhr t ht) (hCqlm t ht)
  have hb18 : ‖D3 (Φ t (expJetIota l)) (Qhk t) (Qmr t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * Cq_hk * Cq_mr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) hCqhk0
      (hKstar3 t ht) (hP l) (hCqhk t ht) (hCqmr t ht)
  have hb19 : ‖D3 (Φ t (expJetIota l)) (Qhm t) (Qkr t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * Cq_hm * Cq_kr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) hCqhm0
      (hKstar3 t ht) (hP l) (hCqhm t ht) (hCqkr t ht)
  have hb20 : ‖D3 (Φ t (expJetIota l)) (Qhr t) (Qkm t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * Cq_hr * Cq_km :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) hCqhr0
      (hKstar3 t ht) (hP l) (hCqhr t ht) (hCqkm t ht)
  have hb21 : ‖D3 (Φ t (expJetIota m)) (Qhk t) (Qlr t)‖
      ≤ Kstar3 * (Cphi * ‖m‖) * Cq_hk * Cq_lr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn m) hCqhk0
      (hKstar3 t ht) (hP m) (hCqhk t ht) (hCqlr t ht)
  have hb22 : ‖D3 (Φ t (expJetIota m)) (Qhl t) (Qkr t)‖
      ≤ Kstar3 * (Cphi * ‖m‖) * Cq_hl * Cq_kr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn m) hCqhl0
      (hKstar3 t ht) (hP m) (hCqhl t ht) (hCqkr t ht)
  have hb23 : ‖D3 (Φ t (expJetIota m)) (Qhr t) (Qkl t)‖
      ≤ Kstar3 * (Cphi * ‖m‖) * Cq_hr * Cq_kl :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn m) hCqhr0
      (hKstar3 t ht) (hP m) (hCqhr t ht) (hCqkl t ht)
  have hb24 : ‖D3 (Φ t (expJetIota r)) (Qhk t) (Qlm t)‖
      ≤ Kstar3 * (Cphi * ‖r‖) * Cq_hk * Cq_lm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn r) hCqhk0
      (hKstar3 t ht) (hP r) (hCqhk t ht) (hCqlm t ht)
  have hb25 : ‖D3 (Φ t (expJetIota r)) (Qhl t) (Qkm t)‖
      ≤ Kstar3 * (Cphi * ‖r‖) * Cq_hl * Cq_km :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn r) hCqhl0
      (hKstar3 t ht) (hP r) (hCqhl t ht) (hCqkm t ht)
  have hb26 : ‖D3 (Φ t (expJetIota r)) (Qhm t) (Qkl t)‖
      ≤ Kstar3 * (Cphi * ‖r‖) * Cq_hm * Cq_kl :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn r) hCqhm0
      (hKstar3 t ht) (hP r) (hCqhm t ht) (hCqkl t ht)
  have hb27 : ‖D3 (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t)‖
      ≤ Kstar3 * (Cphi * ‖m‖) * (Cphi * ‖r‖) * Cq_hkl :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn m) (hnn r)
      (hKstar3 t ht) (hP m) (hP r) (hCqhkl t ht)
  have hb28 : ‖D3 (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖r‖) * Cq_hkm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) (hnn r)
      (hKstar3 t ht) (hP l) (hP r) (hCqhkm t ht)
  have hb29 : ‖D3 (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhkr t)‖
      ≤ Kstar3 * (Cphi * ‖l‖) * (Cphi * ‖m‖) * Cq_hkr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn l) (hnn m)
      (hKstar3 t ht) (hP l) (hP m) (hCqhkr t ht)
  have hb30 : ‖D3 (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖r‖) * Cq_hlm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) (hnn r)
      (hKstar3 t ht) (hP k) (hP r) (hCqhlm t ht)
  have hb31 : ‖D3 (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhlr t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖m‖) * Cq_hlr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) (hnn m)
      (hKstar3 t ht) (hP k) (hP m) (hCqhlr t ht)
  have hb32 : ‖D3 (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhmr t)‖
      ≤ Kstar3 * (Cphi * ‖k‖) * (Cphi * ‖l‖) * Cq_hmr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn k) (hnn l)
      (hKstar3 t ht) (hP k) (hP l) (hCqhmr t ht)
  have hb33 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖r‖) * Cq_klm :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn r)
      (hKstar3 t ht) (hP h) (hP r) (hCqklm t ht)
  have hb34 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qklr t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖m‖) * Cq_klr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn m)
      (hKstar3 t ht) (hP h) (hP m) (hCqklr t ht)
  have hb35 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkmr t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖l‖) * Cq_kmr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn l)
      (hKstar3 t ht) (hP h) (hP l) (hCqkmr t ht)
  have hb36 : ‖D3 (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlmr t)‖
      ≤ Kstar3 * (Cphi * ‖h‖) * (Cphi * ‖k‖) * Cq_lmr :=
    clmApply3_norm_le D3 _ _ _ hKstar30 (hnn h) (hnn k)
      (hKstar3 t ht) (hP h) (hP k) (hCqlmr t ht)
  have hb37 : ‖D2 (Qhkl t) (Qmr t)‖
      ≤ Kstar2 * Cq_hkl * Cq_mr :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhkl0
      (hKstar2 t ht) (hCqhkl t ht) (hCqmr t ht)
  have hb38 : ‖D2 (Qhkm t) (Qlr t)‖
      ≤ Kstar2 * Cq_hkm * Cq_lr :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhkm0
      (hKstar2 t ht) (hCqhkm t ht) (hCqlr t ht)
  have hb39 : ‖D2 (Qhkr t) (Qlm t)‖
      ≤ Kstar2 * Cq_hkr * Cq_lm :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhkr0
      (hKstar2 t ht) (hCqhkr t ht) (hCqlm t ht)
  have hb40 : ‖D2 (Qhlm t) (Qkr t)‖
      ≤ Kstar2 * Cq_hlm * Cq_kr :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhlm0
      (hKstar2 t ht) (hCqhlm t ht) (hCqkr t ht)
  have hb41 : ‖D2 (Qhlr t) (Qkm t)‖
      ≤ Kstar2 * Cq_hlr * Cq_km :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhlr0
      (hKstar2 t ht) (hCqhlr t ht) (hCqkm t ht)
  have hb42 : ‖D2 (Qhmr t) (Qkl t)‖
      ≤ Kstar2 * Cq_hmr * Cq_kl :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqhmr0
      (hKstar2 t ht) (hCqhmr t ht) (hCqkl t ht)
  have hb43 : ‖D2 (Qklm t) (Qhr t)‖
      ≤ Kstar2 * Cq_klm * Cq_hr :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqklm0
      (hKstar2 t ht) (hCqklm t ht) (hCqhr t ht)
  have hb44 : ‖D2 (Qklr t) (Qhm t)‖
      ≤ Kstar2 * Cq_klr * Cq_hm :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqklr0
      (hKstar2 t ht) (hCqklr t ht) (hCqhm t ht)
  have hb45 : ‖D2 (Qkmr t) (Qhl t)‖
      ≤ Kstar2 * Cq_kmr * Cq_hl :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqkmr0
      (hKstar2 t ht) (hCqkmr t ht) (hCqhl t ht)
  have hb46 : ‖D2 (Qlmr t) (Qhk t)‖
      ≤ Kstar2 * Cq_lmr * Cq_hk :=
    clmApply2_norm_le D2 _ _ hKstar20 hCqlmr0
      (hKstar2 t ht) (hCqlmr t ht) (hCqhk t ht)
  have hb47 : ‖D2 (Φ t (expJetIota h)) (Qklmr t)‖
      ≤ Kstar2 * (Cphi * ‖h‖) * Cq_klmr :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn h)
      (hKstar2 t ht) (hP h) (hCqklmr t ht)
  have hb48 : ‖D2 (Φ t (expJetIota k)) (Qhlmr t)‖
      ≤ Kstar2 * (Cphi * ‖k‖) * Cq_hlmr :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn k)
      (hKstar2 t ht) (hP k) (hCqhlmr t ht)
  have hb49 : ‖D2 (Φ t (expJetIota l)) (Qhkmr t)‖
      ≤ Kstar2 * (Cphi * ‖l‖) * Cq_hkmr :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn l)
      (hKstar2 t ht) (hP l) (hCqhkmr t ht)
  have hb50 : ‖D2 (Φ t (expJetIota m)) (Qhklr t)‖
      ≤ Kstar2 * (Cphi * ‖m‖) * Cq_hklr :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn m)
      (hKstar2 t ht) (hP m) (hCqhklr t ht)
  have hb51 : ‖D2 (Φ t (expJetIota r)) (Qhklm t)‖
      ≤ Kstar2 * (Cphi * ‖r‖) * Cq_hklm :=
    clmApply2_norm_le D2 _ _ hKstar20 (hnn r)
      (hKstar2 t ht) (hP r) (hCqhklm t ht)
  -- triangle inequality, sequentially (left-assoc partial sums).
  have hs2 := (norm_add_le _ _).trans (add_le_add hb1 hb2)
  have hs3 := (norm_add_le _ _).trans (add_le_add hs2 hb3)
  have hs4 := (norm_add_le _ _).trans (add_le_add hs3 hb4)
  have hs5 := (norm_add_le _ _).trans (add_le_add hs4 hb5)
  have hs6 := (norm_add_le _ _).trans (add_le_add hs5 hb6)
  have hs7 := (norm_add_le _ _).trans (add_le_add hs6 hb7)
  have hs8 := (norm_add_le _ _).trans (add_le_add hs7 hb8)
  have hs9 := (norm_add_le _ _).trans (add_le_add hs8 hb9)
  have hs10 := (norm_add_le _ _).trans (add_le_add hs9 hb10)
  have hs11 := (norm_add_le _ _).trans (add_le_add hs10 hb11)
  have hs12 := (norm_add_le _ _).trans (add_le_add hs11 hb12)
  have hs13 := (norm_add_le _ _).trans (add_le_add hs12 hb13)
  have hs14 := (norm_add_le _ _).trans (add_le_add hs13 hb14)
  have hs15 := (norm_add_le _ _).trans (add_le_add hs14 hb15)
  have hs16 := (norm_add_le _ _).trans (add_le_add hs15 hb16)
  have hs17 := (norm_add_le _ _).trans (add_le_add hs16 hb17)
  have hs18 := (norm_add_le _ _).trans (add_le_add hs17 hb18)
  have hs19 := (norm_add_le _ _).trans (add_le_add hs18 hb19)
  have hs20 := (norm_add_le _ _).trans (add_le_add hs19 hb20)
  have hs21 := (norm_add_le _ _).trans (add_le_add hs20 hb21)
  have hs22 := (norm_add_le _ _).trans (add_le_add hs21 hb22)
  have hs23 := (norm_add_le _ _).trans (add_le_add hs22 hb23)
  have hs24 := (norm_add_le _ _).trans (add_le_add hs23 hb24)
  have hs25 := (norm_add_le _ _).trans (add_le_add hs24 hb25)
  have hs26 := (norm_add_le _ _).trans (add_le_add hs25 hb26)
  have hs27 := (norm_add_le _ _).trans (add_le_add hs26 hb27)
  have hs28 := (norm_add_le _ _).trans (add_le_add hs27 hb28)
  have hs29 := (norm_add_le _ _).trans (add_le_add hs28 hb29)
  have hs30 := (norm_add_le _ _).trans (add_le_add hs29 hb30)
  have hs31 := (norm_add_le _ _).trans (add_le_add hs30 hb31)
  have hs32 := (norm_add_le _ _).trans (add_le_add hs31 hb32)
  have hs33 := (norm_add_le _ _).trans (add_le_add hs32 hb33)
  have hs34 := (norm_add_le _ _).trans (add_le_add hs33 hb34)
  have hs35 := (norm_add_le _ _).trans (add_le_add hs34 hb35)
  have hs36 := (norm_add_le _ _).trans (add_le_add hs35 hb36)
  have hs37 := (norm_add_le _ _).trans (add_le_add hs36 hb37)
  have hs38 := (norm_add_le _ _).trans (add_le_add hs37 hb38)
  have hs39 := (norm_add_le _ _).trans (add_le_add hs38 hb39)
  have hs40 := (norm_add_le _ _).trans (add_le_add hs39 hb40)
  have hs41 := (norm_add_le _ _).trans (add_le_add hs40 hb41)
  have hs42 := (norm_add_le _ _).trans (add_le_add hs41 hb42)
  have hs43 := (norm_add_le _ _).trans (add_le_add hs42 hb43)
  have hs44 := (norm_add_le _ _).trans (add_le_add hs43 hb44)
  have hs45 := (norm_add_le _ _).trans (add_le_add hs44 hb45)
  have hs46 := (norm_add_le _ _).trans (add_le_add hs45 hb46)
  have hs47 := (norm_add_le _ _).trans (add_le_add hs46 hb47)
  have hs48 := (norm_add_le _ _).trans (add_le_add hs47 hb48)
  have hs49 := (norm_add_le _ _).trans (add_le_add hs48 hb49)
  have hs50 := (norm_add_le _ _).trans (add_le_add hs49 hb50)
  have hs51 := (norm_add_le _ _).trans (add_le_add hs50 hb51)
  rw [expJet5Rhs_apply, ← hD5, ← hD4, ← hD3, ← hD2]
  exact hs51

/-! ### §3. The order-5 compactness clones (tube bound + Lipschitz) -/

/-- **`D⁵F` is uniformly tube-bounded on `[0,1]`.**  Mirror of
    `expJet_fderiv4_tube_bddAbove_unif` one order up: `q ↦ ‖D⁵F q‖` is continuous
    (`contDiff_fderiv4_geodesicField.continuous_fderiv`), the confined tube ball is compact, so
    a single `Kstar5` dominates `‖D⁵F(Y_v t)‖` for all admissible `v` and `t ∈ [0,1]`. -/
theorem expJet_fderiv5_tube_bddAbove_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧ ∀ v : Point n, ‖v‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  have hdFcont : Continuous
      (fun q => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) q‖) :=
    ((contDiff_fderiv4_geodesicField g gi hC).continuous_fderiv (by simp)).norm
  obtain ⟨C, hC'⟩ :=
    (isCompact_closedBall ((p, 0) : Point n × Point n) Rb).exists_bound_of_continuousOn
      hdFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v hv t ht => ?_⟩
  have hmem : expTube g gi hC p v t ∈ Metric.closedBall ((p, 0) : Point n × Point n) Rb := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    obtain ⟨_, _, hconf⟩ := expTube_spec g gi hC p v hv
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconf t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  have hbnd := hC' _ hmem
  refine le_trans (le_trans (le_abs_self _) ?_) (le_max_left C 0)
  simpa using hbnd

/-- **`D⁵F` is Lipschitz on the confined tube ball.**  Mirror of
    `expJet_fderiv4_lipschitzOnWith` one order up: `D⁵F` is `C^∞`
    (`contDiff_fderiv5_geodesicField`, banked in phase 1), hence `C¹`, and the tube ball is
    compact and convex; a `C¹` map is Lipschitz on a compact convex set
    (`ContDiffOn.exists_lipschitzOnWith`).  The `hLipD5F` datum of the J5-3 crux. -/
theorem expJet_fderiv5_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Ld5f : NNReal, LipschitzOnWith Ld5f
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) :=
  ((contDiff_fderiv5_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-! ### §4. The `[0,1]` global fundamental-solution existence (the glue mirror) -/

/-- **Continuity of the Jet₅ inhomogeneous field** `s ↦ DF(Y_v s)(R s) + Θ₅^{hklmr}(s)` on any
    `A ⊆ [0,1]` where `R` is continuous.  Direct mirror of `expJet4Field_continuousOn`, source
    continuity via `expJet5Rhs_continuousOn`. -/
theorem expJet5Field_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1)) (h k l m r : Point n)
    {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1)
    {R : ℝ → (Point n × Point n)} (hR : ContinuousOn R A) :
    ContinuousOn (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
      + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) A := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) A :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hA
  have h1 : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)) A :=
    hDFtube.clm_apply hR
  have h2 : ContinuousOn
      (fun s => expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) A :=
    (expJet5Rhs_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
      hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).mono hA
  exact h1.add h2

set_option maxHeartbeats 4000000 in
/-- **R4-fund SHIFTED — the shifted Jet₅ fourth-variation solver from arbitrary vector IC `x₀`.**
    Direct mirror of `expJet4Fund_shifted`: the vector-normed `IsPicardLindelof` instantiation of
    `F₅ t R := DF(Y_v t)(R) + Θ₅^{hklmr}(t)` centred at `x₀` on `closedBall(x₀, a)` with the same
    linear-in-`x₀` radius `a := 2·(KdF·‖x₀‖·T + Cθ·T) + 1`.  The reusable brick of the `[0,1]`
    concatenation. -/
theorem expJet5Fund_shifted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1)) (h k l m r : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          (Set.Icc t₀ (t₀ + T)) t := by
  -- `Θ₅^{hklmr}` is continuous on the compact `[0,1]`, hence uniformly bounded by some `Cθ ≥ 0`.
  have hΘcont : ContinuousOn
      (fun t => expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
      (Set.Icc (0 : ℝ) 1) :=
    expJet5Rhs_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
      hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
  obtain ⟨Cθ0, hCθ0⟩ := isCompact_Icc.exists_bound_of_continuousOn hΘcont
  set Cθ : ℝ := max Cθ0 0 with hCθdef
  have hCθnn : 0 ≤ Cθ := le_max_right _ _
  have hCθ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖ ≤ Cθ :=
    fun t ht => (hCθ0 t ht).trans (le_max_left _ _)
  -- the affine vector field `F₅ t R = DF(Y_v t)(R) + Θ₅^{hklmr}(t)`.
  set F₅ : ℝ → (Point n × Point n) → (Point n × Point n) :=
    fun t R => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) R
      + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t with hF₅
  have hTnn : 0 ≤ T := hT.le
  -- ball radius (linear in `x₀`, chosen so the affine a-priori bound closes for ANY `x₀`).
  set aval : ℝ := 2 * (KdF * ‖x₀‖ * T + Cθ * T) + 1 with haval
  have haval0 : 0 ≤ aval := by
    rw [haval]
    have h1 : 0 ≤ KdF * ‖x₀‖ * T := mul_nonneg (mul_nonneg hKdF0 (norm_nonneg _)) hTnn
    have h2 : 0 ≤ Cθ * T := mul_nonneg hCθnn hTnn
    linarith
  set Lval : ℝ := KdF * (‖x₀‖ + aval) + Cθ with hLval
  have hLval0 : 0 ≤ Lval := by
    rw [hLval]
    have hm : 0 ≤ KdF * (‖x₀‖ + aval) :=
      mul_nonneg hKdF0 (add_nonneg (norm_nonneg _) haval0)
    linarith
  set Ann : NNReal := ⟨aval, haval0⟩ with hAnndef
  set Lnn : NNReal := ⟨Lval, hLval0⟩ with hLnndef
  set Knn : NNReal := ⟨KdF, hKdF0⟩ with hKnn
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  -- the interval constraint `L·T ≤ a`.
  have hKT : KdF * T ≤ 1 / 2 := by linarith
  have hstepPL : Lval * T ≤ aval := by
    have key : aval * (KdF * T) ≤ aval * (1 / 2) := mul_le_mul_of_nonneg_left hKT haval0
    have hLvalT : Lval * T = KdF * ‖x₀‖ * T + KdF * aval * T + Cθ * T := by rw [hLval]; ring
    rw [hLvalT]
    nlinarith [key, haval, haval0]
  -- `DF(Y_v ·)` continuous on `[0,1]`.
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) :=
    hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  -- assemble `IsPicardLindelof` for the affine field on `[t₀, t₀+T]`, centred at `x₀`.
  have hpl : IsPicardLindelof F₅
      (tmin := t₀) (tmax := t₀ + T) ⟨t₀, ⟨le_refl t₀, by linarith⟩⟩
      x₀ Ann 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `R` with constant `KdF` (source drops out).
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      have hsub : F₅ t M - F₅ t N
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N) := by
        simp only [hF₅, map_sub]; abel
      rw [hsub]
      calc ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (M - N)‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm _
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `R`.
      intro x _
      have h1 : ContinuousOn
          (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x)
          (Set.Icc (0 : ℝ) 1) := hDFtube.clm_apply continuousOn_const
      exact ((h1.add hΘcont).mono hIccsub)
    · -- uniform bound `‖F₅ t x‖ ≤ L` on `closedBall(x₀, a)`.
      intro t ht x hx
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hd : ‖x - x₀‖ ≤ aval := by
        have h' := Metric.mem_closedBall.mp hx
        rw [dist_eq_norm] at h'
        exact h'
      have hxx : (x - x₀) + x₀ = x := by abel
      have hxnorm : ‖x‖ ≤ ‖x₀‖ + aval := by
        calc ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [hxx]
          _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ ≤ aval + ‖x₀‖ := by linarith
          _ = ‖x₀‖ + aval := by ring
      show ‖F₅ t x‖ ≤ Lval
      calc ‖F₅ t x‖
          = ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖ := by
            rw [hF₅]
        _ ≤ ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) x‖
              + ‖expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t‖ :=
            norm_add_le _ _
        _ ≤ KdF * ‖x‖ + Cθ :=
            add_le_add
              (le_trans
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).le_opNorm x)
                (mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)))
              (hCθ t htIcc)
        _ ≤ Lval := by
            rw [hLval]
            have hmul : KdF * ‖x‖ ≤ KdF * (‖x₀‖ + aval) :=
              mul_le_mul_of_nonneg_left hxnorm hKdF0
            linarith
    · -- the interval constraint `L · max(T, 0) ≤ a`.
      show (Lnn : ℝ) * max ((t₀ + T) - ((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ :
              Set.Icc t₀ (t₀ + T)) : ℝ))
          (((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ : Set.Icc t₀ (t₀ + T)) : ℝ) - t₀)
            ≤ (Ann : ℝ) - ((0 : NNReal) : ℝ)
      rw [NNReal.coe_zero, sub_zero]
      show Lval * max ((t₀ + T) - t₀) (t₀ - t₀) ≤ aval
      rw [sub_self, show (t₀ + T) - t₀ = T from by ring, max_eq_left hT.le]
      exact hstepPL
  obtain ⟨R, hR0, hRd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨R, hR0, fun t ht => ?_⟩
  have hd := hRd t ht
  simpa only [hF₅] using hd

set_option maxHeartbeats 4000000 in
/-- **R4-fund SHIFTED-INTEGRAL — the shifted Jet₅ solver in INTEGRAL form (the gluing brick).**
    Direct mirror of `expJet4Fund_shifted_integral`: additionally packages the LOCAL INTEGRAL
    EQUATION `R(t) = x₀ + ∫_{t₀}^t (DF(Y_v s)(R s) + Θ₅^{hklmr}(s)) ds` via FTC-2.  Since the source is
    GLOBAL, the `[0,1]` concatenation glues these directly by ENDPOINT VALUE — no right-composition. -/
theorem expJet5Fund_shifted_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1)) (h k l m r : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1) (hstep : 2 * KdF * T ≤ 1)
    (x₀ : Point n × Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R t₀ = x₀ ∧
      ContinuousOn R (Set.Icc t₀ (t₀ + T)) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          (Set.Icc t₀ (t₀ + T)) t) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        R t = x₀ + ∫ s in t₀..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)) := by
  obtain ⟨R, hR0, hRd⟩ :=
    expJet5Fund_shifted g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont
      hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
      KdF hKdF0 hKdF t₀ T ht₀ hT hsum hstep x₀
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hRcont : ContinuousOn R (Set.Icc t₀ (t₀ + T)) := fun s hs => (hRd s hs).continuousWithinAt
  have hintegrand : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
      (Set.Icc t₀ (t₀ + T)) :=
    expJet5Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
      hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r hIccsub hRcont
  refine ⟨R, hR0, hRcont, hRd, fun t ht => ?_⟩
  have hab : t₀ ≤ t := ht.1
  have hsubt : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := Set.Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn R (Set.Icc t₀ t) := hRcont.mono hsubt
  have hderiv : ∀ x ∈ Set.Ioo t₀ t,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)) (R x)
           + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r x)
        (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc t₀ (t₀ + T) := hsubt ⟨hx.1.le, hx.2.le⟩
    have hnhds : Set.Icc t₀ (t₀ + T) ∈ nhds x :=
      Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
    exact ((hRd x hxIcc).hasDerivAt hnhds).hasDerivWithinAt
  have hint : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
      MeasureTheory.volume t₀ t :=
    (hintegrand.mono hsubt).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  rw [hR0] at hftc
  rw [hftc]; abel

set_option maxHeartbeats 8000000 in
/-- **The partition induction (endpoint-matching concatenation) for the Jet₅ solver.**  Direct mirror
    of `expJet4Fund_glue`: for every `j ≤ N` builds a curve `R` on `[0, j/N]` with `R 0 = 0`,
    continuous, obeying the GLOBAL integral equation
    `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₅^{hklmr}(s)) ds`, by induction gluing `R_j` and the shifted
    solver `U` at the endpoint value `R_j(j/N)`; the global source pastes directly. -/
private theorem expJet5Fund_glue (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1)) (h k l m r : Point n)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (N : ℕ) (hN0 : 0 < N) (hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1) :
    ∀ j : ℕ, j ≤ N →
      ∃ R : ℝ → (Point n × Point n),
        R 0 = 0 ∧
        ContinuousOn R (Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ))) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ)),
          R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
            ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
               + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => (0 : Point n × Point n), rfl, continuousOn_const, ?_⟩
    intro t ht
    have h0 : ((0 : ℕ) : ℝ) / (N : ℝ) = 0 := by rw [Nat.cast_zero, zero_div]
    rw [h0] at ht
    have htz : t = 0 := le_antisymm ht.2 ht.1
    subst htz
    simp only [intervalIntegral.integral_same, add_zero]
  | succ M ih =>
    intro hk
    obtain ⟨Rj, hRj0, hRjcont, hRjint⟩ := ih (Nat.le_of_succ_le hk)
    have hτnn : 0 ≤ (M : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg M) hNpos.le
    have hInpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hsucc : ((M + 1 : ℕ) : ℝ) / (N : ℝ) = (M : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      push_cast; ring
    have hτm1le1 : (M : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 :=
      hsucc ▸ (by rw [div_le_one hNpos]; exact_mod_cast hk)
    obtain ⟨U, hU0, hUcont, hUderiv, hUint⟩ :=
      expJet5Fund_shifted_integral g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv
        hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
        KdF hKdF0 hKdF
        ((M : ℝ) / (N : ℝ)) (1 / (N : ℝ)) hτnn hInpos hτm1le1 hstep (Rj ((M : ℝ) / (N : ℝ)))
    set R' : ℝ → (Point n × Point n) :=
      fun t => if t ≤ (M : ℝ) / (N : ℝ) then Rj t else U t with hR'def
    have hR'_lo : ∀ s, s ≤ (M : ℝ) / (N : ℝ) → R' s = Rj s := by
      intro s hs; rw [hR'def]; exact if_pos hs
    have hR'_hi : ∀ s, ¬ (s ≤ (M : ℝ) / (N : ℝ)) → R' s = U s := by
      intro s hs; rw [hR'def]; exact if_neg hs
    -- EqOn on the two closed pieces (junction value matches: `Rj(τ_M) = x₀ = U(τ_M)`).
    have hEqLo : Set.EqOn R' Rj (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ))) :=
      fun s hs => hR'_lo s hs.2
    have hEqHi : Set.EqOn R' U
        (Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      intro s hs
      by_cases hsle : s ≤ (M : ℝ) / (N : ℝ)
      · have hseq : s = (M : ℝ) / (N : ℝ) := le_antisymm hsle hs.1
        rw [hR'_lo s hsle, hseq, hU0]
      · rw [hR'_hi s hsle]
    -- continuity of the glued curve on [0, (M+1)/N].
    have hR'cont : ContinuousOn R' (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      have hunion : Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))
          = Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ))
            ∪ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
        (Set.Icc_union_Icc_eq_Icc hτnn (by linarith)).symm
      rw [hunion]
      exact (hRjcont.congr hEqLo).union_of_isClosed (hUcont.congr hEqHi)
        isClosed_Icc isClosed_Icc
    -- integrand continuity for interval integrability.
    have hcontψ' : ContinuousOn
        (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
          + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
        (Set.Icc (0 : ℝ) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      expJet5Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
        hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
        (Set.Icc_subset_Icc_right hτm1le1) hR'cont
    rw [hsucc]
    refine ⟨R', ?_, hR'cont, ?_⟩
    · rw [hR'_lo 0 hτnn]; exact hRj0
    · intro t ht
      by_cases htle : t ≤ (M : ℝ) / (N : ℝ)
      · -- t in [0, τM]: the curve is Rj there.
        rw [hR'_lo t htle]
        have hcong : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
            = ∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                 + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ht.1] at hs
          show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
            = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
          rw [hR'_lo s (le_trans hs.2 htle)]
        rw [hcong]
        exact hRjint t ⟨ht.1, htle⟩
      · -- t in (τM, τM + 1/N]: the curve is U there.
        have htlt : (M : ℝ) / (N : ℝ) < t := not_le.mp htle
        have htmem : t ∈ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
          ⟨htlt.le, ht.2⟩
        rw [hR'_hi t htle]
        have hII1 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
            MeasureTheory.volume 0 ((M : ℝ) / (N : ℝ)) :=
          (hcontψ'.mono (Set.Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hτnn
        have hII2 : IntervalIntegrable
            (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
            MeasureTheory.volume ((M : ℝ) / (N : ℝ)) t :=
          (hcontψ'.mono (Set.Icc_subset_Icc hτnn ht.2)).intervalIntegrable_of_Icc htlt.le
        have hsplit : (∫ s in (0 : ℝ)..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
            = (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
              + ∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) :=
          (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
        -- first piece = Rj(τM) - 0.
        have hI1 : (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
            = Rj ((M : ℝ) / (N : ℝ)) - (0 : Point n × Point n) := by
          have hc : (∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
              = ∫ s in (0 : ℝ)..((M : ℝ) / (N : ℝ)),
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hτnn] at hs
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Rj s)
                + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
            rw [hR'_lo s hs.2]
          rw [hc, hRjint ((M : ℝ) / (N : ℝ)) ⟨hτnn, le_refl _⟩]; abel
        -- second piece = U(t) - Rj(τM).
        have hI2 : (∫ s in ((M : ℝ) / (N : ℝ))..t,
              ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                 + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
            = U t - Rj ((M : ℝ) / (N : ℝ)) := by
          have hc : (∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s))
              = ∫ s in ((M : ℝ) / (N : ℝ))..t,
                ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                   + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le htlt.le] at hs
            have hsmem : s ∈ Set.Icc ((M : ℝ) / (N : ℝ)) ((M : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
              ⟨hs.1, le_trans hs.2 ht.2⟩
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R' s)
                + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
              = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (U s)
                + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s
            rw [hEqHi hsmem]
          rw [hc, hUint t htmem]; abel
        rw [hsplit, hI1, hI2]; abel

set_option maxHeartbeats 8000000 in
/-- **R4-fund CAPSTONE — the `[0,1]` Jet₅ fourth-variation fundamental solution `R^{hklmr}`.**  Direct
    mirror of `expJet4Fund`: for `‖v‖ ≤ expRho` and `Φ`/`Qhk … Qklm` continuous on `[0,1]`, there is a
    vector-valued curve `R : ℝ → Point n × Point n` with `R 0 = 0`, continuous on `[0,1]`, obeying the
    GLOBAL integral equation `R t = 0 + ∫₀ᵗ (DF(Y_v s)(R s) + Θ₅^{hklmr}(s)) ds`, and — by FTC-1 — the
    inhomogeneous Jet₅ derivative law `HasDerivWithinAt R (DF(Y_v t)(R t) + Θ₅^{hklmr}(t)) (Icc 0 1) t`
    for every `t ∈ [0,1]`.  Built by concatenating `N ≥ 2(KdF+1)` shifted solvers
    (`expJet5Fund_glue`).

    HONEST: the `[0,1]` inhomogeneous Jet₅ fourth-variation solution `R^{hklmr}` (the fourth-variation
    transport of `h, k, l, m` through `D⁴F`/`D³F`/`D²F`).  It does NOT instantiate `Φ`/`Q`, NOT close
    `ContDiff⁴ exp_p`, NOT the parameter-residual identity, NOT `κ = 1/6`, NOT numerical-`G`. -/
theorem expJet5Fund (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1)) (h k l m r : Point n) :
    ∃ R : ℝ → (Point n × Point n),
      R 0 = 0 ∧
      ContinuousOn R (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        R t = (0 : Point n × Point n) + ∫ s in (0 : ℝ)..t,
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt R
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          (Set.Icc (0 : ℝ) 1) t) := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (KdF + 1))
  have hpos : (0 : ℝ) < 2 * (KdF + 1) := by linarith
  have hNRpos : (0 : ℝ) < (N : ℝ) := hpos.trans_le hN
  have hN0 : 0 < N := by exact_mod_cast hNRpos
  have hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1 := by
    have h2 : 2 * KdF * (1 / (N : ℝ)) = (2 * KdF) / (N : ℝ) := by ring
    rw [h2, div_le_one hNRpos]; linarith [hN]
  obtain ⟨R, hR0, hRcont, hRint⟩ :=
    expJet5Fund_glue g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont
      hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
      KdF hKdF0 hKdF N hN0 hstep N le_rfl
  have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNRpos.ne'
  rw [hNN] at hRcont hRint
  refine ⟨R, hR0, hRcont, hRint, ?_⟩
  have hψcont : ContinuousOn
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
      (Set.Icc (0 : ℝ) 1) :=
    expJet5Field_continuousOn g gi hC p v hv Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
      hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r (subset_refl _) hRcont
  intro t ht
  have hII : IntervalIntegrable
      (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (R s)
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r s)
      MeasureTheory.volume 0 t :=
    (hψcont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
  have hmeas := hψcont.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
    measurableSet_Icc t
  have hFTC := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) 1)
    hII hmeas (hψcont t ht)
  have hconst := hFTC.const_add (0 : Point n × Point n)
  exact hconst.congr (fun s hs => hRint s hs) (hRint t ht)

/-! ### §5. Packaging: `IsExpJet5FundSol` is inhabited + non-vacuity gates -/

/-- **`IsExpJet5FundSol` is INHABITED** — the phase-1 fundamental-solution SHAPE has a witness:
    the four conjuncts of the `expJet5Fund` conclusion are literally the four conjuncts of the
    shape.  This is the phase-2 obligation the phase-1 firewall deferred. -/
theorem expJet5FundSol_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (h k l m r : Point n) :
    ∃ R : ℝ → (Point n × Point n),
      IsExpJet5FundSol g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r R := by
  obtain ⟨R, hR0, hRcont, hRint, hRderiv⟩ :=
    expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont
      hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
  exact ⟨R, hR0, hRcont, hRint, hRderiv⟩

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate (cp466 discipline): the D5 existence fires at the GENUINELY CURVED
    witness.**  At `g^κ = curvedRNCMetric (−1)` / `curvedRNCInv (−1)` (`hC` supplied by the
    banked `curvedRNC_hChr`), `p = v = 0` (`hv` from `expRho_pos`), and the zero abstract
    variations, EVERY antecedent of `expJet5FundSol_exists` is DISCHARGED and the conclusion is
    inhabited — the shape `IsExpJet5FundSol` is satisfiable at curved data, not vacuously
    quantified.  NOT `a₁ = R/6`. -/
theorem expJet5Fund_gate_curved (h k l m r : Point n) :
    ∃ R : ℝ → (Point n × Point n),
      IsExpJet5FundSol (curvedRNCMetric (-1)) (curvedRNCInv (-1))
        (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        h k l m r R :=
  expJet5FundSol_exists (curvedRNCMetric (-1)) (curvedRNCInv (-1))
    (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by simpa using (expRho_pos (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) 0).le)
    continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    h k l m r

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate for the 51-term bound: all antecedents discharged at the curved
    witness.**  The tube-bound antecedents `hKstar5/4/3/2` are supplied by the four `_unif`
    compactness lemmas at `g^κ = curvedRNCMetric (−1)`, `p = v = 0`; with the zero variations
    (`Cphi = Cq = 0`) the 51-term polynomial collapses and the bound yields
    `‖Θ₅(t)‖ ≤ 0` on `[0,1]` — the bound's hypothesis set is jointly satisfiable and the
    conclusion is consistent (the zero-variation source IS zero).  NOT `a₁ = R/6`. -/
theorem expJet5Rhs_norm_le_gate (h k l m r : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet5Rhs (curvedRNCMetric (-1)) (curvedRNCInv (-1))
        (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        h k l m r t‖ ≤ 0 := by
  intro t ht
  obtain ⟨K5, hK50, hK5⟩ := expJet_fderiv5_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1))
    (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K4, hK40, hK4⟩ := expJet_fderiv4_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1))
    (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K3, hK30, hK3⟩ := expJet_fderiv3_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1))
    (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨K2, hK20, hK2⟩ := expJet_fderiv2_tube_bddAbove_unif (n := n) (curvedRNCMetric (-1))
    (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  have hv : ‖(0 : Point n)‖ ≤ expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n) := by
    simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1))
      (curvedRNC_hChr (-1) (by norm_num)) 0).le
  have hb := expJet5Rhs_norm_le (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1))
    (curvedRNC_hChr (-1) (by norm_num)) 0 0 (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    h k l m r K5 K4 K3 K2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    hK50 hK40 hK30 hK20 le_rfl
    (fun s hs => hK5 0 hv s hs) (fun s hs => hK4 0 hv s hs)
    (fun s hs => hK3 0 hv s hs) (fun s hs => hK2 0 hv s hs)
    (fun s _ => by simp)
    (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp) (fun s _ => by simp)
    t ht
  simpa only [mul_zero, zero_mul, add_zero, zero_add] using hb

end QIQTH.ExpMap
