/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff3
import QIQTH.ExpJet4ValFull
import Mathlib

/-!
# JET-5 telescope family file A (J4-649): generic multilinear peel bounds + `expJet5VtpConst`

Brick **J4-649** of the JET-5 campaign toward the truly-unconditional `a₁ = R/6`
(`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`), split architecture, family file A.

The 202-sub-term `ρ₅`-telescope of the order-5 two-point crux `expJet5Val_v_two_pt_diff`
(assembled in `ExpJet5Phase5.lean`) factors through FOUR generic "peel" bounds — one per
multilinear arity occurring in the 51-term source `Θ₅^{hklmr}` (`expJet5Rhs`):

* `expJet5TelePeel2` — bilinear peel (3 sub-terms); consumed by the 10 `D²F(q³,q²)` and the
  5 `D²F(Φι·, q⁴)` difference blocks;
* `expJet5TelePeel3` — trilinear peel (4 sub-terms); consumed by the 15 `D³F(Φι·, q², q²)`
  and the 10 `D³F(Φι·, Φι·, q³)` blocks;
* `expJet5TelePeel4` — quadrilinear peel (5 sub-terms); consumed by the 10
  `D⁴F(Φι·,Φι·,Φι·, q²)` blocks;
* `expJet5TelePeel5` — quintilinear peel (6 sub-terms); consumed by the single
  `D⁵F(Φι·)⁵` block.

Sub-term count: `1·6 + 10·5 + (15+10)·4 + (10+5)·3 = 201`, plus the leading
`[DF(Y_v)−DF(Y_w)](R_w)` Lipschitz term `= 202`.

Also here: the aggregate constant `expJet5VtpConst` (the assembled Jet₅ two-point Lipschitz
constant) and its nonnegativity.

## Honest firewall (binding)

This file is pure normed-space combinatorics: NO geometry is proved here.  It does NOT
establish `exp_p ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`; `a₁ = R/6`
remains CONDITIONAL (flat tower non-vacuous; curved owes the Jet-5 completion + the Duhamel
carry + fat-K carriers + capstone co-instantiation).
-/

namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 400000

/-! ### Local private copies of the multilinear CLM-application norm bounds
(the `ExpJet4ValFull` originals are `private`), extended to arity 5 -/

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

private theorem clmApply5_norm_le {E F G H I J : Type*}
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

/-! ### Generic multilinear-difference telescoping identities (arities 2–5) -/

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

private theorem clm5_diff_eq {E F G H I J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup J] [NormedSpace ℝ J]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I →L[ℝ] J) (a : E) (b : F) (c : G) (d : H) (e : I)
    (a' : E) (b' : F) (c' : G) (d' : H) (e' : I) :
    B a b c d e - B' a' b' c' d' e'
      = B (a - a') b c d e + B a' (b - b') c d e + B a' b' (c - c') d e
        + B a' b' c' (d - d') e + B a' b' c' d' (e - e') + (B - B') a' b' c' d' e' := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]; abel

/-! ### The four generic peel bounds -/

/-- **Bilinear peel bound** (3 sub-terms): the family lemma behind the `D²F(q³,q²)` and
    `D²F(Φι·,q⁴)` difference blocks of the `ρ₅`-telescope. -/
theorem expJet5TelePeel2 {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B B' : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) (a' : E) (b' : F)
    {KB LB Na Nb da db : ℝ}
    (hKB : 0 ≤ KB) (hLB : 0 ≤ LB) (hNa : 0 ≤ Na) (hda0 : 0 ≤ da)
    (hB : ‖B‖ ≤ KB) (hBd : ‖B - B'‖ ≤ LB)
    (ha : ‖a‖ ≤ Na) (ha' : ‖a'‖ ≤ Na) (hb : ‖b‖ ≤ Nb) (hb' : ‖b'‖ ≤ Nb)
    (hda : ‖a - a'‖ ≤ da) (hdb : ‖b - b'‖ ≤ db) :
    ‖B a b - B' a' b'‖ ≤ KB * da * Nb + KB * Na * db + LB * Na * Nb := by
  rw [clm2_diff_eq B B' a b a' b']
  have t1 : ‖B (a - a') b‖ ≤ KB * da * Nb :=
    clmApply2_norm_le B (a - a') b hKB hda0 hB hda hb
  have t2 : ‖B a' (b - b')‖ ≤ KB * Na * db :=
    clmApply2_norm_le B a' (b - b') hKB hNa hB ha' hdb
  have t3 : ‖(B - B') a' b'‖ ≤ LB * Na * Nb :=
    clmApply2_norm_le (B - B') a' b' hLB hNa hBd ha' hb'
  refine (norm_add_le _ _).trans (add_le_add ?_ t3)
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

/-- **Trilinear peel bound** (4 sub-terms): the family lemma behind the `D³F(Φι·,q²,q²)` and
    `D³F(Φι·,Φι·,q³)` difference blocks of the `ρ₅`-telescope. -/
theorem expJet5TelePeel3 {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) (a' : E) (b' : F) (c' : G)
    {KB LB Na Nb Nc da db dc : ℝ}
    (hKB : 0 ≤ KB) (hLB : 0 ≤ LB) (hNa : 0 ≤ Na) (hNb : 0 ≤ Nb) (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db)
    (hB : ‖B‖ ≤ KB) (hBd : ‖B - B'‖ ≤ LB)
    (ha : ‖a‖ ≤ Na) (ha' : ‖a'‖ ≤ Na) (hb : ‖b‖ ≤ Nb) (hb' : ‖b'‖ ≤ Nb)
    (hc : ‖c‖ ≤ Nc) (hc' : ‖c'‖ ≤ Nc)
    (hda : ‖a - a'‖ ≤ da) (hdb : ‖b - b'‖ ≤ db) (hdc : ‖c - c'‖ ≤ dc) :
    ‖B a b c - B' a' b' c'‖
      ≤ KB * da * Nb * Nc + KB * Na * db * Nc + KB * Na * Nb * dc + LB * Na * Nb * Nc := by
  rw [clm3_diff_eq B B' a b c a' b' c']
  have t1 : ‖B (a - a') b c‖ ≤ KB * da * Nb * Nc :=
    clmApply3_norm_le B (a - a') b c hKB hda0 hNb hB hda hb hc
  have t2 : ‖B a' (b - b') c‖ ≤ KB * Na * db * Nc :=
    clmApply3_norm_le B a' (b - b') c hKB hNa hdb0 hB ha' hdb hc
  have t3 : ‖B a' b' (c - c')‖ ≤ KB * Na * Nb * dc :=
    clmApply3_norm_le B a' b' (c - c') hKB hNa hNb hB ha' hb' hdc
  have t4 : ‖(B - B') a' b' c'‖ ≤ LB * Na * Nb * Nc :=
    clmApply3_norm_le (B - B') a' b' c' hLB hNa hNb hBd ha' hb' hc'
  refine (norm_add_le _ _).trans (add_le_add ?_ t4)
  refine (norm_add_le _ _).trans (add_le_add ?_ t3)
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

/-- **Quadrilinear peel bound** (5 sub-terms): the family lemma behind the
    `D⁴F(Φι·,Φι·,Φι·,q²)` difference blocks of the `ρ₅`-telescope. -/
theorem expJet5TelePeel4 {E F G H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I) (a : E) (b : F) (c : G) (d : H)
    (a' : E) (b' : F) (c' : G) (d' : H)
    {KB LB Na Nb Nc Nd da db dc dd : ℝ}
    (hKB : 0 ≤ KB) (hLB : 0 ≤ LB) (hNa : 0 ≤ Na) (hNb : 0 ≤ Nb) (hNc : 0 ≤ Nc)
    (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) (hdc0 : 0 ≤ dc)
    (hB : ‖B‖ ≤ KB) (hBd : ‖B - B'‖ ≤ LB)
    (ha : ‖a‖ ≤ Na) (ha' : ‖a'‖ ≤ Na) (hb : ‖b‖ ≤ Nb) (hb' : ‖b'‖ ≤ Nb)
    (hc : ‖c‖ ≤ Nc) (hc' : ‖c'‖ ≤ Nc) (hd : ‖d‖ ≤ Nd) (hd' : ‖d'‖ ≤ Nd)
    (hda : ‖a - a'‖ ≤ da) (hdb : ‖b - b'‖ ≤ db) (hdc : ‖c - c'‖ ≤ dc) (hdd : ‖d - d'‖ ≤ dd) :
    ‖B a b c d - B' a' b' c' d'‖
      ≤ KB * da * Nb * Nc * Nd + KB * Na * db * Nc * Nd + KB * Na * Nb * dc * Nd
        + KB * Na * Nb * Nc * dd + LB * Na * Nb * Nc * Nd := by
  rw [clm4_diff_eq B B' a b c d a' b' c' d']
  have t1 : ‖B (a - a') b c d‖ ≤ KB * da * Nb * Nc * Nd :=
    clmApply4_norm_le B (a - a') b c d hKB hda0 hNb hNc hB hda hb hc hd
  have t2 : ‖B a' (b - b') c d‖ ≤ KB * Na * db * Nc * Nd :=
    clmApply4_norm_le B a' (b - b') c d hKB hNa hdb0 hNc hB ha' hdb hc hd
  have t3 : ‖B a' b' (c - c') d‖ ≤ KB * Na * Nb * dc * Nd :=
    clmApply4_norm_le B a' b' (c - c') d hKB hNa hNb hdc0 hB ha' hb' hdc hd
  have t4 : ‖B a' b' c' (d - d')‖ ≤ KB * Na * Nb * Nc * dd :=
    clmApply4_norm_le B a' b' c' (d - d') hKB hNa hNb hNc hB ha' hb' hc' hdd
  have t5 : ‖(B - B') a' b' c' d'‖ ≤ LB * Na * Nb * Nc * Nd :=
    clmApply4_norm_le (B - B') a' b' c' d' hLB hNa hNb hNc hBd ha' hb' hc' hd'
  refine (norm_add_le _ _).trans (add_le_add ?_ t5)
  refine (norm_add_le _ _).trans (add_le_add ?_ t4)
  refine (norm_add_le _ _).trans (add_le_add ?_ t3)
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

/-- **Quintilinear peel bound** (6 sub-terms): the family lemma behind the single
    `D⁵F(Φι·)⁵` difference block of the `ρ₅`-telescope. -/
theorem expJet5TelePeel5 {E F G H I J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup J] [NormedSpace ℝ J]
    (B B' : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I →L[ℝ] J) (a : E) (b : F) (c : G) (d : H) (e : I)
    (a' : E) (b' : F) (c' : G) (d' : H) (e' : I)
    {KB LB Na Nb Nc Nd Ne da db dc dd de : ℝ}
    (hKB : 0 ≤ KB) (hLB : 0 ≤ LB) (hNa : 0 ≤ Na) (hNb : 0 ≤ Nb) (hNc : 0 ≤ Nc) (hNd : 0 ≤ Nd)
    (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) (hdc0 : 0 ≤ dc) (hdd0 : 0 ≤ dd)
    (hB : ‖B‖ ≤ KB) (hBd : ‖B - B'‖ ≤ LB)
    (ha : ‖a‖ ≤ Na) (ha' : ‖a'‖ ≤ Na) (hb : ‖b‖ ≤ Nb) (hb' : ‖b'‖ ≤ Nb)
    (hc : ‖c‖ ≤ Nc) (hc' : ‖c'‖ ≤ Nc) (hd : ‖d‖ ≤ Nd) (hd' : ‖d'‖ ≤ Nd)
    (he : ‖e‖ ≤ Ne) (he' : ‖e'‖ ≤ Ne)
    (hda : ‖a - a'‖ ≤ da) (hdb : ‖b - b'‖ ≤ db) (hdc : ‖c - c'‖ ≤ dc) (hdd : ‖d - d'‖ ≤ dd)
    (hde : ‖e - e'‖ ≤ de) :
    ‖B a b c d e - B' a' b' c' d' e'‖
      ≤ KB * da * Nb * Nc * Nd * Ne + KB * Na * db * Nc * Nd * Ne
        + KB * Na * Nb * dc * Nd * Ne + KB * Na * Nb * Nc * dd * Ne
        + KB * Na * Nb * Nc * Nd * de + LB * Na * Nb * Nc * Nd * Ne := by
  rw [clm5_diff_eq B B' a b c d e a' b' c' d' e']
  have t1 : ‖B (a - a') b c d e‖ ≤ KB * da * Nb * Nc * Nd * Ne :=
    clmApply5_norm_le B (a - a') b c d e hKB hda0 hNb hNc hNd hB hda hb hc hd he
  have t2 : ‖B a' (b - b') c d e‖ ≤ KB * Na * db * Nc * Nd * Ne :=
    clmApply5_norm_le B a' (b - b') c d e hKB hNa hdb0 hNc hNd hB ha' hdb hc hd he
  have t3 : ‖B a' b' (c - c') d e‖ ≤ KB * Na * Nb * dc * Nd * Ne :=
    clmApply5_norm_le B a' b' (c - c') d e hKB hNa hNb hdc0 hNd hB ha' hb' hdc hd he
  have t4 : ‖B a' b' c' (d - d') e‖ ≤ KB * Na * Nb * Nc * dd * Ne :=
    clmApply5_norm_le B a' b' c' (d - d') e hKB hNa hNb hNc hdd0 hB ha' hb' hc' hdd he
  have t5 : ‖B a' b' c' d' (e - e')‖ ≤ KB * Na * Nb * Nc * Nd * de :=
    clmApply5_norm_le B a' b' c' d' (e - e') hKB hNa hNb hNc hNd hB ha' hb' hc' hd' hde
  have t6 : ‖(B - B') a' b' c' d' e'‖ ≤ LB * Na * Nb * Nc * Nd * Ne :=
    clmApply5_norm_le (B - B') a' b' c' d' e' hLB hNa hNb hNc hNd hBd ha' hb' hc' hd' he'
  refine (norm_add_le _ _).trans (add_le_add ?_ t6)
  refine (norm_add_le _ _).trans (add_le_add ?_ t5)
  refine (norm_add_le _ _).trans (add_le_add ?_ t4)
  refine (norm_add_le _ _).trans (add_le_add ?_ t3)
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

/-! ### The aggregate `ρ₅`-telescope constant -/

/-- **The assembled Jet₅ two-point Lipschitz constant** for `v ↦ R⁵_v(1)` (the fifth
    derivative): the aggregate of the 202 `ρ₅`-telescope sub-term coefficients (grouped by
    block family, with multiplicities), times the outer Grönwall factor `e^{Kstar}`.
    Abbreviations (inlined): `E = e^{Kstar}`, `CΦd = Ldf·e^{Kf}·E²` (the propagator two-point
    constant), `B₂/B₃/B₄/B₅` the pair/triple/quadruple/quintuple value-bound constants, and
    `T₂/T₃/T₄ = expJet{2,3,4}VtpConst` the lower-order two-point constants. -/
noncomputable def expJet5VtpConst
    (Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ) : ℝ :=
  (Ldf * Real.exp Kf
      * ((Kstar5 * Real.exp Kstar ^ 5
          + 10 * (Kstar4 * Real.exp Kstar ^ 3 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          + 15 * (Kstar3 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2)
          + 10 * (Kstar3 * Real.exp Kstar ^ 2 * ((Kstar3 * Real.exp Kstar ^ 3
              + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
            * Real.exp Kstar))
          + 10 * (Kstar2 * ((Kstar3 * Real.exp Kstar ^ 3
              + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
            * Real.exp Kstar) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          + 5 * (Kstar2 * Real.exp Kstar * ((Kstar4 * Real.exp Kstar ^ 4
              + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)
              + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2
              + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3
                  + 3 * Kstar2 * Real.exp Kstar
                    * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)) * Real.exp Kstar))
            * Real.exp Kstar))) * Real.exp Kstar)
    + 5 * (Kstar5 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 4)
    + Ld5f * Real.exp Kf * Real.exp Kstar ^ 5
    + 30 * (Kstar4 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar ^ 2
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 10 * (Kstar4 * Real.exp Kstar ^ 3 * expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2)
    + 10 * (Ld4f * Real.exp Kf * Real.exp Kstar ^ 3
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 15 * (Kstar3 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar)
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2)
    + 30 * (Kstar3 * Real.exp Kstar * expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 15 * (Ld3f * Real.exp Kf * Real.exp Kstar
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2)
    + 20 * (Kstar3 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar) * Real.exp Kstar
        * ((Kstar3 * Real.exp Kstar ^ 3
            + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          * Real.exp Kstar))
    + 10 * (Kstar3 * Real.exp Kstar ^ 2
        * expJet3VtpConst Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3)
    + 10 * (Ld3f * Real.exp Kf * Real.exp Kstar ^ 2 * ((Kstar3 * Real.exp Kstar ^ 3
        + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
      * Real.exp Kstar))
    + 10 * (Kstar2 * expJet3VtpConst Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3
        * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 10 * (Kstar2 * ((Kstar3 * Real.exp Kstar ^ 3
        + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
      * Real.exp Kstar) * expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2)
    + 10 * (Ld2f * Real.exp Kf * ((Kstar3 * Real.exp Kstar ^ 3
        + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
      * Real.exp Kstar) * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
    + 5 * (Kstar2 * (Ldf * Real.exp Kf * Real.exp Kstar * Real.exp Kstar)
        * ((Kstar4 * Real.exp Kstar ^ 4
            + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)
            + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2
            + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3
                + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
              * Real.exp Kstar)) * Real.exp Kstar))
    + 5 * (Kstar2 * Real.exp Kstar
        * expJet4VtpConst Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4)
    + 5 * (Ld2f * Real.exp Kf * Real.exp Kstar * ((Kstar4 * Real.exp Kstar ^ 4
        + 6 * Kstar3 * Real.exp Kstar ^ 2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar)
        + 3 * Kstar2 * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar) ^ 2
        + 4 * Kstar2 * Real.exp Kstar * ((Kstar3 * Real.exp Kstar ^ 3
            + 3 * Kstar2 * Real.exp Kstar * (Kstar2 * Real.exp Kstar ^ 2 * Real.exp Kstar))
          * Real.exp Kstar)) * Real.exp Kstar))) * Real.exp Kstar

theorem expJet5VtpConst_nonneg (Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ)
    (hLdf : 0 ≤ Ldf) (hLd2f : 0 ≤ Ld2f) (hLd3f : 0 ≤ Ld3f) (hLd4f : 0 ≤ Ld4f) (hLd5f : 0 ≤ Ld5f)
    (hKstar2 : 0 ≤ Kstar2) (hKstar3 : 0 ≤ Kstar3) (hKstar4 : 0 ≤ Kstar4) (hKstar5 : 0 ≤ Kstar5) :
    0 ≤ expJet5VtpConst Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5 := by
  have hCe2 : 0 ≤ expJet2VtpConst Kf Ldf Ld2f Kstar Kstar2 :=
    expJet2VtpConst_nonneg _ _ _ _ _ hLdf hLd2f hKstar2
  have hCe3 : 0 ≤ expJet3VtpConst Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3 :=
    expJet3VtpConst_nonneg _ _ _ _ _ _ _ hLdf hLd2f hLd3f hKstar2 hKstar3
  have hCe4 : 0 ≤ expJet4VtpConst Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4 :=
    expJet4VtpConst_nonneg _ _ _ _ _ _ _ _ _ hLdf hLd2f hLd3f hLd4f hKstar2 hKstar3 hKstar4
  unfold expJet5VtpConst
  positivity

end QIQTH.ExpMap
