/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemHelpers

/-!
# Jet₅ quadratic-remainder helper layer — the three abstract CROSS blocks

The order-5 remainder census (`docs/qg_roadmap/JET4_TOWER_PLAN.md`, J4-654) splits the 51-term
`Θ₅` quadratic remainder into 15 blocks.  Beyond `remBlk0_bound` (head) and `remBlkTop_bound` (the
pure Faà-di-Bruno top), the remaining thirteen blocks come in three abstract SHAPES.  This file banks
one representative abstract-normed-space bound for each:

* `remBlk211_bound` — the `(2+1+1)` shape (source `D³F(Pa,Pb,Qxy)`, two first-variation slots and one
  second-variation slot).  The direct one-Fréchet-order-up mirror of the order-4 Block-2 argument
  (`ExpJet4Remainder.lean:474`, `hbB2`), with the perturbation `m ↦ r` and one extra first-variation
  slot; `14`-term telescope.
* `remBlk22_bound` — the `(2+2)` shape (source `D²F(Qxy,Qzw)`, two second-variation slots);
  `10`-term telescope, no argument symmetry needed.
* `remBlk31_bound` — the `(3+1)` shape (source `D²F(Px,Qyzw)`, one first-variation slot and one
  third-variation slot).  The direct mirror of the order-4 Block-2 shape with the second-variation
  slot promoted to a third-variation; `8`-term telescope.

Every telescope was derived and validated numerically (random symmetric multilinear data, residuals
`≤ 2.2e-16`) before transcription.  Every analytic input is carried as a HYPOTHESIS and every
argument-permutation symmetry of the concrete derivatives as an equality hypothesis, in the exact
style of the banked `remBlk0_bound` / `remBlkTop_bound`.  No `fderiv` atoms.

## Honest firewall (binding)

Block-shape lemmas ONLY.  These are pure multilinear-algebra telescoping bounds; they do NOT by
themselves prove `expJet5_remainder_quadratic_bound` (which additionally needs Block-0, the Top
block, and the final assembly of all fifteen blocks), do NOT prove
`expJet5_remainder_quadratic_bound_P` / `_unif`, do NOT reach `expMap_fderiv4_hasFDerivAt`,
`exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

/-- **Abstract `(2+1+1)` cross block quadratic bound** (mirror of the order-4 Block-2 argument
    `ExpJet4Remainder.lean:474`, one Fréchet order up with an extra first-variation slot).

    The source `d3w(Paw,Pbw,Qwxy) − d3v(Pa,Pb,Qxy) − d4v(Pa,Pb,Pr,Qxy)` minus the three perturbation
    corrections telescopes into a `D³F` Taylor remainder, a `D⁴F` accuracy residual, three `d4v Pr`
    slot-difference residuals and eight `d3v` cross residuals — each `O(nr²)`.  `V`/`Vq` are uniform
    value bounds on the first/second variations; `Ddel·nr` bounds each two-point `δ`; `Qlip·nr` the
    second-variation Lipschitz gap; `Fdel·nr²` each first→second and `Fq·nr²` the second→third
    variation residual. -/
theorem remBlk211_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d4v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d3v d3w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (Pa Pb Paw Pbw Pr Qar Qbr Qxy Qwxy Qxyr dy : E)
    (nr eKf eKs L4 C2 Kstar4 Kstar3 V Vq Ddel Qlip Fdel Fq : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL4 : 0 ≤ L4) (hC2 : 0 ≤ C2) (hK4 : 0 ≤ Kstar4) (hK3 : 0 ≤ Kstar3)
    (hV : 0 ≤ V) (hVq : 0 ≤ Vq) (hDdel : 0 ≤ Ddel) (hQlip : 0 ≤ Qlip)
    (hFdel : 0 ≤ Fdel) (hFq : 0 ≤ Fq)
    (hcyc4 : d4v Pr Pa Pb Qxy = d4v Pa Pb Pr Qxy)
    (htay : ‖d3w - d3v - d4v dy‖ ≤ L4 * (nr * eKf) ^ 2)
    (hd4 : ‖d4v‖ ≤ Kstar4) (hd3 : ‖d3v‖ ≤ Kstar3)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hPa : ‖Pa‖ ≤ V) (hPb : ‖Pb‖ ≤ V) (hPaw : ‖Paw‖ ≤ V) (hPbw : ‖Pbw‖ ≤ V)
    (hQxy : ‖Qxy‖ ≤ Vq) (hQwxy : ‖Qwxy‖ ≤ Vq)
    (hda : ‖Paw - Pa‖ ≤ Ddel * nr) (hdb : ‖Pbw - Pb‖ ≤ Ddel * nr)
    (hQlipQ : ‖Qwxy - Qxy‖ ≤ Qlip * nr)
    (hFa : ‖Paw - Pa - Qar‖ ≤ Fdel * nr ^ 2) (hFb : ‖Pbw - Pb - Qbr‖ ≤ Fdel * nr ^ 2)
    (hFQ : ‖Qwxy - Qxy - Qxyr‖ ≤ Fq * nr ^ 2) :
    ‖d3w Paw Pbw Qwxy - d3v Pa Pb Qxy - d4v Pa Pb Pr Qxy
       - d3v Qar Pb Qxy - d3v Pa Qbr Qxy - d3v Pa Pb Qxyr‖
      ≤ (L4 * eKf ^ 2 * V ^ 2 * Vq + Kstar4 * C2 * V ^ 2 * Vq
          + Kstar4 * eKs * Ddel * V * Vq + Kstar4 * eKs * Ddel * V * Vq
          + Kstar4 * eKs * Qlip * V ^ 2
          + Kstar3 * V ^ 2 * Fq
          + Kstar3 * V * Vq * Fdel + Kstar3 * V * Ddel * Qlip
          + 2 * Kstar3 * V * Vq * Fdel
          + Kstar3 * V * Vq * Fdel + Kstar3 * Ddel ^ 2 * Vq
          + 2 * Kstar3 * V * Vq * Fdel + Kstar3 * Ddel * Qlip * V
          + 2 * Kstar3 * V * Vq * Fdel) * nr ^ 2 := by
  have heq : d3w Paw Pbw Qwxy - d3v Pa Pb Qxy - d4v Pa Pb Pr Qxy
       - d3v Qar Pb Qxy - d3v Pa Qbr Qxy - d3v Pa Pb Qxyr
      = (d3w - d3v - d4v dy) Paw Pbw Qwxy
        + d4v (dy - Pr) Paw Pbw Qwxy
        + d4v Pr (Paw - Pa) Pbw Qwxy
        + d4v Pr Pa (Pbw - Pb) Qwxy
        + d4v Pr Pa Pb (Qwxy - Qxy)
        + d3v Pa Pb (Qwxy - Qxy - Qxyr)
        + d3v Pa (Pbw - Pb - Qbr) Qwxy
        + d3v Pa (Pbw - Pb) (Qwxy - Qxy)
        + d3v Pa (Pbw - Pb - Qbr) (Qxy - Qwxy)
        + d3v (Paw - Pa - Qar) Pbw Qwxy
        + d3v (Paw - Pa) (Pbw - Pb) Qwxy
        + d3v (Paw - Pa - Qar) (Pb - Pbw) Qwxy
        + d3v (Paw - Pa) Pb (Qwxy - Qxy)
        + d3v (Paw - Pa - Qar) Pb (Qxy - Qwxy) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [hcyc4]
    abel
  rw [heq]
  have hdaV : ‖Pb - Pbw‖ ≤ V + V := (norm_sub_le _ _).trans (add_le_add hPb hPbw)
  have hQV : ‖Qxy - Qwxy‖ ≤ Vq + Vq := (norm_sub_le _ _).trans (add_le_add hQxy hQwxy)
  have h1 : ‖(d3w - d3v - d4v dy) Paw Pbw Qwxy‖ ≤ (L4 * eKf ^ 2 * V ^ 2 * Vq) * nr ^ 2 := by
    refine (clmApply3_norm_le (d3w - d3v - d4v dy) Paw Pbw Qwxy (by positivity) (by positivity)
      (by positivity) htay hPaw hPbw hQwxy).trans (le_of_eq ?_)
    ring
  have h2 : ‖d4v (dy - Pr) Paw Pbw Qwxy‖ ≤ (Kstar4 * C2 * V ^ 2 * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v (dy - Pr) Paw Pbw Qwxy hK4 (by positivity) hV hV hd4 hacc hPaw hPbw
      hQwxy).trans (le_of_eq (by ring))
  have h3 : ‖d4v Pr (Paw - Pa) Pbw Qwxy‖ ≤ (Kstar4 * eKs * Ddel * V * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr (Paw - Pa) Pbw Qwxy hK4 (by positivity) (by positivity) hV
      hd4 hPr hda hPbw hQwxy).trans (le_of_eq (by ring))
  have h4 : ‖d4v Pr Pa (Pbw - Pb) Qwxy‖ ≤ (Kstar4 * eKs * Ddel * V * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr Pa (Pbw - Pb) Qwxy hK4 (by positivity) hV (by positivity)
      hd4 hPr hPa hdb hQwxy).trans (le_of_eq (by ring))
  have h5 : ‖d4v Pr Pa Pb (Qwxy - Qxy)‖ ≤ (Kstar4 * eKs * Qlip * V ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr Pa Pb (Qwxy - Qxy) hK4 (by positivity) hV hV
      hd4 hPr hPa hPb hQlipQ).trans (le_of_eq (by ring))
  have h6 : ‖d3v Pa Pb (Qwxy - Qxy - Qxyr)‖ ≤ (Kstar3 * V ^ 2 * Fq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa Pb (Qwxy - Qxy - Qxyr) hK3 hV hV hd3 hPa hPb hFQ).trans
      (le_of_eq (by ring))
  have h7 : ‖d3v Pa (Pbw - Pb - Qbr) Qwxy‖ ≤ (Kstar3 * V * Vq * Fdel) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb - Qbr) Qwxy hK3 hV (by positivity) hd3 hPa hFb hQwxy).trans
      (le_of_eq (by ring))
  have h8 : ‖d3v Pa (Pbw - Pb) (Qwxy - Qxy)‖ ≤ (Kstar3 * V * Ddel * Qlip) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb) (Qwxy - Qxy) hK3 hV (by positivity) hd3 hPa hdb hQlipQ).trans
      (le_of_eq (by ring))
  have h9 : ‖d3v Pa (Pbw - Pb - Qbr) (Qxy - Qwxy)‖ ≤ (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb - Qbr) (Qxy - Qwxy) hK3 hV (by positivity) hd3 hPa hFb
      hQV).trans (le_of_eq (by ring))
  have h10 : ‖d3v (Paw - Pa - Qar) Pbw Qwxy‖ ≤ (Kstar3 * V * Vq * Fdel) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) Pbw Qwxy hK3 (by positivity) hV hd3 hFa hPbw hQwxy).trans
      (le_of_eq (by ring))
  have h11 : ‖d3v (Paw - Pa) (Pbw - Pb) Qwxy‖ ≤ (Kstar3 * Ddel ^ 2 * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa) (Pbw - Pb) Qwxy hK3 (by positivity) (by positivity) hd3 hda hdb
      hQwxy).trans (le_of_eq (by ring))
  have h12 : ‖d3v (Paw - Pa - Qar) (Pb - Pbw) Qwxy‖ ≤ (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) (Pb - Pbw) Qwxy hK3 (by positivity) (by positivity) hd3
      hFa hdaV hQwxy).trans (le_of_eq (by ring))
  have h13 : ‖d3v (Paw - Pa) Pb (Qwxy - Qxy)‖ ≤ (Kstar3 * Ddel * Qlip * V) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa) Pb (Qwxy - Qxy) hK3 (by positivity) hV hd3 hda hPb hQlipQ).trans
      (le_of_eq (by ring))
  have h14 : ‖d3v (Paw - Pa - Qar) Pb (Qxy - Qwxy)‖ ≤ (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) Pb (Qxy - Qwxy) hK3 (by positivity) hV hd3 hFa hPb
      hQV).trans (le_of_eq (by ring))
  rw [show (L4 * eKf ^ 2 * V ^ 2 * Vq + Kstar4 * C2 * V ^ 2 * Vq
          + Kstar4 * eKs * Ddel * V * Vq + Kstar4 * eKs * Ddel * V * Vq
          + Kstar4 * eKs * Qlip * V ^ 2 + Kstar3 * V ^ 2 * Fq
          + Kstar3 * V * Vq * Fdel + Kstar3 * V * Ddel * Qlip
          + 2 * Kstar3 * V * Vq * Fdel + Kstar3 * V * Vq * Fdel + Kstar3 * Ddel ^ 2 * Vq
          + 2 * Kstar3 * V * Vq * Fdel + Kstar3 * Ddel * Qlip * V
          + 2 * Kstar3 * V * Vq * Fdel) * nr ^ 2
      = (L4 * eKf ^ 2 * V ^ 2 * Vq) * nr ^ 2 + (Kstar4 * C2 * V ^ 2 * Vq) * nr ^ 2
        + (Kstar4 * eKs * Ddel * V * Vq) * nr ^ 2 + (Kstar4 * eKs * Ddel * V * Vq) * nr ^ 2
        + (Kstar4 * eKs * Qlip * V ^ 2) * nr ^ 2 + (Kstar3 * V ^ 2 * Fq) * nr ^ 2
        + (Kstar3 * V * Vq * Fdel) * nr ^ 2 + (Kstar3 * V * Ddel * Qlip) * nr ^ 2
        + (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2 + (Kstar3 * V * Vq * Fdel) * nr ^ 2
        + (Kstar3 * Ddel ^ 2 * Vq) * nr ^ 2 + (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2
        + (Kstar3 * Ddel * Qlip * V) * nr ^ 2 + (2 * Kstar3 * V * Vq * Fdel) * nr ^ 2
      from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ h14)
  refine (norm_add_le _ _).trans (add_le_add ?_ h13)
  refine (norm_add_le _ _).trans (add_le_add ?_ h12)
  refine (norm_add_le _ _).trans (add_le_add ?_ h11)
  refine (norm_add_le _ _).trans (add_le_add ?_ h10)
  refine (norm_add_le _ _).trans (add_le_add ?_ h9)
  refine (norm_add_le _ _).trans (add_le_add ?_ h8)
  refine (norm_add_le _ _).trans (add_le_add ?_ h7)
  refine (norm_add_le _ _).trans (add_le_add ?_ h6)
  refine (norm_add_le _ _).trans (add_le_add ?_ h5)
  refine (norm_add_le _ _).trans (add_le_add ?_ h4)
  refine (norm_add_le _ _).trans (add_le_add ?_ h3)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- **Abstract `(2+2)` cross block quadratic bound** (source `D²F(Qxy,Qzw)`, two second-variation
    slots).  `10`-term telescope; no argument-permutation symmetry needed (the top `d3v Pr` base
    already matches).  `Vq`/`Vqr`/`VFq` are value bounds on the second variations / the
    second→third couplings / the residual; `Qcr·nr` the smallness of a second→third coupling,
    `Qlip·nr` the second-variation Lipschitz gap, `Fq·nr²` the second→third residual. -/
theorem remBlk22_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d3v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (Pr Qxy Qzw Qwxy Qwzw Qxyr Qzwr dy : E)
    (nr eKf eKs L3 C2 Kstar3 Kstar2 Vq Vqr VFq Qcr Qlip Fq : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL3 : 0 ≤ L3) (hC2 : 0 ≤ C2) (hK3 : 0 ≤ Kstar3) (hK2 : 0 ≤ Kstar2)
    (hVq : 0 ≤ Vq) (hVqr : 0 ≤ Vqr) (hVFq : 0 ≤ VFq) (hQcr : 0 ≤ Qcr)
    (hQlip : 0 ≤ Qlip) (hFq : 0 ≤ Fq)
    (htay : ‖d2w - d2v - d3v dy‖ ≤ L3 * (nr * eKf) ^ 2)
    (hd3 : ‖d3v‖ ≤ Kstar3) (hd2 : ‖d2v‖ ≤ Kstar2)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hQxy : ‖Qxy‖ ≤ Vq) (hQzw : ‖Qzw‖ ≤ Vq) (hQwxy : ‖Qwxy‖ ≤ Vq) (hQwzw : ‖Qwzw‖ ≤ Vq)
    (hQxyrV : ‖Qxyr‖ ≤ Vqr) (hQzwrV : ‖Qzwr‖ ≤ Vqr)
    (hQxyrs : ‖Qxyr‖ ≤ Qcr * nr) (hQzwrs : ‖Qzwr‖ ≤ Qcr * nr)
    (hQlipXY : ‖Qwxy - Qxy‖ ≤ Qlip * nr) (hQlipZW : ‖Qwzw - Qzw‖ ≤ Qlip * nr)
    (hFQxyV : ‖Qwxy - Qxy - Qxyr‖ ≤ VFq) (hFQzwV : ‖Qwzw - Qzw - Qzwr‖ ≤ VFq)
    (hFQxy : ‖Qwxy - Qxy - Qxyr‖ ≤ Fq * nr ^ 2) (hFQzw : ‖Qwzw - Qzw - Qzwr‖ ≤ Fq * nr ^ 2) :
    ‖d2w Qwxy Qwzw - d2v Qxy Qzw - d3v Pr Qxy Qzw - d2v Qxyr Qzw - d2v Qxy Qzwr‖
      ≤ (L3 * eKf ^ 2 * Vq ^ 2 + Kstar3 * C2 * Vq ^ 2
          + Kstar3 * eKs * Qlip * Vq + Kstar3 * eKs * Qlip * Vq
          + Kstar2 * Vq * Fq + Kstar2 * Qcr ^ 2 + Kstar2 * Vqr * Fq
          + Kstar2 * Fq * Vq + Kstar2 * Fq * Vqr + Kstar2 * Fq * VFq) * nr ^ 2 := by
  have heq : d2w Qwxy Qwzw - d2v Qxy Qzw - d3v Pr Qxy Qzw - d2v Qxyr Qzw - d2v Qxy Qzwr
      = (d2w - d2v - d3v dy) Qwxy Qwzw
        + d3v (dy - Pr) Qwxy Qwzw
        + d3v Pr (Qwxy - Qxy) Qwzw
        + d3v Pr Qxy (Qwzw - Qzw)
        + d2v Qxy (Qwzw - Qzw - Qzwr)
        + d2v Qxyr Qzwr
        + d2v Qxyr (Qwzw - Qzw - Qzwr)
        + d2v (Qwxy - Qxy - Qxyr) Qzw
        + d2v (Qwxy - Qxy - Qxyr) Qzwr
        + d2v (Qwxy - Qxy - Qxyr) (Qwzw - Qzw - Qzwr) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  have h1 : ‖(d2w - d2v - d3v dy) Qwxy Qwzw‖ ≤ (L3 * eKf ^ 2 * Vq ^ 2) * nr ^ 2 := by
    refine (clmApply2_norm_le (d2w - d2v - d3v dy) Qwxy Qwzw (by positivity) (by positivity)
      htay hQwxy hQwzw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d3v (dy - Pr) Qwxy Qwzw‖ ≤ (Kstar3 * C2 * Vq ^ 2) * nr ^ 2 :=
    (clmApply3_norm_le d3v (dy - Pr) Qwxy Qwzw hK3 (by positivity) hVq hd3 hacc hQwxy hQwzw).trans
      (le_of_eq (by ring))
  have h3 : ‖d3v Pr (Qwxy - Qxy) Qwzw‖ ≤ (Kstar3 * eKs * Qlip * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr (Qwxy - Qxy) Qwzw hK3 (by positivity) (by positivity) hd3 hPr hQlipXY
      hQwzw).trans (le_of_eq (by ring))
  have h4 : ‖d3v Pr Qxy (Qwzw - Qzw)‖ ≤ (Kstar3 * eKs * Qlip * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr Qxy (Qwzw - Qzw) hK3 (by positivity) hVq hd3 hPr hQxy hQlipZW).trans
      (le_of_eq (by ring))
  have h5 : ‖d2v Qxy (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Vq * Fq) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxy (Qwzw - Qzw - Qzwr) hK2 hVq hd2 hQxy hFQzw).trans (le_of_eq (by ring))
  have h6 : ‖d2v Qxyr Qzwr‖ ≤ (Kstar2 * Qcr ^ 2) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxyr Qzwr hK2 (by positivity) hd2 hQxyrs hQzwrs).trans (le_of_eq (by ring))
  have h7 : ‖d2v Qxyr (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Vqr * Fq) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxyr (Qwzw - Qzw - Qzwr) hK2 hVqr hd2 hQxyrV hFQzw).trans
      (le_of_eq (by ring))
  have h8 : ‖d2v (Qwxy - Qxy - Qxyr) Qzw‖ ≤ (Kstar2 * Fq * Vq) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) Qzw hK2 (by positivity) hd2 hFQxy hQzw).trans
      (le_of_eq (by ring))
  have h9 : ‖d2v (Qwxy - Qxy - Qxyr) Qzwr‖ ≤ (Kstar2 * Fq * Vqr) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) Qzwr hK2 (by positivity) hd2 hFQxy hQzwrV).trans
      (le_of_eq (by ring))
  have h10 : ‖d2v (Qwxy - Qxy - Qxyr) (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Fq * VFq) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) (Qwzw - Qzw - Qzwr) hK2 (by positivity) hd2 hFQxy
      hFQzwV).trans (le_of_eq (by ring))
  rw [show (L3 * eKf ^ 2 * Vq ^ 2 + Kstar3 * C2 * Vq ^ 2
          + Kstar3 * eKs * Qlip * Vq + Kstar3 * eKs * Qlip * Vq
          + Kstar2 * Vq * Fq + Kstar2 * Qcr ^ 2 + Kstar2 * Vqr * Fq
          + Kstar2 * Fq * Vq + Kstar2 * Fq * Vqr + Kstar2 * Fq * VFq) * nr ^ 2
      = (L3 * eKf ^ 2 * Vq ^ 2) * nr ^ 2 + (Kstar3 * C2 * Vq ^ 2) * nr ^ 2
        + (Kstar3 * eKs * Qlip * Vq) * nr ^ 2 + (Kstar3 * eKs * Qlip * Vq) * nr ^ 2
        + (Kstar2 * Vq * Fq) * nr ^ 2 + (Kstar2 * Qcr ^ 2) * nr ^ 2 + (Kstar2 * Vqr * Fq) * nr ^ 2
        + (Kstar2 * Fq * Vq) * nr ^ 2 + (Kstar2 * Fq * Vqr) * nr ^ 2 + (Kstar2 * Fq * VFq) * nr ^ 2
      from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ h10)
  refine (norm_add_le _ _).trans (add_le_add ?_ h9)
  refine (norm_add_le _ _).trans (add_le_add ?_ h8)
  refine (norm_add_le _ _).trans (add_le_add ?_ h7)
  refine (norm_add_le _ _).trans (add_le_add ?_ h6)
  refine (norm_add_le _ _).trans (add_le_add ?_ h5)
  refine (norm_add_le _ _).trans (add_le_add ?_ h4)
  refine (norm_add_le _ _).trans (add_le_add ?_ h3)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- **Abstract `(3+1)` cross block quadratic bound** (source `D²F(Px,Qyzw)`, one first-variation
    slot and one third-variation slot).  The direct mirror of the order-4 Block-2 shape with the
    second-variation slot promoted to a third-variation; `8`-term telescope, one argument symmetry
    (`hsA`, the top `d3v` first-two-argument swap).  `V`/`Vq3` value bounds on the first / third
    variations; `Ddel·nr` the two-point `δ`, `Qlip·nr` the third-variation Lipschitz gap,
    `Fdel·nr²` the first→second and `Fq·nr²` the third→fourth variation residual. -/
theorem remBlk31_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d3v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (Px Pxw Pr Qxr Qyzw Qwyzw Qyzwr dy : E)
    (nr eKf eKs L3 C2 Kstar3 Kstar2 V Vq3 Ddel Qlip Fdel Fq : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL3 : 0 ≤ L3) (hC2 : 0 ≤ C2) (hK3 : 0 ≤ Kstar3) (hK2 : 0 ≤ Kstar2)
    (hV : 0 ≤ V) (hVq3 : 0 ≤ Vq3) (hDdel : 0 ≤ Ddel) (hQlip : 0 ≤ Qlip)
    (hFdel : 0 ≤ Fdel) (hFq : 0 ≤ Fq)
    (hsA : d3v Pr Px Qyzw = d3v Px Pr Qyzw)
    (htay : ‖d2w - d2v - d3v dy‖ ≤ L3 * (nr * eKf) ^ 2)
    (hd3 : ‖d3v‖ ≤ Kstar3) (hd2 : ‖d2v‖ ≤ Kstar2)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hPx : ‖Px‖ ≤ V) (hPxw : ‖Pxw‖ ≤ V) (hQyzw : ‖Qyzw‖ ≤ Vq3) (hQwyzw : ‖Qwyzw‖ ≤ Vq3)
    (hdx : ‖Pxw - Px‖ ≤ Ddel * nr) (hQlip3 : ‖Qwyzw - Qyzw‖ ≤ Qlip * nr)
    (hFx : ‖Pxw - Px - Qxr‖ ≤ Fdel * nr ^ 2)
    (hFQ3 : ‖Qwyzw - Qyzw - Qyzwr‖ ≤ Fq * nr ^ 2) :
    ‖d2w Pxw Qwyzw - d2v Px Qyzw - d3v Px Pr Qyzw - d2v Qxr Qyzw - d2v Px Qyzwr‖
      ≤ (L3 * eKf ^ 2 * V * Vq3 + Kstar3 * C2 * V * Vq3
          + Kstar3 * eKs * Ddel * Vq3 + Kstar3 * eKs * Qlip * V
          + Kstar2 * Ddel * Qlip + 2 * Kstar2 * Vq3 * Fdel
          + Kstar2 * Vq3 * Fdel + Kstar2 * V * Fq) * nr ^ 2 := by
  have heq : d2w Pxw Qwyzw - d2v Px Qyzw - d3v Px Pr Qyzw - d2v Qxr Qyzw - d2v Px Qyzwr
      = (d2w - d2v - d3v dy) Pxw Qwyzw
        + d3v (dy - Pr) Pxw Qwyzw
        + d3v Pr (Pxw - Px) Qwyzw
        + d3v Pr Px (Qwyzw - Qyzw)
        + d2v (Pxw - Px) (Qwyzw - Qyzw)
        + d2v (Pxw - Px - Qxr) (Qyzw - Qwyzw)
        + d2v (Pxw - Px - Qxr) Qwyzw
        + d2v Px (Qwyzw - Qyzw - Qyzwr) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsA]
    abel
  rw [heq]
  have hQV : ‖Qyzw - Qwyzw‖ ≤ Vq3 + Vq3 := (norm_sub_le _ _).trans (add_le_add hQyzw hQwyzw)
  have h1 : ‖(d2w - d2v - d3v dy) Pxw Qwyzw‖ ≤ (L3 * eKf ^ 2 * V * Vq3) * nr ^ 2 := by
    refine (clmApply2_norm_le (d2w - d2v - d3v dy) Pxw Qwyzw (by positivity) (by positivity)
      htay hPxw hQwyzw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d3v (dy - Pr) Pxw Qwyzw‖ ≤ (Kstar3 * C2 * V * Vq3) * nr ^ 2 :=
    (clmApply3_norm_le d3v (dy - Pr) Pxw Qwyzw hK3 (by positivity) hV hd3 hacc hPxw hQwyzw).trans
      (le_of_eq (by ring))
  have h3 : ‖d3v Pr (Pxw - Px) Qwyzw‖ ≤ (Kstar3 * eKs * Ddel * Vq3) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr (Pxw - Px) Qwyzw hK3 (by positivity) (by positivity) hd3 hPr hdx
      hQwyzw).trans (le_of_eq (by ring))
  have h4 : ‖d3v Pr Px (Qwyzw - Qyzw)‖ ≤ (Kstar3 * eKs * Qlip * V) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr Px (Qwyzw - Qyzw) hK3 (by positivity) hV hd3 hPr hPx hQlip3).trans
      (le_of_eq (by ring))
  have h5 : ‖d2v (Pxw - Px) (Qwyzw - Qyzw)‖ ≤ (Kstar2 * Ddel * Qlip) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px) (Qwyzw - Qyzw) hK2 (by positivity) hd2 hdx hQlip3).trans
      (le_of_eq (by ring))
  have h6 : ‖d2v (Pxw - Px - Qxr) (Qyzw - Qwyzw)‖ ≤ (2 * Kstar2 * Vq3 * Fdel) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px - Qxr) (Qyzw - Qwyzw) hK2 (by positivity) hd2 hFx hQV).trans
      (le_of_eq (by ring))
  have h7 : ‖d2v (Pxw - Px - Qxr) Qwyzw‖ ≤ (Kstar2 * Vq3 * Fdel) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px - Qxr) Qwyzw hK2 (by positivity) hd2 hFx hQwyzw).trans
      (le_of_eq (by ring))
  have h8 : ‖d2v Px (Qwyzw - Qyzw - Qyzwr)‖ ≤ (Kstar2 * V * Fq) * nr ^ 2 :=
    (clmApply2_norm_le d2v Px (Qwyzw - Qyzw - Qyzwr) hK2 hV hd2 hPx hFQ3).trans (le_of_eq (by ring))
  rw [show (L3 * eKf ^ 2 * V * Vq3 + Kstar3 * C2 * V * Vq3
          + Kstar3 * eKs * Ddel * Vq3 + Kstar3 * eKs * Qlip * V
          + Kstar2 * Ddel * Qlip + 2 * Kstar2 * Vq3 * Fdel
          + Kstar2 * Vq3 * Fdel + Kstar2 * V * Fq) * nr ^ 2
      = (L3 * eKf ^ 2 * V * Vq3) * nr ^ 2 + (Kstar3 * C2 * V * Vq3) * nr ^ 2
        + (Kstar3 * eKs * Ddel * Vq3) * nr ^ 2 + (Kstar3 * eKs * Qlip * V) * nr ^ 2
        + (Kstar2 * Ddel * Qlip) * nr ^ 2 + (2 * Kstar2 * Vq3 * Fdel) * nr ^ 2
        + (Kstar2 * Vq3 * Fdel) * nr ^ 2 + (Kstar2 * V * Fq) * nr ^ 2
      from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ h8)
  refine (norm_add_le _ _).trans (add_le_add ?_ h7)
  refine (norm_add_le _ _).trans (add_le_add ?_ h6)
  refine (norm_add_le _ _).trans (add_le_add ?_ h5)
  refine (norm_add_le _ _).trans (add_le_add ?_ h4)
  refine (norm_add_le _ _).trans (add_le_add ?_ h3)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end QIQTH.ExpMap
