/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemBlkCross

/-!
# Jet_5 quadratic-remainder — DIRECTIONAL abstract cross-block bounds (rung J5-5c, dir foundation)

DIRECTIONAL variants of `remBlk211_bound` / `remBlk22_bound` / `remBlk31_bound`
(`ExpJet5RemBlkCross.lean`).  Identical telescopes and opaque-atom abel identities, but every value /
two-point / residual bound is carried with its OWN per-direction scale, so the witness constant is a
sum of MIXED products.  When the concrete directional `_P` assembly instantiates each scale with the
corresponding directional value (`Va := eKs·‖a‖`, `Vxy := Cq2·‖x‖·‖y‖`, …) the block bounds carry the
explicit directional factor.  These are the cross bricks of the directional order-5 assembly the
`_P`/`_unif` remainder packaging consumes.

## Honest firewall (binding)

Pure abstract functional-analysis block bounds ONLY (opaque multilinear atoms).  Does NOT prove
`expJet5_remainder_quadratic_bound_P`, `expJet5_remainder_quadratic_bound_unif`,
`expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`
(CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Directional abstract `(2+1+1)` cross block bound.**  Per-direction scales `Va Vb` (first
    variations), `Vq` (second variation), `Da Db` (two-point), `Fa Fb` (first→second residuals),
    `Ql` (second-variation Lipschitz), `Fq` (second→third residual). -/
theorem remBlk211_bound_dir
    (d4v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d3v d3w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (Pa Pb Paw Pbw Pr Qar Qbr Qxy Qwxy Qxyr dy : E)
    (nr eKf eKs L4 C2 Kstar4 Kstar3 Va Vb Vq Da Db Ql Fa Fb Fq : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL4 : 0 ≤ L4) (hC2 : 0 ≤ C2) (hK4 : 0 ≤ Kstar4) (hK3 : 0 ≤ Kstar3)
    (hVa : 0 ≤ Va) (hVb : 0 ≤ Vb) (hVq : 0 ≤ Vq) (hDa : 0 ≤ Da) (hDb : 0 ≤ Db)
    (hQl : 0 ≤ Ql) (hFa0 : 0 ≤ Fa) (hFb0 : 0 ≤ Fb) (hFq0 : 0 ≤ Fq)
    (hcyc4 : d4v Pr Pa Pb Qxy = d4v Pa Pb Pr Qxy)
    (htay : ‖d3w - d3v - d4v dy‖ ≤ L4 * (nr * eKf) ^ 2)
    (hd4 : ‖d4v‖ ≤ Kstar4) (hd3 : ‖d3v‖ ≤ Kstar3)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hPa : ‖Pa‖ ≤ Va) (hPb : ‖Pb‖ ≤ Vb) (hPaw : ‖Paw‖ ≤ Va) (hPbw : ‖Pbw‖ ≤ Vb)
    (hQxy : ‖Qxy‖ ≤ Vq) (hQwxy : ‖Qwxy‖ ≤ Vq)
    (hda : ‖Paw - Pa‖ ≤ Da * nr) (hdb : ‖Pbw - Pb‖ ≤ Db * nr)
    (hQlipQ : ‖Qwxy - Qxy‖ ≤ Ql * nr)
    (hFa : ‖Paw - Pa - Qar‖ ≤ Fa * nr ^ 2) (hFb : ‖Pbw - Pb - Qbr‖ ≤ Fb * nr ^ 2)
    (hFQ : ‖Qwxy - Qxy - Qxyr‖ ≤ Fq * nr ^ 2) :
    ‖d3w Paw Pbw Qwxy - d3v Pa Pb Qxy - d4v Pa Pb Pr Qxy
       - d3v Qar Pb Qxy - d3v Pa Qbr Qxy - d3v Pa Pb Qxyr‖
      ≤ (L4 * eKf ^ 2 * (Va * Vb) * Vq + Kstar4 * C2 * (Va * Vb) * Vq
          + Kstar4 * eKs * Da * Vb * Vq + Kstar4 * eKs * Va * Db * Vq
          + Kstar4 * eKs * Va * Vb * Ql
          + Kstar3 * Va * Vb * Fq
          + Kstar3 * Va * Fb * Vq + Kstar3 * Va * Db * Ql
          + 2 * Kstar3 * Va * Fb * Vq
          + Kstar3 * Fa * Vb * Vq + Kstar3 * Da * Db * Vq
          + 2 * Kstar3 * Fa * Vb * Vq + Kstar3 * Da * Vb * Ql
          + 2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2 := by
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
  have hdaV : ‖Pb - Pbw‖ ≤ Vb + Vb := (norm_sub_le _ _).trans (add_le_add hPb hPbw)
  have hQV : ‖Qxy - Qwxy‖ ≤ Vq + Vq := (norm_sub_le _ _).trans (add_le_add hQxy hQwxy)
  have h1 : ‖(d3w - d3v - d4v dy) Paw Pbw Qwxy‖ ≤ (L4 * eKf ^ 2 * (Va * Vb) * Vq) * nr ^ 2 := by
    refine (clmApply3_norm_le (d3w - d3v - d4v dy) Paw Pbw Qwxy (by positivity) hVa hVb
      htay hPaw hPbw hQwxy).trans (le_of_eq ?_)
    ring
  have h2 : ‖d4v (dy - Pr) Paw Pbw Qwxy‖ ≤ (Kstar4 * C2 * (Va * Vb) * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v (dy - Pr) Paw Pbw Qwxy hK4 (by positivity) hVa hVb hd4 hacc hPaw hPbw
      hQwxy).trans (le_of_eq (by ring))
  have h3 : ‖d4v Pr (Paw - Pa) Pbw Qwxy‖ ≤ (Kstar4 * eKs * Da * Vb * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr (Paw - Pa) Pbw Qwxy hK4 (by positivity) (by positivity) hVb
      hd4 hPr hda hPbw hQwxy).trans (le_of_eq (by ring))
  have h4 : ‖d4v Pr Pa (Pbw - Pb) Qwxy‖ ≤ (Kstar4 * eKs * Va * Db * Vq) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr Pa (Pbw - Pb) Qwxy hK4 (by positivity) hVa (by positivity)
      hd4 hPr hPa hdb hQwxy).trans (le_of_eq (by ring))
  have h5 : ‖d4v Pr Pa Pb (Qwxy - Qxy)‖ ≤ (Kstar4 * eKs * Va * Vb * Ql) * nr ^ 2 :=
    (clmApply4_norm_le d4v Pr Pa Pb (Qwxy - Qxy) hK4 (by positivity) hVa hVb
      hd4 hPr hPa hPb hQlipQ).trans (le_of_eq (by ring))
  have h6 : ‖d3v Pa Pb (Qwxy - Qxy - Qxyr)‖ ≤ (Kstar3 * Va * Vb * Fq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa Pb (Qwxy - Qxy - Qxyr) hK3 hVa hVb hd3 hPa hPb hFQ).trans
      (le_of_eq (by ring))
  have h7 : ‖d3v Pa (Pbw - Pb - Qbr) Qwxy‖ ≤ (Kstar3 * Va * Fb * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb - Qbr) Qwxy hK3 hVa (by positivity) hd3 hPa hFb hQwxy).trans
      (le_of_eq (by ring))
  have h8 : ‖d3v Pa (Pbw - Pb) (Qwxy - Qxy)‖ ≤ (Kstar3 * Va * Db * Ql) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb) (Qwxy - Qxy) hK3 hVa (by positivity) hd3 hPa hdb hQlipQ).trans
      (le_of_eq (by ring))
  have h9 : ‖d3v Pa (Pbw - Pb - Qbr) (Qxy - Qwxy)‖ ≤ (2 * Kstar3 * Va * Fb * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pa (Pbw - Pb - Qbr) (Qxy - Qwxy) hK3 hVa (by positivity) hd3 hPa hFb
      hQV).trans (le_of_eq (by ring))
  have h10 : ‖d3v (Paw - Pa - Qar) Pbw Qwxy‖ ≤ (Kstar3 * Fa * Vb * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) Pbw Qwxy hK3 (by positivity) hVb hd3 hFa hPbw hQwxy).trans
      (le_of_eq (by ring))
  have h11 : ‖d3v (Paw - Pa) (Pbw - Pb) Qwxy‖ ≤ (Kstar3 * Da * Db * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa) (Pbw - Pb) Qwxy hK3 (by positivity) (by positivity) hd3 hda hdb
      hQwxy).trans (le_of_eq (by ring))
  have h12 : ‖d3v (Paw - Pa - Qar) (Pb - Pbw) Qwxy‖ ≤ (2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) (Pb - Pbw) Qwxy hK3 (by positivity) (by positivity) hd3
      hFa hdaV hQwxy).trans (le_of_eq (by ring))
  have h13 : ‖d3v (Paw - Pa) Pb (Qwxy - Qxy)‖ ≤ (Kstar3 * Da * Vb * Ql) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa) Pb (Qwxy - Qxy) hK3 (by positivity) hVb hd3 hda hPb hQlipQ).trans
      (le_of_eq (by ring))
  have h14 : ‖d3v (Paw - Pa - Qar) Pb (Qxy - Qwxy)‖ ≤ (2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2 :=
    (clmApply3_norm_le d3v (Paw - Pa - Qar) Pb (Qxy - Qwxy) hK3 (by positivity) hVb hd3 hFa hPb
      hQV).trans (le_of_eq (by ring))
  rw [show (L4 * eKf ^ 2 * (Va * Vb) * Vq + Kstar4 * C2 * (Va * Vb) * Vq
          + Kstar4 * eKs * Da * Vb * Vq + Kstar4 * eKs * Va * Db * Vq
          + Kstar4 * eKs * Va * Vb * Ql + Kstar3 * Va * Vb * Fq
          + Kstar3 * Va * Fb * Vq + Kstar3 * Va * Db * Ql
          + 2 * Kstar3 * Va * Fb * Vq + Kstar3 * Fa * Vb * Vq + Kstar3 * Da * Db * Vq
          + 2 * Kstar3 * Fa * Vb * Vq + Kstar3 * Da * Vb * Ql
          + 2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2
      = (L4 * eKf ^ 2 * (Va * Vb) * Vq) * nr ^ 2 + (Kstar4 * C2 * (Va * Vb) * Vq) * nr ^ 2
        + (Kstar4 * eKs * Da * Vb * Vq) * nr ^ 2 + (Kstar4 * eKs * Va * Db * Vq) * nr ^ 2
        + (Kstar4 * eKs * Va * Vb * Ql) * nr ^ 2 + (Kstar3 * Va * Vb * Fq) * nr ^ 2
        + (Kstar3 * Va * Fb * Vq) * nr ^ 2 + (Kstar3 * Va * Db * Ql) * nr ^ 2
        + (2 * Kstar3 * Va * Fb * Vq) * nr ^ 2 + (Kstar3 * Fa * Vb * Vq) * nr ^ 2
        + (Kstar3 * Da * Db * Vq) * nr ^ 2 + (2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2
        + (Kstar3 * Da * Vb * Ql) * nr ^ 2 + (2 * Kstar3 * Fa * Vb * Vq) * nr ^ 2
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

/-- **Directional abstract `(2+2)` cross block bound.**  Per-direction scales `Vxy Vzw` (second
    variations), `Vxyr Vzwr` (second→third value), `Qcxy Qczw` (second→third smallness), `Qlxy Qlzw`
    (Lipschitz), `VFxy VFzw` (residual value), `Fxy Fzw` (second→third residual). -/
theorem remBlk22_bound_dir
    (d3v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (Pr Qxy Qzw Qwxy Qwzw Qxyr Qzwr dy : E)
    (nr eKf eKs L3 C2 Kstar3 Kstar2 Vxy Vzw Vxyr Vzwr VFxy VFzw Qcxy Qczw Qlxy Qlzw Fxy Fzw : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL3 : 0 ≤ L3) (hC2 : 0 ≤ C2) (hK3 : 0 ≤ Kstar3) (hK2 : 0 ≤ Kstar2)
    (hVxy : 0 ≤ Vxy) (hVzw : 0 ≤ Vzw) (hVxyr : 0 ≤ Vxyr) (hVzwr : 0 ≤ Vzwr)
    (hVFxy : 0 ≤ VFxy) (hVFzw : 0 ≤ VFzw) (hQcxy : 0 ≤ Qcxy) (hQczw : 0 ≤ Qczw)
    (hQlxy : 0 ≤ Qlxy) (hQlzw : 0 ≤ Qlzw) (hFxy0 : 0 ≤ Fxy) (hFzw0 : 0 ≤ Fzw)
    (htay : ‖d2w - d2v - d3v dy‖ ≤ L3 * (nr * eKf) ^ 2)
    (hd3 : ‖d3v‖ ≤ Kstar3) (hd2 : ‖d2v‖ ≤ Kstar2)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hQxy : ‖Qxy‖ ≤ Vxy) (hQzw : ‖Qzw‖ ≤ Vzw) (hQwxy : ‖Qwxy‖ ≤ Vxy) (hQwzw : ‖Qwzw‖ ≤ Vzw)
    (hQxyrV : ‖Qxyr‖ ≤ Vxyr) (hQzwrV : ‖Qzwr‖ ≤ Vzwr)
    (hQxyrs : ‖Qxyr‖ ≤ Qcxy * nr) (hQzwrs : ‖Qzwr‖ ≤ Qczw * nr)
    (hQlipXY : ‖Qwxy - Qxy‖ ≤ Qlxy * nr) (hQlipZW : ‖Qwzw - Qzw‖ ≤ Qlzw * nr)
    (hFQxyV : ‖Qwxy - Qxy - Qxyr‖ ≤ VFxy) (hFQzwV : ‖Qwzw - Qzw - Qzwr‖ ≤ VFzw)
    (hFQxy : ‖Qwxy - Qxy - Qxyr‖ ≤ Fxy * nr ^ 2) (hFQzw : ‖Qwzw - Qzw - Qzwr‖ ≤ Fzw * nr ^ 2) :
    ‖d2w Qwxy Qwzw - d2v Qxy Qzw - d3v Pr Qxy Qzw - d2v Qxyr Qzw - d2v Qxy Qzwr‖
      ≤ (L3 * eKf ^ 2 * (Vxy * Vzw) + Kstar3 * C2 * (Vxy * Vzw)
          + Kstar3 * eKs * Qlxy * Vzw + Kstar3 * eKs * Vxy * Qlzw
          + Kstar2 * Vxy * Fzw + Kstar2 * Qcxy * Qczw + Kstar2 * Vxyr * Fzw
          + Kstar2 * Fxy * Vzw + Kstar2 * Fxy * Vzwr + Kstar2 * Fxy * VFzw) * nr ^ 2 := by
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
  have h1 : ‖(d2w - d2v - d3v dy) Qwxy Qwzw‖ ≤ (L3 * eKf ^ 2 * (Vxy * Vzw)) * nr ^ 2 := by
    refine (clmApply2_norm_le (d2w - d2v - d3v dy) Qwxy Qwzw (by positivity) (by positivity)
      htay hQwxy hQwzw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d3v (dy - Pr) Qwxy Qwzw‖ ≤ (Kstar3 * C2 * (Vxy * Vzw)) * nr ^ 2 :=
    (clmApply3_norm_le d3v (dy - Pr) Qwxy Qwzw hK3 (by positivity) hVxy hd3 hacc hQwxy hQwzw).trans
      (le_of_eq (by ring))
  have h3 : ‖d3v Pr (Qwxy - Qxy) Qwzw‖ ≤ (Kstar3 * eKs * Qlxy * Vzw) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr (Qwxy - Qxy) Qwzw hK3 (by positivity) (by positivity) hd3 hPr hQlipXY
      hQwzw).trans (le_of_eq (by ring))
  have h4 : ‖d3v Pr Qxy (Qwzw - Qzw)‖ ≤ (Kstar3 * eKs * Vxy * Qlzw) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr Qxy (Qwzw - Qzw) hK3 (by positivity) hVxy hd3 hPr hQxy hQlipZW).trans
      (le_of_eq (by ring))
  have h5 : ‖d2v Qxy (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Vxy * Fzw) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxy (Qwzw - Qzw - Qzwr) hK2 hVxy hd2 hQxy hFQzw).trans (le_of_eq (by ring))
  have h6 : ‖d2v Qxyr Qzwr‖ ≤ (Kstar2 * Qcxy * Qczw) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxyr Qzwr hK2 (by positivity) hd2 hQxyrs hQzwrs).trans (le_of_eq (by ring))
  have h7 : ‖d2v Qxyr (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Vxyr * Fzw) * nr ^ 2 :=
    (clmApply2_norm_le d2v Qxyr (Qwzw - Qzw - Qzwr) hK2 hVxyr hd2 hQxyrV hFQzw).trans
      (le_of_eq (by ring))
  have h8 : ‖d2v (Qwxy - Qxy - Qxyr) Qzw‖ ≤ (Kstar2 * Fxy * Vzw) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) Qzw hK2 (by positivity) hd2 hFQxy hQzw).trans
      (le_of_eq (by ring))
  have h9 : ‖d2v (Qwxy - Qxy - Qxyr) Qzwr‖ ≤ (Kstar2 * Fxy * Vzwr) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) Qzwr hK2 (by positivity) hd2 hFQxy hQzwrV).trans
      (le_of_eq (by ring))
  have h10 : ‖d2v (Qwxy - Qxy - Qxyr) (Qwzw - Qzw - Qzwr)‖ ≤ (Kstar2 * Fxy * VFzw) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Qwxy - Qxy - Qxyr) (Qwzw - Qzw - Qzwr) hK2 (by positivity) hd2 hFQxy
      hFQzwV).trans (le_of_eq (by ring))
  rw [show (L3 * eKf ^ 2 * (Vxy * Vzw) + Kstar3 * C2 * (Vxy * Vzw)
          + Kstar3 * eKs * Qlxy * Vzw + Kstar3 * eKs * Vxy * Qlzw
          + Kstar2 * Vxy * Fzw + Kstar2 * Qcxy * Qczw + Kstar2 * Vxyr * Fzw
          + Kstar2 * Fxy * Vzw + Kstar2 * Fxy * Vzwr + Kstar2 * Fxy * VFzw) * nr ^ 2
      = (L3 * eKf ^ 2 * (Vxy * Vzw)) * nr ^ 2 + (Kstar3 * C2 * (Vxy * Vzw)) * nr ^ 2
        + (Kstar3 * eKs * Qlxy * Vzw) * nr ^ 2 + (Kstar3 * eKs * Vxy * Qlzw) * nr ^ 2
        + (Kstar2 * Vxy * Fzw) * nr ^ 2 + (Kstar2 * Qcxy * Qczw) * nr ^ 2
        + (Kstar2 * Vxyr * Fzw) * nr ^ 2
        + (Kstar2 * Fxy * Vzw) * nr ^ 2 + (Kstar2 * Fxy * Vzwr) * nr ^ 2
        + (Kstar2 * Fxy * VFzw) * nr ^ 2
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

/-- **Directional abstract `(3+1)` cross block bound.**  Per-direction scales `Vx` (first variation),
    `Vq3` (third variation), `Dx` (two-point), `Ql3` (third-variation Lipschitz), `Fx` (first→second
    residual), `Fq3` (third→fourth residual). -/
theorem remBlk31_bound_dir
    (d3v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (Px Pxw Pr Qxr Qyzw Qwyzw Qyzwr dy : E)
    (nr eKf eKs L3 C2 Kstar3 Kstar2 Vx Vq3 Dx Ql3 Fx Fq3 : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL3 : 0 ≤ L3) (hC2 : 0 ≤ C2) (hK3 : 0 ≤ Kstar3) (hK2 : 0 ≤ Kstar2)
    (hVx : 0 ≤ Vx) (hVq3 : 0 ≤ Vq3) (hDx : 0 ≤ Dx) (hQl3 : 0 ≤ Ql3)
    (hFx0 : 0 ≤ Fx) (hFq30 : 0 ≤ Fq3)
    (hsA : d3v Pr Px Qyzw = d3v Px Pr Qyzw)
    (htay : ‖d2w - d2v - d3v dy‖ ≤ L3 * (nr * eKf) ^ 2)
    (hd3 : ‖d3v‖ ≤ Kstar3) (hd2 : ‖d2v‖ ≤ Kstar2)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2) (hPr : ‖Pr‖ ≤ eKs * nr)
    (hPx : ‖Px‖ ≤ Vx) (hPxw : ‖Pxw‖ ≤ Vx) (hQyzw : ‖Qyzw‖ ≤ Vq3) (hQwyzw : ‖Qwyzw‖ ≤ Vq3)
    (hdx : ‖Pxw - Px‖ ≤ Dx * nr) (hQlip3 : ‖Qwyzw - Qyzw‖ ≤ Ql3 * nr)
    (hFx : ‖Pxw - Px - Qxr‖ ≤ Fx * nr ^ 2)
    (hFQ3 : ‖Qwyzw - Qyzw - Qyzwr‖ ≤ Fq3 * nr ^ 2) :
    ‖d2w Pxw Qwyzw - d2v Px Qyzw - d3v Px Pr Qyzw - d2v Qxr Qyzw - d2v Px Qyzwr‖
      ≤ (L3 * eKf ^ 2 * (Vx * Vq3) + Kstar3 * C2 * (Vx * Vq3)
          + Kstar3 * eKs * Dx * Vq3 + Kstar3 * eKs * Vx * Ql3
          + Kstar2 * Dx * Ql3 + 2 * Kstar2 * Fx * Vq3
          + Kstar2 * Fx * Vq3 + Kstar2 * Vx * Fq3) * nr ^ 2 := by
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
  have h1 : ‖(d2w - d2v - d3v dy) Pxw Qwyzw‖ ≤ (L3 * eKf ^ 2 * (Vx * Vq3)) * nr ^ 2 := by
    refine (clmApply2_norm_le (d2w - d2v - d3v dy) Pxw Qwyzw (by positivity) (by positivity)
      htay hPxw hQwyzw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d3v (dy - Pr) Pxw Qwyzw‖ ≤ (Kstar3 * C2 * (Vx * Vq3)) * nr ^ 2 :=
    (clmApply3_norm_le d3v (dy - Pr) Pxw Qwyzw hK3 (by positivity) hVx hd3 hacc hPxw hQwyzw).trans
      (le_of_eq (by ring))
  have h3 : ‖d3v Pr (Pxw - Px) Qwyzw‖ ≤ (Kstar3 * eKs * Dx * Vq3) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr (Pxw - Px) Qwyzw hK3 (by positivity) (by positivity) hd3 hPr hdx
      hQwyzw).trans (le_of_eq (by ring))
  have h4 : ‖d3v Pr Px (Qwyzw - Qyzw)‖ ≤ (Kstar3 * eKs * Vx * Ql3) * nr ^ 2 :=
    (clmApply3_norm_le d3v Pr Px (Qwyzw - Qyzw) hK3 (by positivity) hVx hd3 hPr hPx hQlip3).trans
      (le_of_eq (by ring))
  have h5 : ‖d2v (Pxw - Px) (Qwyzw - Qyzw)‖ ≤ (Kstar2 * Dx * Ql3) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px) (Qwyzw - Qyzw) hK2 (by positivity) hd2 hdx hQlip3).trans
      (le_of_eq (by ring))
  have h6 : ‖d2v (Pxw - Px - Qxr) (Qyzw - Qwyzw)‖ ≤ (2 * Kstar2 * Fx * Vq3) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px - Qxr) (Qyzw - Qwyzw) hK2 (by positivity) hd2 hFx hQV).trans
      (le_of_eq (by ring))
  have h7 : ‖d2v (Pxw - Px - Qxr) Qwyzw‖ ≤ (Kstar2 * Fx * Vq3) * nr ^ 2 :=
    (clmApply2_norm_le d2v (Pxw - Px - Qxr) Qwyzw hK2 (by positivity) hd2 hFx hQwyzw).trans
      (le_of_eq (by ring))
  have h8 : ‖d2v Px (Qwyzw - Qyzw - Qyzwr)‖ ≤ (Kstar2 * Vx * Fq3) * nr ^ 2 :=
    (clmApply2_norm_le d2v Px (Qwyzw - Qyzw - Qyzwr) hK2 hVx hd2 hPx hFQ3).trans (le_of_eq (by ring))
  rw [show (L3 * eKf ^ 2 * (Vx * Vq3) + Kstar3 * C2 * (Vx * Vq3)
          + Kstar3 * eKs * Dx * Vq3 + Kstar3 * eKs * Vx * Ql3
          + Kstar2 * Dx * Ql3 + 2 * Kstar2 * Fx * Vq3
          + Kstar2 * Fx * Vq3 + Kstar2 * Vx * Fq3) * nr ^ 2
      = (L3 * eKf ^ 2 * (Vx * Vq3)) * nr ^ 2 + (Kstar3 * C2 * (Vx * Vq3)) * nr ^ 2
        + (Kstar3 * eKs * Dx * Vq3) * nr ^ 2 + (Kstar3 * eKs * Vx * Ql3) * nr ^ 2
        + (Kstar2 * Dx * Ql3) * nr ^ 2 + (2 * Kstar2 * Fx * Vq3) * nr ^ 2
        + (Kstar2 * Fx * Vq3) * nr ^ 2 + (Kstar2 * Vx * Fq3) * nr ^ 2
      from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ h8)
  refine (norm_add_le _ _).trans (add_le_add ?_ h7)
  refine (norm_add_le _ _).trans (add_le_add ?_ h6)
  refine (norm_add_le _ _).trans (add_le_add ?_ h5)
  refine (norm_add_le _ _).trans (add_le_add ?_ h4)
  refine (norm_add_le _ _).trans (add_le_add ?_ h3)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end QIQTH.ExpMap
