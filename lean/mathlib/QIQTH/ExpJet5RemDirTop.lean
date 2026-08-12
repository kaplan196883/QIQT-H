/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemBlkTop

/-!
# Jet_5 quadratic-remainder — DIRECTIONAL abstract top-block bound (rung J5-5c, dir foundation)

DIRECTIONAL variant of `remBlkTop_bound` (`ExpJet5RemBlkTop.lean`).  Identical 22-term telescope,
identical opaque-atom abel identity (reused verbatim), but every first-variation value / two-point /
first→second residual bound is carried with its OWN per-direction scale `Vh Vk Vl Vm` / `Dh Dk Dl Dm`
/ `Fh Fk Fl Fm` instead of one shared `V`/`Ddel`/`Fdel`.  Consequently the witness constant is a sum
of MIXED products `Kstar5·eKs·Dh·Vk·Vl·Vm`, `Kstar4·Vh·Vk·Vl·Fm`, … — so when the concrete directional
`_P` assembly instantiates `Vh := eKs·‖h‖`, `Dh := C3·‖h‖`, `Fh := Cd·‖h‖`, … the whole block bound
carries the explicit directional factor `‖h‖·‖k‖·‖l‖·‖m‖`.  This is the top brick of the directional
order-5 assembly the `_P`/`_unif` remainder packaging consumes.

## Honest firewall (binding)

Pure abstract functional-analysis block bound ONLY (opaque multilinear atoms).  Does NOT prove
`expJet5_remainder_quadratic_bound_P`, `expJet5_remainder_quadratic_bound_unif`,
`expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`
(CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Directional abstract order-5 top-block bound.**  Per-direction value scales `Vh Vk Vl Vm`,
    two-point scales `Dh Dk Dl Dm`, first→second residual scales `Fh Fk Fl Fm`; the resulting witness
    constant is a sum of mixed products carrying the explicit directional weight
    `‖h‖·‖k‖·‖l‖·‖m‖` once the concrete assembly instantiates each scale. -/
theorem remBlkTop_bound_dir
    (d5v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d4v d4w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (Ph Pk Pl Pm Phw Pkw Plw Pmw Pr Qhr Qkr Qlr Qmr dy : E)
    (nr eKf eKs L5 C2 Kstar5 Kstar4 Vh Vk Vl Vm Dh Dk Dl Dm Fh Fk Fl Fm : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL5 : 0 ≤ L5) (hC2 : 0 ≤ C2) (hK5 : 0 ≤ Kstar5) (hK4 : 0 ≤ Kstar4)
    (hVh : 0 ≤ Vh) (hVk : 0 ≤ Vk) (hVl : 0 ≤ Vl) (hVm : 0 ≤ Vm)
    (hDh : 0 ≤ Dh) (hDk : 0 ≤ Dk) (hDl : 0 ≤ Dl) (hDm : 0 ≤ Dm)
    (hFh : 0 ≤ Fh) (hFk : 0 ≤ Fk) (hFl : 0 ≤ Fl) (hFm : 0 ≤ Fm)
    -- full argument-permutation symmetry of the concrete `D⁴F`/`D⁵F` (carried as needed facts)
    (hcyc5 : d5v Pr Ph Pk Pl Pm = d5v Ph Pk Pl Pm Pr)
    (hQa : d4v Qhr Pk Pl Pm = d4v Pk Pl Pm Qhr)
    (hQb : d4v Ph Qkr Pl Pm = d4v Ph Pl Pm Qkr)
    (hQc : d4v Ph Pk Qlr Pm = d4v Ph Pk Pm Qlr)
    -- `D⁴F` second-order Taylor accuracy and operator-norm bounds
    (htay : ‖d4w - d4v - d5v dy‖ ≤ L5 * (nr * eKf) ^ 2)
    (hd5 : ‖d5v‖ ≤ Kstar5) (hd4 : ‖d4v‖ ≤ Kstar4)
    (hacc : ‖dy - Pr‖ ≤ C2 * nr ^ 2)
    (hPr : ‖Pr‖ ≤ eKs * nr)
    -- first-variation value bounds (per-direction)
    (hPh : ‖Ph‖ ≤ Vh) (hPk : ‖Pk‖ ≤ Vk) (hPl : ‖Pl‖ ≤ Vl) (hPm : ‖Pm‖ ≤ Vm)
    (hPhw : ‖Phw‖ ≤ Vh) (hPkw : ‖Pkw‖ ≤ Vk) (hPlw : ‖Plw‖ ≤ Vl) (hPmw : ‖Pmw‖ ≤ Vm)
    -- two-point `δ` smallness bounds (per-direction)
    (hda : ‖Phw - Ph‖ ≤ Dh * nr) (hdb : ‖Pkw - Pk‖ ≤ Dk * nr)
    (hdc : ‖Plw - Pl‖ ≤ Dl * nr) (hdd : ‖Pmw - Pm‖ ≤ Dm * nr)
    -- first→second variation residual bounds (per-direction)
    (hFa : ‖Phw - Ph - Qhr‖ ≤ Fh * nr ^ 2) (hFb : ‖Pkw - Pk - Qkr‖ ≤ Fk * nr ^ 2)
    (hFc : ‖Plw - Pl - Qlr‖ ≤ Fl * nr ^ 2) (hFd : ‖Pmw - Pm - Qmr‖ ≤ Fm * nr ^ 2) :
    ‖d4w Phw Pkw Plw Pmw - d4v Ph Pk Pl Pm - d5v Ph Pk Pl Pm Pr
       - d4v Pk Pl Pm Qhr - d4v Ph Pl Pm Qkr - d4v Ph Pk Pm Qlr - d4v Ph Pk Pl Qmr‖
      ≤ (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm) + Kstar5 * C2 * (Vh * Vk * Vl * Vm)
          + Kstar5 * eKs * Dh * Vk * Vl * Vm + Kstar5 * eKs * Vh * Dk * Vl * Vm
          + Kstar5 * eKs * Vh * Vk * Dl * Vm + Kstar5 * eKs * Vh * Vk * Vl * Dm
          + Kstar4 * Vh * Vk * Vl * Fm + Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Vk * Dl * Dm + 2 * Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Dl * Vm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Vl * Dm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Dk * Vl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Dl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Vl * Dm + 2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2 := by
  -- exact 22-term telescoping identity (reused verbatim from `remBlkTop_bound`).
  have heq : d4w Phw Pkw Plw Pmw - d4v Ph Pk Pl Pm - d5v Ph Pk Pl Pm Pr
       - d4v Pk Pl Pm Qhr - d4v Ph Pl Pm Qkr - d4v Ph Pk Pm Qlr - d4v Ph Pk Pl Qmr
      = (d4w - d4v - d5v dy) Phw Pkw Plw Pmw
        + d5v (dy - Pr) Phw Pkw Plw Pmw
        + d5v Pr (Phw - Ph) Pkw Plw Pmw
        + d5v Pr Ph (Pkw - Pk) Plw Pmw
        + d5v Pr Ph Pk (Plw - Pl) Pmw
        + d5v Pr Ph Pk Pl (Pmw - Pm)
        + d4v Ph Pk Pl (Pmw - Pm - Qmr)
        + d4v Ph Pk (Plw - Pl - Qlr) Pmw
        + d4v Ph Pk (Plw - Pl) (Pmw - Pm)
        + d4v Ph Pk (Plw - Pl - Qlr) (Pm - Pmw)
        + d4v Ph (Pkw - Pk - Qkr) Plw Pmw
        + d4v Ph (Pkw - Pk) (Plw - Pl) Pmw
        + d4v Ph (Pkw - Pk - Qkr) (Pl - Plw) Pmw
        + d4v Ph (Pkw - Pk) Pl (Pmw - Pm)
        + d4v Ph (Pkw - Pk - Qkr) Pl (Pm - Pmw)
        + d4v (Phw - Ph - Qhr) Pkw Plw Pmw
        + d4v (Phw - Ph) (Pkw - Pk) Plw Pmw
        + d4v (Phw - Ph - Qhr) (Pk - Pkw) Plw Pmw
        + d4v (Phw - Ph) Pk (Plw - Pl) Pmw
        + d4v (Phw - Ph - Qhr) Pk (Pl - Plw) Pmw
        + d4v (Phw - Ph) Pk Pl (Pmw - Pm)
        + d4v (Phw - Ph - Qhr) Pk Pl (Pm - Pmw) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [hcyc5, hQa, hQb, hQc]
    abel
  rw [heq]
  -- derived value bounds on the reversed `δ`'s (for the `F·δ` cross terms, `δ` enters at value scale)
  have hdaV : ‖Pk - Pkw‖ ≤ Vk + Vk := (norm_sub_le _ _).trans (add_le_add hPk hPkw)
  have hdcV : ‖Pl - Plw‖ ≤ Vl + Vl := (norm_sub_le _ _).trans (add_le_add hPl hPlw)
  have hddV : ‖Pm - Pmw‖ ≤ Vm + Vm := (norm_sub_le _ _).trans (add_le_add hPm hPmw)
  -- term bounds (one per telescope summand), each with its mixed directional product
  have h1 : ‖(d4w - d4v - d5v dy) Phw Pkw Plw Pmw‖
      ≤ (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm)) * nr ^ 2 := by
    refine (clmApply4_norm_le (d4w - d4v - d5v dy) Phw Pkw Plw Pmw (by positivity) hVh hVk hVl
      htay hPhw hPkw hPlw hPmw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d5v (dy - Pr) Phw Pkw Plw Pmw‖ ≤ (Kstar5 * C2 * (Vh * Vk * Vl * Vm)) * nr ^ 2 :=
    (clmApply5_norm_le d5v (dy - Pr) Phw Pkw Plw Pmw hK5 (by positivity) hVh hVk hVl
      hd5 hacc hPhw hPkw hPlw hPmw).trans (le_of_eq (by ring))
  have h3 : ‖d5v Pr (Phw - Ph) Pkw Plw Pmw‖ ≤ (Kstar5 * eKs * Dh * Vk * Vl * Vm) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr (Phw - Ph) Pkw Plw Pmw hK5 (by positivity) (by positivity) hVk hVl
      hd5 hPr hda hPkw hPlw hPmw).trans (le_of_eq (by ring))
  have h4 : ‖d5v Pr Ph (Pkw - Pk) Plw Pmw‖ ≤ (Kstar5 * eKs * Vh * Dk * Vl * Vm) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph (Pkw - Pk) Plw Pmw hK5 (by positivity) hVh (by positivity) hVl
      hd5 hPr hPh hdb hPlw hPmw).trans (le_of_eq (by ring))
  have h5 : ‖d5v Pr Ph Pk (Plw - Pl) Pmw‖ ≤ (Kstar5 * eKs * Vh * Vk * Dl * Vm) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph Pk (Plw - Pl) Pmw hK5 (by positivity) hVh hVk (by positivity)
      hd5 hPr hPh hPk hdc hPmw).trans (le_of_eq (by ring))
  have h6 : ‖d5v Pr Ph Pk Pl (Pmw - Pm)‖ ≤ (Kstar5 * eKs * Vh * Vk * Vl * Dm) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph Pk Pl (Pmw - Pm) hK5 (by positivity) hVh hVk hVl
      hd5 hPr hPh hPk hPl hdd).trans (le_of_eq (by ring))
  have h7 : ‖d4v Ph Pk Pl (Pmw - Pm - Qmr)‖ ≤ (Kstar4 * Vh * Vk * Vl * Fm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk Pl (Pmw - Pm - Qmr) hK4 hVh hVk hVl hd4 hPh hPk hPl hFd).trans
      (le_of_eq (by ring))
  have h8 : ‖d4v Ph Pk (Plw - Pl - Qlr) Pmw‖ ≤ (Kstar4 * Vh * Vk * Fl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl - Qlr) Pmw hK4 hVh hVk (by positivity) hd4 hPh hPk hFc
      hPmw).trans (le_of_eq (by ring))
  have h9 : ‖d4v Ph Pk (Plw - Pl) (Pmw - Pm)‖ ≤ (Kstar4 * Vh * Vk * Dl * Dm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl) (Pmw - Pm) hK4 hVh hVk (by positivity) hd4 hPh hPk hdc
      hdd).trans (le_of_eq (by ring))
  have h10 : ‖d4v Ph Pk (Plw - Pl - Qlr) (Pm - Pmw)‖ ≤ (2 * Kstar4 * Vh * Vk * Fl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl - Qlr) (Pm - Pmw) hK4 hVh hVk (by positivity) hd4 hPh hPk
      hFc hddV).trans (le_of_eq (by ring))
  have h11 : ‖d4v Ph (Pkw - Pk - Qkr) Plw Pmw‖ ≤ (Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) Plw Pmw hK4 hVh (by positivity) hVl hd4 hPh hFb hPlw
      hPmw).trans (le_of_eq (by ring))
  have h12 : ‖d4v Ph (Pkw - Pk) (Plw - Pl) Pmw‖ ≤ (Kstar4 * Vh * Dk * Dl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk) (Plw - Pl) Pmw hK4 hVh (by positivity) (by positivity) hd4
      hPh hdb hdc hPmw).trans (le_of_eq (by ring))
  have h13 : ‖d4v Ph (Pkw - Pk - Qkr) (Pl - Plw) Pmw‖ ≤ (2 * Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) (Pl - Plw) Pmw hK4 hVh (by positivity) (by positivity)
      hd4 hPh hFb hdcV hPmw).trans (le_of_eq (by ring))
  have h14 : ‖d4v Ph (Pkw - Pk) Pl (Pmw - Pm)‖ ≤ (Kstar4 * Vh * Dk * Vl * Dm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk) Pl (Pmw - Pm) hK4 hVh (by positivity) hVl hd4 hPh hdb hPl
      hdd).trans (le_of_eq (by ring))
  have h15 : ‖d4v Ph (Pkw - Pk - Qkr) Pl (Pm - Pmw)‖ ≤ (2 * Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) Pl (Pm - Pmw) hK4 hVh (by positivity) hVl hd4 hPh hFb
      hPl hddV).trans (le_of_eq (by ring))
  have h16 : ‖d4v (Phw - Ph - Qhr) Pkw Plw Pmw‖ ≤ (Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pkw Plw Pmw hK4 (by positivity) hVk hVl hd4 hFa hPkw hPlw
      hPmw).trans (le_of_eq (by ring))
  have h17 : ‖d4v (Phw - Ph) (Pkw - Pk) Plw Pmw‖ ≤ (Kstar4 * Dh * Dk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) (Pkw - Pk) Plw Pmw hK4 (by positivity) (by positivity) hVl hd4
      hda hdb hPlw hPmw).trans (le_of_eq (by ring))
  have h18 : ‖d4v (Phw - Ph - Qhr) (Pk - Pkw) Plw Pmw‖ ≤ (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) (Pk - Pkw) Plw Pmw hK4 (by positivity) (by positivity) hVl
      hd4 hFa hdaV hPlw hPmw).trans (le_of_eq (by ring))
  have h19 : ‖d4v (Phw - Ph) Pk (Plw - Pl) Pmw‖ ≤ (Kstar4 * Dh * Vk * Dl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) Pk (Plw - Pl) Pmw hK4 (by positivity) hVk (by positivity) hd4
      hda hPk hdc hPmw).trans (le_of_eq (by ring))
  have h20 : ‖d4v (Phw - Ph - Qhr) Pk (Pl - Plw) Pmw‖ ≤ (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pk (Pl - Plw) Pmw hK4 (by positivity) hVk (by positivity)
      hd4 hFa hPk hdcV hPmw).trans (le_of_eq (by ring))
  have h21 : ‖d4v (Phw - Ph) Pk Pl (Pmw - Pm)‖ ≤ (Kstar4 * Dh * Vk * Vl * Dm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) Pk Pl (Pmw - Pm) hK4 (by positivity) hVk hVl hd4 hda hPk hPl
      hdd).trans (le_of_eq (by ring))
  have h22 : ‖d4v (Phw - Ph - Qhr) Pk Pl (Pm - Pmw)‖ ≤ (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pk Pl (Pm - Pmw) hK4 (by positivity) hVk hVl hd4 hFa hPk
      hPl hddV).trans (le_of_eq (by ring))
  -- distribute the constant across the 22 summands and chain the triangle inequality
  rw [show (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm) + Kstar5 * C2 * (Vh * Vk * Vl * Vm)
          + Kstar5 * eKs * Dh * Vk * Vl * Vm + Kstar5 * eKs * Vh * Dk * Vl * Vm
          + Kstar5 * eKs * Vh * Vk * Dl * Vm + Kstar5 * eKs * Vh * Vk * Vl * Dm
          + Kstar4 * Vh * Vk * Vl * Fm + Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Vk * Dl * Dm + 2 * Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Dl * Vm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Vl * Dm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Dk * Vl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Dl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Vl * Dm + 2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2
      = (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm)) * nr ^ 2
        + (Kstar5 * C2 * (Vh * Vk * Vl * Vm)) * nr ^ 2
        + (Kstar5 * eKs * Dh * Vk * Vl * Vm) * nr ^ 2 + (Kstar5 * eKs * Vh * Dk * Vl * Vm) * nr ^ 2
        + (Kstar5 * eKs * Vh * Vk * Dl * Vm) * nr ^ 2 + (Kstar5 * eKs * Vh * Vk * Vl * Dm) * nr ^ 2
        + (Kstar4 * Vh * Vk * Vl * Fm) * nr ^ 2 + (Kstar4 * Vh * Vk * Fl * Vm) * nr ^ 2
        + (Kstar4 * Vh * Vk * Dl * Dm) * nr ^ 2 + (2 * Kstar4 * Vh * Vk * Fl * Vm) * nr ^ 2
        + (Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 + (Kstar4 * Vh * Dk * Dl * Vm) * nr ^ 2
        + (2 * Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 + (Kstar4 * Vh * Dk * Vl * Dm) * nr ^ 2
        + (2 * Kstar4 * Vh * Fk * Vl * Vm) * nr ^ 2 + (Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2
        + (Kstar4 * Dh * Dk * Vl * Vm) * nr ^ 2 + (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2
        + (Kstar4 * Dh * Vk * Dl * Vm) * nr ^ 2 + (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2
        + (Kstar4 * Dh * Vk * Vl * Dm) * nr ^ 2 + (2 * Kstar4 * Fh * Vk * Vl * Vm) * nr ^ 2
      from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ h22)
  refine (norm_add_le _ _).trans (add_le_add ?_ h21)
  refine (norm_add_le _ _).trans (add_le_add ?_ h20)
  refine (norm_add_le _ _).trans (add_le_add ?_ h19)
  refine (norm_add_le _ _).trans (add_le_add ?_ h18)
  refine (norm_add_le _ _).trans (add_le_add ?_ h17)
  refine (norm_add_le _ _).trans (add_le_add ?_ h16)
  refine (norm_add_le _ _).trans (add_le_add ?_ h15)
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

end QIQTH.ExpMap
