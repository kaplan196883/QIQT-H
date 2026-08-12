/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemHelpers

/-!
# Jet₅ quadratic-remainder helper layer — the abstract TOP block

The order-5 remainder census (`docs/qg_roadmap/JET4_TOWER_PLAN.md`, J4-654) splits the 51-term
`Θ₅` quadratic remainder into 15 blocks.  This file banks the **abstract Top block**
`remBlkTop_bound`, the pure Faà-di-Bruno cancellation of the `D⁴F(Ph,Pk,Pl,Pm)` source term against
the `D⁵F(Ph,Pk,Pl,Pm,Pr)` full contraction and the four `D⁴F` `(2+1+1)` corrections whose coupling
pair contains the perturbation direction `r`.

It is the **direct one-Fréchet-order-up mirror** of the order-4 Block-1 argument
(`ExpJet4Remainder.lean:679`, `hbB1`): the third-variation head `D³F` is replaced by the
fourth-variation head `D⁴F`, the top correction `D⁴F` by `D⁵F`, and the three real directions
`h,k,l` become four `h,k,l,m` with the perturbation `m ↦ r`.  The `22`-term telescope was derived
and validated numerically (random symmetric multilinear data, residual `3.3e-16`) before
transcription.

Stated over an abstract normed space with every analytic input (`D⁴F` Taylor accuracy, `D⁵F`/`D⁴F`
operator-norm bounds, first-variation value/`δ`/`F` residual bounds) carried as a HYPOTHESIS and
every argument-permutation symmetry of the concrete `D⁴F`/`D⁵F` carried as an equality hypothesis,
in the exact style of the banked `remBlk0_bound`.  No `fderiv` atoms; the concrete assembly
instantiates them later.

## Honest firewall (binding)

Block-shape lemma ONLY.  This is a pure multilinear-algebra telescoping bound; it does NOT by itself
prove `expJet5_remainder_quadratic_bound` (which additionally needs Block-0, the fourteen cross
blocks, and the final assembly), does NOT prove `expJet5_remainder_quadratic_bound_P` / `_unif`, does
NOT reach `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or
`a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

/-- **Abstract Top block quadratic bound** (mirror of the order-4 Block-1 argument
    `ExpJet4Remainder.lean:679`, one Fréchet order up).

    The pure Faà-di-Bruno head term
    `d4w(Phw,Pkw,Plw,Pmw) − d4v(Ph,Pk,Pl,Pm) − d5v(Ph,Pk,Pl,Pm,Pr)`
    minus the four `(2+1+1)` perturbation corrections `d4v(·,·,·,Q·r)` telescopes exactly into a
    `D⁴F` second-order Taylor remainder, a `D⁵F` first-variation accuracy residual, four `d5v Pr`
    slot-difference residuals, and sixteen `d4v` cross residuals — each `O(nr²)` given the carried
    bounds.  `nr = ‖r‖`; `V` is a uniform value bound on the first variations; `Ddel·nr` bounds each
    two-point `δ`; `Fdel·nr²` bounds each first→second variation residual `F`. -/
theorem remBlkTop_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d5v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d4v d4w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (Ph Pk Pl Pm Phw Pkw Plw Pmw Pr Qhr Qkr Qlr Qmr dy : E)
    (nr eKf eKs L5 C2 Kstar5 Kstar4 V Ddel Fdel : ℝ)
    (hnr : 0 ≤ nr) (heKf : 0 ≤ eKf) (heKs : 0 ≤ eKs)
    (hL5 : 0 ≤ L5) (hC2 : 0 ≤ C2) (hK5 : 0 ≤ Kstar5) (hK4 : 0 ≤ Kstar4)
    (hV : 0 ≤ V) (hDdel : 0 ≤ Ddel) (hFdel : 0 ≤ Fdel)
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
    -- first-variation value bounds
    (hPh : ‖Ph‖ ≤ V) (hPk : ‖Pk‖ ≤ V) (hPl : ‖Pl‖ ≤ V) (hPm : ‖Pm‖ ≤ V)
    (hPhw : ‖Phw‖ ≤ V) (hPkw : ‖Pkw‖ ≤ V) (hPlw : ‖Plw‖ ≤ V) (hPmw : ‖Pmw‖ ≤ V)
    -- two-point `δ` smallness bounds
    (hda : ‖Phw - Ph‖ ≤ Ddel * nr) (hdb : ‖Pkw - Pk‖ ≤ Ddel * nr)
    (hdc : ‖Plw - Pl‖ ≤ Ddel * nr) (hdd : ‖Pmw - Pm‖ ≤ Ddel * nr)
    -- first→second variation residual bounds
    (hFa : ‖Phw - Ph - Qhr‖ ≤ Fdel * nr ^ 2) (hFb : ‖Pkw - Pk - Qkr‖ ≤ Fdel * nr ^ 2)
    (hFc : ‖Plw - Pl - Qlr‖ ≤ Fdel * nr ^ 2) (hFd : ‖Pmw - Pm - Qmr‖ ≤ Fdel * nr ^ 2) :
    ‖d4w Phw Pkw Plw Pmw - d4v Ph Pk Pl Pm - d5v Ph Pk Pl Pm Pr
       - d4v Pk Pl Pm Qhr - d4v Ph Pl Pm Qkr - d4v Ph Pk Pm Qlr - d4v Ph Pk Pl Qmr‖
      ≤ (L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4
          + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
          + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
          + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel
          + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel
          + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 := by
  -- exact 22-term telescoping identity (validated numerically; closes by symmetry + `abel`).
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
  -- derived value bounds on the `δ`'s (for the `F·δ` cross terms, `δ` enters at value scale)
  have hdaV : ‖Pk - Pkw‖ ≤ V + V := (norm_sub_le _ _).trans (add_le_add hPk hPkw)
  have hdcV : ‖Pl - Plw‖ ≤ V + V := (norm_sub_le _ _).trans (add_le_add hPl hPlw)
  have hddV : ‖Pm - Pmw‖ ≤ V + V := (norm_sub_le _ _).trans (add_le_add hPm hPmw)
  -- term bounds (one per telescope summand)
  have h1 : ‖(d4w - d4v - d5v dy) Phw Pkw Plw Pmw‖ ≤ (L5 * eKf ^ 2 * V ^ 4) * nr ^ 2 := by
    refine (clmApply4_norm_le (d4w - d4v - d5v dy) Phw Pkw Plw Pmw (by positivity) (by positivity)
      (by positivity) (by positivity) htay hPhw hPkw hPlw hPmw).trans (le_of_eq ?_)
    ring
  have h2 : ‖d5v (dy - Pr) Phw Pkw Plw Pmw‖ ≤ (Kstar5 * C2 * V ^ 4) * nr ^ 2 :=
    (clmApply5_norm_le d5v (dy - Pr) Phw Pkw Plw Pmw hK5 (by positivity) hV hV hV
      hd5 hacc hPhw hPkw hPlw hPmw).trans (le_of_eq (by ring))
  have h3 : ‖d5v Pr (Phw - Ph) Pkw Plw Pmw‖ ≤ (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr (Phw - Ph) Pkw Plw Pmw hK5 (by positivity) (by positivity) hV hV
      hd5 hPr hda hPkw hPlw hPmw).trans (le_of_eq (by ring))
  have h4 : ‖d5v Pr Ph (Pkw - Pk) Plw Pmw‖ ≤ (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph (Pkw - Pk) Plw Pmw hK5 (by positivity) hV (by positivity) hV
      hd5 hPr hPh hdb hPlw hPmw).trans (le_of_eq (by ring))
  have h5 : ‖d5v Pr Ph Pk (Plw - Pl) Pmw‖ ≤ (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph Pk (Plw - Pl) Pmw hK5 (by positivity) hV hV (by positivity)
      hd5 hPr hPh hPk hdc hPmw).trans (le_of_eq (by ring))
  have h6 : ‖d5v Pr Ph Pk Pl (Pmw - Pm)‖ ≤ (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 :=
    (clmApply5_norm_le d5v Pr Ph Pk Pl (Pmw - Pm) hK5 (by positivity) hV hV hV
      hd5 hPr hPh hPk hPl hdd).trans (le_of_eq (by ring))
  have h7 : ‖d4v Ph Pk Pl (Pmw - Pm - Qmr)‖ ≤ (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk Pl (Pmw - Pm - Qmr) hK4 hV hV hV hd4 hPh hPk hPl hFd).trans
      (le_of_eq (by ring))
  have h8 : ‖d4v Ph Pk (Plw - Pl - Qlr) Pmw‖ ≤ (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl - Qlr) Pmw hK4 hV hV (by positivity) hd4 hPh hPk hFc
      hPmw).trans (le_of_eq (by ring))
  have h9 : ‖d4v Ph Pk (Plw - Pl) (Pmw - Pm)‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl) (Pmw - Pm) hK4 hV hV (by positivity) hd4 hPh hPk hdc
      hdd).trans (le_of_eq (by ring))
  have h10 : ‖d4v Ph Pk (Plw - Pl - Qlr) (Pm - Pmw)‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph Pk (Plw - Pl - Qlr) (Pm - Pmw) hK4 hV hV (by positivity) hd4 hPh hPk
      hFc hddV).trans (le_of_eq (by ring))
  have h11 : ‖d4v Ph (Pkw - Pk - Qkr) Plw Pmw‖ ≤ (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) Plw Pmw hK4 hV (by positivity) hV hd4 hPh hFb hPlw
      hPmw).trans (le_of_eq (by ring))
  have h12 : ‖d4v Ph (Pkw - Pk) (Plw - Pl) Pmw‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk) (Plw - Pl) Pmw hK4 hV (by positivity) (by positivity) hd4
      hPh hdb hdc hPmw).trans (le_of_eq (by ring))
  have h13 : ‖d4v Ph (Pkw - Pk - Qkr) (Pl - Plw) Pmw‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) (Pl - Plw) Pmw hK4 hV (by positivity) (by positivity)
      hd4 hPh hFb hdcV hPmw).trans (le_of_eq (by ring))
  have h14 : ‖d4v Ph (Pkw - Pk) Pl (Pmw - Pm)‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk) Pl (Pmw - Pm) hK4 hV (by positivity) hV hd4 hPh hdb hPl
      hdd).trans (le_of_eq (by ring))
  have h15 : ‖d4v Ph (Pkw - Pk - Qkr) Pl (Pm - Pmw)‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v Ph (Pkw - Pk - Qkr) Pl (Pm - Pmw) hK4 hV (by positivity) hV hd4 hPh hFb
      hPl hddV).trans (le_of_eq (by ring))
  have h16 : ‖d4v (Phw - Ph - Qhr) Pkw Plw Pmw‖ ≤ (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pkw Plw Pmw hK4 (by positivity) hV hV hd4 hFa hPkw hPlw
      hPmw).trans (le_of_eq (by ring))
  have h17 : ‖d4v (Phw - Ph) (Pkw - Pk) Plw Pmw‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) (Pkw - Pk) Plw Pmw hK4 (by positivity) (by positivity) hV hd4
      hda hdb hPlw hPmw).trans (le_of_eq (by ring))
  have h18 : ‖d4v (Phw - Ph - Qhr) (Pk - Pkw) Plw Pmw‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) (Pk - Pkw) Plw Pmw hK4 (by positivity) (by positivity) hV
      hd4 hFa hdaV hPlw hPmw).trans (le_of_eq (by ring))
  have h19 : ‖d4v (Phw - Ph) Pk (Plw - Pl) Pmw‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) Pk (Plw - Pl) Pmw hK4 (by positivity) hV (by positivity) hd4
      hda hPk hdc hPmw).trans (le_of_eq (by ring))
  have h20 : ‖d4v (Phw - Ph - Qhr) Pk (Pl - Plw) Pmw‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pk (Pl - Plw) Pmw hK4 (by positivity) hV (by positivity)
      hd4 hFa hPk hdcV hPmw).trans (le_of_eq (by ring))
  have h21 : ‖d4v (Phw - Ph) Pk Pl (Pmw - Pm)‖ ≤ (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph) Pk Pl (Pmw - Pm) hK4 (by positivity) hV hV hd4 hda hPk hPl
      hdd).trans (le_of_eq (by ring))
  have h22 : ‖d4v (Phw - Ph - Qhr) Pk Pl (Pm - Pmw)‖ ≤ (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 :=
    (clmApply4_norm_le d4v (Phw - Ph - Qhr) Pk Pl (Pm - Pmw) hK4 (by positivity) hV hV hd4 hFa hPk
      hPl hddV).trans (le_of_eq (by ring))
  -- distribute the constant across the 22 summands and chain the triangle inequality
  rw [show (L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4
          + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
          + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3
          + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel
          + Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel
          + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Fdel + Kstar4 * V ^ 2 * Ddel ^ 2
          + 2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2
      = (L5 * eKf ^ 2 * V ^ 4) * nr ^ 2 + (Kstar5 * C2 * V ^ 4) * nr ^ 2
        + (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 + (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2
        + (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2 + (Kstar5 * eKs * Ddel * V ^ 3) * nr ^ 2
        + (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 + (Kstar4 * V ^ 3 * Fdel) * nr ^ 2
        + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2
        + (Kstar4 * V ^ 3 * Fdel) * nr ^ 2 + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2
        + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2
        + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2 + (Kstar4 * V ^ 3 * Fdel) * nr ^ 2
        + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2
        + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2
        + (Kstar4 * V ^ 2 * Ddel ^ 2) * nr ^ 2 + (2 * Kstar4 * V ^ 3 * Fdel) * nr ^ 2
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
