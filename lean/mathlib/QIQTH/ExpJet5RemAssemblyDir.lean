/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderB
import QIQTH.ExpJet5RemDirTop
import QIQTH.ExpJet5RemDirCross

/-!
# Jet_5 quadratic-remainder — DIRECTIONAL abstract assembly lemma (rung J5-5c, dir assembly)

Banks `remAssembly_dir`: the DIRECTIONAL variant of `remAssembly` (`ExpJet5RemainderB.lean`).  Over
an abstract normed space with opaque multilinear atoms, the order-5 residual head
`(dw − dv) qw + (Θ₄w − Θ₄v − Θ₅v)` is bounded by `Cfull_dir · nr²`, where every value / two-point /
first→second / second→third / Lipschitz bound is carried with its OWN per-direction scale.  The
fifteen block bounds are the directional bricks `remBlk0_bound` (already directional-capable) +
`remBlkTop_bound_dir` + `remBlk211_bound_dir`×6 + `remBlk22_bound_dir`×3 + `remBlk31_bound_dir`×4.
The reassembly is the SAME opaque master `remMaster_identity`.  The witness constant is the sum of the
fifteen per-direction block constants, so once the concrete `_P` assembly instantiates each scale with
its directional value (`Vh := eKs·‖h‖`, `Vhk := Cq2·‖h‖·‖k‖`, …) the whole bound carries the explicit
directional factor `‖h‖·‖k‖·‖l‖·‖m‖`.

The heavy `≈130-term` distribute-ring is ISOLATED into the pure-ℝ 16-atom helper `distrib15_nr` (a
trivial `ring` on named atoms), so the assembly proof itself never runs a large `ring`/`whnf`.

## Honest firewall (binding)

Pure functional-analysis assembly ONLY.  Does NOT prove `expJet5_remainder_quadratic_bound_P`,
`expJet5_remainder_quadratic_bound_unif`, `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the
heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pure-ℝ 16-atom distribution helper: `(Σ aᵢ)·q = Σ (aᵢ·q)`.  Isolates the assembly's constant
    distribution so the main proof never runs a large `ring`. -/
private theorem distrib15_nr (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 q : ℝ) :
    (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14) * q
      = a0 * q + a1 * q + a2 * q + a3 * q + a4 * q + a5 * q + a6 * q + a7 * q + a8 * q + a9 * q
        + a10 * q + a11 * q + a12 * q + a13 * q + a14 * q := by ring

/-- **Directional abstract order-5 quadratic-remainder assembly.**  Per-direction value / two-point /
    residual / Lipschitz scales; witness constant = sum of the fifteen per-direction block constants. -/
theorem remAssembly_dir
    (dv dw : E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (d3v d3w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d4v d4w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d5v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (qw Pr Ph Pk Pl Pm Phw Pkw Plw Pmw Qhk Qhl Qhm Qkl Qkm Qlm Qhr Qkr Qlr Qmr Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qhkl Qhkm Qhlm Qklm Qhkr Qhlr Qhmr Qklr Qkmr Qlmr Qwhkl Qwhkm Qwhlm Qwklm Qhklm Qhklr Qhkmr Qhlmr Qklmr yv yw : E)
    (nr eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5 M4 Ce0 : ℝ)
    (Vh Vk Vl Vm Dh Dk Dl Dm Fh Fk Fl Fm : ℝ)
    (Vhk Vhl Vhm Vkl Vkm Vlm Lhk Lhl Lhm Lkl Lkm Llm FQhk FQhl FQhm FQkl FQkm FQlm : ℝ)
    (VQ3hkr VQ3hlr VQ3hmr VQ3klr VQ3kmr VQ3lmr Ccrhk Ccrhl Ccrhm Ccrkl Ccrkm Ccrlm VFqhk VFqhl VFqhm VFqkl VFqkm VFqlm : ℝ)
    (Vklm Vhlm Vhkm Vhkl L3klm L3hlm L3hkm L3hkl FQ3klm FQ3hlm FQ3hkm FQ3hkl : ℝ)
    (hnr0 : 0 ≤ nr) (heKf0 : 0 ≤ eKf) (heKs0 : 0 ≤ eKs)
    (hL2_0 : 0 ≤ L2) (hL3_0 : 0 ≤ L3) (hL4_0 : 0 ≤ L4) (hL5_0 : 0 ≤ L5)
    (hC2_0 : 0 ≤ C2) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3)
    (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5) (hM40 : 0 ≤ M4) (hCe00 : 0 ≤ Ce0)
    (hVh0 : 0 ≤ Vh) (hVk0 : 0 ≤ Vk) (hVl0 : 0 ≤ Vl) (hVm0 : 0 ≤ Vm)
    (hDh0 : 0 ≤ Dh) (hDk0 : 0 ≤ Dk) (hDl0 : 0 ≤ Dl) (hDm0 : 0 ≤ Dm)
    (hFh0 : 0 ≤ Fh) (hFk0 : 0 ≤ Fk) (hFl0 : 0 ≤ Fl) (hFm0 : 0 ≤ Fm)
    (hVhk0 : 0 ≤ Vhk) (hVhl0 : 0 ≤ Vhl) (hVhm0 : 0 ≤ Vhm) (hVkl0 : 0 ≤ Vkl) (hVkm0 : 0 ≤ Vkm) (hVlm0 : 0 ≤ Vlm)
    (hLhk0 : 0 ≤ Lhk) (hLhl0 : 0 ≤ Lhl) (hLhm0 : 0 ≤ Lhm) (hLkl0 : 0 ≤ Lkl) (hLkm0 : 0 ≤ Lkm) (hLlm0 : 0 ≤ Llm)
    (hFQhk0 : 0 ≤ FQhk) (hFQhl0 : 0 ≤ FQhl) (hFQhm0 : 0 ≤ FQhm) (hFQkl0 : 0 ≤ FQkl) (hFQkm0 : 0 ≤ FQkm) (hFQlm0 : 0 ≤ FQlm)
    (hVQ3hkr0 : 0 ≤ VQ3hkr) (hVQ3hlr0 : 0 ≤ VQ3hlr) (hVQ3hmr0 : 0 ≤ VQ3hmr) (hVQ3klr0 : 0 ≤ VQ3klr) (hVQ3kmr0 : 0 ≤ VQ3kmr) (hVQ3lmr0 : 0 ≤ VQ3lmr)
    (hCcrhk0 : 0 ≤ Ccrhk) (hCcrhl0 : 0 ≤ Ccrhl) (hCcrhm0 : 0 ≤ Ccrhm) (hCcrkl0 : 0 ≤ Ccrkl) (hCcrkm0 : 0 ≤ Ccrkm) (hCcrlm0 : 0 ≤ Ccrlm)
    (hVFqhk0 : 0 ≤ VFqhk) (hVFqhl0 : 0 ≤ VFqhl) (hVFqhm0 : 0 ≤ VFqhm) (hVFqkl0 : 0 ≤ VFqkl) (hVFqkm0 : 0 ≤ VFqkm) (hVFqlm0 : 0 ≤ VFqlm)
    (hVklm0 : 0 ≤ Vklm) (hVhlm0 : 0 ≤ Vhlm) (hVhkm0 : 0 ≤ Vhkm) (hVhkl0 : 0 ≤ Vhkl)
    (hL3klm0 : 0 ≤ L3klm) (hL3hlm0 : 0 ≤ L3hlm) (hL3hkm0 : 0 ≤ L3hkm) (hL3hkl0 : 0 ≤ L3hkl)
    (hFQ3klm0 : 0 ≤ FQ3klm) (hFQ3hlm0 : 0 ≤ FQ3hlm) (hFQ3hkm0 : 0 ≤ FQ3hkm) (hFQ3hkl0 : 0 ≤ FQ3hkl)
    (htay2 : ‖dw - dv - d2v (yw - yv)‖ ≤ L2 * (nr * eKf) ^ 2)
    (htay3 : ‖d2w - d2v - d3v (yw - yv)‖ ≤ L3 * (nr * eKf) ^ 2)
    (htay4 : ‖d3w - d3v - d4v (yw - yv)‖ ≤ L4 * (nr * eKf) ^ 2)
    (htay5 : ‖d4w - d4v - d5v (yw - yv)‖ ≤ L5 * (nr * eKf) ^ 2)
    (hacc0 : ‖yw - yv - Pr‖ ≤ C2 * nr ^ 2) (hPrn : ‖Pr‖ ≤ eKs * nr)
    (hd2n : ‖d2v‖ ≤ Kstar2) (hd3n : ‖d3v‖ ≤ Kstar3) (hd4n : ‖d4v‖ ≤ Kstar4) (hd5n : ‖d5v‖ ≤ Kstar5)
    (hqwM4 : ‖qw‖ ≤ M4)
    (hQlipTop : ‖qw - Qhklm‖ ≤ Ce0 * nr)
    (hPhV : ‖Ph‖ ≤ Vh) (hPkV : ‖Pk‖ ≤ Vk) (hPlV : ‖Pl‖ ≤ Vl) (hPmV : ‖Pm‖ ≤ Vm)
    (hPhwV : ‖Phw‖ ≤ Vh) (hPkwV : ‖Pkw‖ ≤ Vk) (hPlwV : ‖Plw‖ ≤ Vl) (hPmwV : ‖Pmw‖ ≤ Vm)
    (hδH : ‖Phw - Ph‖ ≤ Dh * nr) (hδK : ‖Pkw - Pk‖ ≤ Dk * nr)
    (hδL : ‖Plw - Pl‖ ≤ Dl * nr) (hδM : ‖Pmw - Pm‖ ≤ Dm * nr)
    (hFPh : ‖Phw - Ph - Qhr‖ ≤ Fh * nr ^ 2) (hFPk : ‖Pkw - Pk - Qkr‖ ≤ Fk * nr ^ 2)
    (hFPl : ‖Plw - Pl - Qlr‖ ≤ Fl * nr ^ 2) (hFPm : ‖Pmw - Pm - Qmr‖ ≤ Fm * nr ^ 2)
    (hVhk : ‖Qhk‖ ≤ Vhk) (hVhl : ‖Qhl‖ ≤ Vhl) (hVhm : ‖Qhm‖ ≤ Vhm)
    (hVkl : ‖Qkl‖ ≤ Vkl) (hVkm : ‖Qkm‖ ≤ Vkm) (hVlm : ‖Qlm‖ ≤ Vlm)
    (hVwhk : ‖Qwhk‖ ≤ Vhk) (hVwhl : ‖Qwhl‖ ≤ Vhl) (hVwhm : ‖Qwhm‖ ≤ Vhm)
    (hVwkl : ‖Qwkl‖ ≤ Vkl) (hVwkm : ‖Qwkm‖ ≤ Vkm) (hVwlm : ‖Qwlm‖ ≤ Vlm)
    (hQLhk : ‖Qwhk - Qhk‖ ≤ Lhk * nr) (hQLhl : ‖Qwhl - Qhl‖ ≤ Lhl * nr) (hQLhm : ‖Qwhm - Qhm‖ ≤ Lhm * nr)
    (hQLkl : ‖Qwkl - Qkl‖ ≤ Lkl * nr) (hQLkm : ‖Qwkm - Qkm‖ ≤ Lkm * nr) (hQLlm : ‖Qwlm - Qlm‖ ≤ Llm * nr)
    (hFQhk : ‖Qwhk - Qhk - Qhkr‖ ≤ FQhk * nr ^ 2) (hFQhl : ‖Qwhl - Qhl - Qhlr‖ ≤ FQhl * nr ^ 2)
    (hFQhm : ‖Qwhm - Qhm - Qhmr‖ ≤ FQhm * nr ^ 2) (hFQkl : ‖Qwkl - Qkl - Qklr‖ ≤ FQkl * nr ^ 2)
    (hFQkm : ‖Qwkm - Qkm - Qkmr‖ ≤ FQkm * nr ^ 2) (hFQlm : ‖Qwlm - Qlm - Qlmr‖ ≤ FQlm * nr ^ 2)
    (hVQhkr : ‖Qhkr‖ ≤ VQ3hkr) (hVQhlr : ‖Qhlr‖ ≤ VQ3hlr) (hVQhmr : ‖Qhmr‖ ≤ VQ3hmr)
    (hVQklr : ‖Qklr‖ ≤ VQ3klr) (hVQkmr : ‖Qkmr‖ ≤ VQ3kmr) (hVQlmr : ‖Qlmr‖ ≤ VQ3lmr)
    (hSQhkr : ‖Qhkr‖ ≤ Ccrhk * nr) (hSQhlr : ‖Qhlr‖ ≤ Ccrhl * nr) (hSQhmr : ‖Qhmr‖ ≤ Ccrhm * nr)
    (hSQklr : ‖Qklr‖ ≤ Ccrkl * nr) (hSQkmr : ‖Qkmr‖ ≤ Ccrkm * nr) (hSQlmr : ‖Qlmr‖ ≤ Ccrlm * nr)
    (hFQhkV : ‖Qwhk - Qhk - Qhkr‖ ≤ VFqhk) (hFQhlV : ‖Qwhl - Qhl - Qhlr‖ ≤ VFqhl)
    (hFQhmV : ‖Qwhm - Qhm - Qhmr‖ ≤ VFqhm) (hFQklV : ‖Qwkl - Qkl - Qklr‖ ≤ VFqkl)
    (hFQkmV : ‖Qwkm - Qkm - Qkmr‖ ≤ VFqkm) (hFQlmV : ‖Qwlm - Qlm - Qlmr‖ ≤ VFqlm)
    (hVklm : ‖Qklm‖ ≤ Vklm) (hVhlm : ‖Qhlm‖ ≤ Vhlm) (hVhkm : ‖Qhkm‖ ≤ Vhkm) (hVhkl : ‖Qhkl‖ ≤ Vhkl)
    (hVwklm : ‖Qwklm‖ ≤ Vklm) (hVwhlm : ‖Qwhlm‖ ≤ Vhlm) (hVwhkm : ‖Qwhkm‖ ≤ Vhkm) (hVwhkl : ‖Qwhkl‖ ≤ Vhkl)
    (hQL3klm : ‖Qwklm - Qklm‖ ≤ L3klm * nr) (hQL3hlm : ‖Qwhlm - Qhlm‖ ≤ L3hlm * nr)
    (hQL3hkm : ‖Qwhkm - Qhkm‖ ≤ L3hkm * nr) (hQL3hkl : ‖Qwhkl - Qhkl‖ ≤ L3hkl * nr)
    (hFQ3klm : ‖Qwklm - Qklm - Qklmr‖ ≤ FQ3klm * nr ^ 2) (hFQ3hlm : ‖Qwhlm - Qhlm - Qhlmr‖ ≤ FQ3hlm * nr ^ 2)
    (hFQ3hkm : ‖Qwhkm - Qhkm - Qhkmr‖ ≤ FQ3hkm * nr ^ 2) (hFQ3hkl : ‖Qwhkl - Qhkl - Qhklr‖ ≤ FQ3hkl * nr ^ 2)
    (hs1 : d3v Pm Qhk Qlr = d3v Qlr Pm Qhk)
    (hs2 : d3v Pl Qhk Qmr = d3v Pl Qmr Qhk)
    (hs3 : d3v Pm Qhl Qkr = d3v Qkr Pm Qhl)
    (hs4 : d3v Pk Qhl Qmr = d3v Pk Qmr Qhl)
    (hs5 : d3v Pl Qhm Qkr = d3v Qkr Pl Qhm)
    (hs6 : d3v Pk Qhm Qlr = d3v Pk Qlr Qhm)
    (hs7 : d3v Pm Qhr Qkl = d3v Qhr Pm Qkl)
    (hs8 : d3v Ph Qkl Qmr = d3v Ph Qmr Qkl)
    (hs9 : d3v Pl Qhr Qkm = d3v Qhr Pl Qkm)
    (hs10 : d3v Ph Qkm Qlr = d3v Ph Qlr Qkm)
    (hs11 : d3v Pk Qhr Qlm = d3v Qhr Pk Qlm)
    (hs12 : d2v Qlmr Qhk = d2v Qhk Qlmr)
    (hs13 : d2v Qkmr Qhl = d2v Qhl Qkmr)
    (hs14 : d2v Qklr Qhm = d2v Qhm Qklr)
    (hs15 : d2v Qklm Qhr = d2v Qhr Qklm)
    (hs16 : d2v Qhlm Qkr = d2v Qkr Qhlm)
    (hs17 : d2v Qhkm Qlr = d2v Qlr Qhkm)
    (hs18 : d2v Qhkl Qmr = d2v Qmr Qhkl)
    (hcyc5 : d5v Pr Ph Pk Pl Pm = d5v Ph Pk Pl Pm Pr)
    (hQa : d4v Qhr Pk Pl Pm = d4v Pk Pl Pm Qhr)
    (hQb : d4v Ph Qkr Pl Pm = d4v Ph Pl Pm Qkr)
    (hQc : d4v Ph Pk Qlr Pm = d4v Ph Pk Pm Qlr)
    (hcyc4_hk : d4v Pr Pl Pm Qhk = d4v Pl Pm Pr Qhk)
    (hcyc4_hl : d4v Pr Pk Pm Qhl = d4v Pk Pm Pr Qhl)
    (hcyc4_hm : d4v Pr Pk Pl Qhm = d4v Pk Pl Pr Qhm)
    (hcyc4_kl : d4v Pr Ph Pm Qkl = d4v Ph Pm Pr Qkl)
    (hcyc4_km : d4v Pr Ph Pl Qkm = d4v Ph Pl Pr Qkm)
    (hcyc4_lm : d4v Pr Ph Pk Qlm = d4v Ph Pk Pr Qlm)
    (hsA_klm : d3v Pr Ph Qklm = d3v Ph Pr Qklm)
    (hsA_hlm : d3v Pr Pk Qhlm = d3v Pk Pr Qhlm)
    (hsA_hkm : d3v Pr Pl Qhkm = d3v Pl Pr Qhkm)
    (hsA_hkl : d3v Pr Pm Qhkl = d3v Pm Pr Qhkl) :
    ‖(dw - dv) qw
      + ((d4w Phw Pkw Plw Pmw + d3w Plw Pmw Qwhk + d3w Pkw Pmw Qwhl + d3w Pkw Plw Qwhm + d3w Phw Pmw Qwkl + d3w Phw Plw Qwkm + d3w Phw Pkw Qwlm + d2w Qwhk Qwlm + d2w Qwhl Qwkm + d2w Qwhm Qwkl + d2w Phw Qwklm + d2w Pkw Qwhlm + d2w Plw Qwhkm + d2w Pmw Qwhkl)
         - (d4v Ph Pk Pl Pm + d3v Pl Pm Qhk + d3v Pk Pm Qhl + d3v Pk Pl Qhm + d3v Ph Pm Qkl + d3v Ph Pl Qkm + d3v Ph Pk Qlm + d2v Qhk Qlm + d2v Qhl Qkm + d2v Qhm Qkl + d2v Ph Qklm + d2v Pk Qhlm + d2v Pl Qhkm + d2v Pm Qhkl)
         - (d5v Ph Pk Pl Pm Pr + d4v Pl Pm Pr Qhk + d4v Pk Pm Pr Qhl + d4v Pk Pl Pr Qhm + d4v Pk Pl Pm Qhr + d4v Ph Pm Pr Qkl + d4v Ph Pl Pr Qkm + d4v Ph Pl Pm Qkr + d4v Ph Pk Pr Qlm + d4v Ph Pk Pm Qlr + d4v Ph Pk Pl Qmr + d3v Ph Qkl Qmr + d3v Ph Qkm Qlr + d3v Ph Qkr Qlm + d3v Pk Qhl Qmr + d3v Pk Qhm Qlr + d3v Pk Qhr Qlm + d3v Pl Qhk Qmr + d3v Pl Qhm Qkr + d3v Pl Qhr Qkm + d3v Pm Qhk Qlr + d3v Pm Qhl Qkr + d3v Pm Qhr Qkl + d3v Pr Qhk Qlm + d3v Pr Qhl Qkm + d3v Pr Qhm Qkl + d3v Pm Pr Qhkl + d3v Pl Pr Qhkm + d3v Pl Pm Qhkr + d3v Pk Pr Qhlm + d3v Pk Pm Qhlr + d3v Pk Pl Qhmr + d3v Ph Pr Qklm + d3v Ph Pm Qklr + d3v Ph Pl Qkmr + d3v Ph Pk Qlmr + d2v Qhkl Qmr + d2v Qhkm Qlr + d2v Qhkr Qlm + d2v Qhlm Qkr + d2v Qhlr Qkm + d2v Qhmr Qkl + d2v Qklm Qhr + d2v Qklr Qhm + d2v Qkmr Qhl + d2v Qlmr Qhk + d2v Ph Qklmr + d2v Pk Qhlmr + d2v Pl Qhkmr + d2v Pm Qhklr + d2v Pr Qhklm))‖
      ≤ (
(L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce0)
        + (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm) + Kstar5 * C2 * (Vh * Vk * Vl * Vm)
          + Kstar5 * eKs * Dh * Vk * Vl * Vm + Kstar5 * eKs * Vh * Dk * Vl * Vm
          + Kstar5 * eKs * Vh * Vk * Dl * Vm + Kstar5 * eKs * Vh * Vk * Vl * Dm
          + Kstar4 * Vh * Vk * Vl * Fm + Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Vk * Dl * Dm + 2 * Kstar4 * Vh * Vk * Fl * Vm
          + Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Dl * Vm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Vl * Dm
          + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Dk * Vl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Dl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm
          + Kstar4 * Dh * Vk * Vl * Dm + 2 * Kstar4 * Fh * Vk * Vl * Vm)
        + (L4 * eKf ^ 2 * (Vl * Vm) * Vhk + Kstar4 * C2 * (Vl * Vm) * Vhk
          + Kstar4 * eKs * Dl * Vm * Vhk + Kstar4 * eKs * Vl * Dm * Vhk
          + Kstar4 * eKs * Vl * Vm * Lhk
          + Kstar3 * Vl * Vm * FQhk
          + Kstar3 * Vl * Fm * Vhk + Kstar3 * Vl * Dm * Lhk
          + 2 * Kstar3 * Vl * Fm * Vhk
          + Kstar3 * Fl * Vm * Vhk + Kstar3 * Dl * Dm * Vhk
          + 2 * Kstar3 * Fl * Vm * Vhk + Kstar3 * Dl * Vm * Lhk
          + 2 * Kstar3 * Fl * Vm * Vhk)
        + (L4 * eKf ^ 2 * (Vk * Vm) * Vhl + Kstar4 * C2 * (Vk * Vm) * Vhl
          + Kstar4 * eKs * Dk * Vm * Vhl + Kstar4 * eKs * Vk * Dm * Vhl
          + Kstar4 * eKs * Vk * Vm * Lhl
          + Kstar3 * Vk * Vm * FQhl
          + Kstar3 * Vk * Fm * Vhl + Kstar3 * Vk * Dm * Lhl
          + 2 * Kstar3 * Vk * Fm * Vhl
          + Kstar3 * Fk * Vm * Vhl + Kstar3 * Dk * Dm * Vhl
          + 2 * Kstar3 * Fk * Vm * Vhl + Kstar3 * Dk * Vm * Lhl
          + 2 * Kstar3 * Fk * Vm * Vhl)
        + (L4 * eKf ^ 2 * (Vk * Vl) * Vhm + Kstar4 * C2 * (Vk * Vl) * Vhm
          + Kstar4 * eKs * Dk * Vl * Vhm + Kstar4 * eKs * Vk * Dl * Vhm
          + Kstar4 * eKs * Vk * Vl * Lhm
          + Kstar3 * Vk * Vl * FQhm
          + Kstar3 * Vk * Fl * Vhm + Kstar3 * Vk * Dl * Lhm
          + 2 * Kstar3 * Vk * Fl * Vhm
          + Kstar3 * Fk * Vl * Vhm + Kstar3 * Dk * Dl * Vhm
          + 2 * Kstar3 * Fk * Vl * Vhm + Kstar3 * Dk * Vl * Lhm
          + 2 * Kstar3 * Fk * Vl * Vhm)
        + (L4 * eKf ^ 2 * (Vh * Vm) * Vkl + Kstar4 * C2 * (Vh * Vm) * Vkl
          + Kstar4 * eKs * Dh * Vm * Vkl + Kstar4 * eKs * Vh * Dm * Vkl
          + Kstar4 * eKs * Vh * Vm * Lkl
          + Kstar3 * Vh * Vm * FQkl
          + Kstar3 * Vh * Fm * Vkl + Kstar3 * Vh * Dm * Lkl
          + 2 * Kstar3 * Vh * Fm * Vkl
          + Kstar3 * Fh * Vm * Vkl + Kstar3 * Dh * Dm * Vkl
          + 2 * Kstar3 * Fh * Vm * Vkl + Kstar3 * Dh * Vm * Lkl
          + 2 * Kstar3 * Fh * Vm * Vkl)
        + (L4 * eKf ^ 2 * (Vh * Vl) * Vkm + Kstar4 * C2 * (Vh * Vl) * Vkm
          + Kstar4 * eKs * Dh * Vl * Vkm + Kstar4 * eKs * Vh * Dl * Vkm
          + Kstar4 * eKs * Vh * Vl * Lkm
          + Kstar3 * Vh * Vl * FQkm
          + Kstar3 * Vh * Fl * Vkm + Kstar3 * Vh * Dl * Lkm
          + 2 * Kstar3 * Vh * Fl * Vkm
          + Kstar3 * Fh * Vl * Vkm + Kstar3 * Dh * Dl * Vkm
          + 2 * Kstar3 * Fh * Vl * Vkm + Kstar3 * Dh * Vl * Lkm
          + 2 * Kstar3 * Fh * Vl * Vkm)
        + (L4 * eKf ^ 2 * (Vh * Vk) * Vlm + Kstar4 * C2 * (Vh * Vk) * Vlm
          + Kstar4 * eKs * Dh * Vk * Vlm + Kstar4 * eKs * Vh * Dk * Vlm
          + Kstar4 * eKs * Vh * Vk * Llm
          + Kstar3 * Vh * Vk * FQlm
          + Kstar3 * Vh * Fk * Vlm + Kstar3 * Vh * Dk * Llm
          + 2 * Kstar3 * Vh * Fk * Vlm
          + Kstar3 * Fh * Vk * Vlm + Kstar3 * Dh * Dk * Vlm
          + 2 * Kstar3 * Fh * Vk * Vlm + Kstar3 * Dh * Vk * Llm
          + 2 * Kstar3 * Fh * Vk * Vlm)
        + (L3 * eKf ^ 2 * (Vhk * Vlm) + Kstar3 * C2 * (Vhk * Vlm)
          + Kstar3 * eKs * Lhk * Vlm + Kstar3 * eKs * Vhk * Llm
          + Kstar2 * Vhk * FQlm + Kstar2 * Ccrhk * Ccrlm + Kstar2 * VQ3hkr * FQlm
          + Kstar2 * FQhk * Vlm + Kstar2 * FQhk * VQ3lmr + Kstar2 * FQhk * VFqlm)
        + (L3 * eKf ^ 2 * (Vhl * Vkm) + Kstar3 * C2 * (Vhl * Vkm)
          + Kstar3 * eKs * Lhl * Vkm + Kstar3 * eKs * Vhl * Lkm
          + Kstar2 * Vhl * FQkm + Kstar2 * Ccrhl * Ccrkm + Kstar2 * VQ3hlr * FQkm
          + Kstar2 * FQhl * Vkm + Kstar2 * FQhl * VQ3kmr + Kstar2 * FQhl * VFqkm)
        + (L3 * eKf ^ 2 * (Vhm * Vkl) + Kstar3 * C2 * (Vhm * Vkl)
          + Kstar3 * eKs * Lhm * Vkl + Kstar3 * eKs * Vhm * Lkl
          + Kstar2 * Vhm * FQkl + Kstar2 * Ccrhm * Ccrkl + Kstar2 * VQ3hmr * FQkl
          + Kstar2 * FQhm * Vkl + Kstar2 * FQhm * VQ3klr + Kstar2 * FQhm * VFqkl)
        + (L3 * eKf ^ 2 * (Vh * Vklm) + Kstar3 * C2 * (Vh * Vklm)
          + Kstar3 * eKs * Dh * Vklm + Kstar3 * eKs * Vh * L3klm
          + Kstar2 * Dh * L3klm + 2 * Kstar2 * Fh * Vklm
          + Kstar2 * Fh * Vklm + Kstar2 * Vh * FQ3klm)
        + (L3 * eKf ^ 2 * (Vk * Vhlm) + Kstar3 * C2 * (Vk * Vhlm)
          + Kstar3 * eKs * Dk * Vhlm + Kstar3 * eKs * Vk * L3hlm
          + Kstar2 * Dk * L3hlm + 2 * Kstar2 * Fk * Vhlm
          + Kstar2 * Fk * Vhlm + Kstar2 * Vk * FQ3hlm)
        + (L3 * eKf ^ 2 * (Vl * Vhkm) + Kstar3 * C2 * (Vl * Vhkm)
          + Kstar3 * eKs * Dl * Vhkm + Kstar3 * eKs * Vl * L3hkm
          + Kstar2 * Dl * L3hkm + 2 * Kstar2 * Fl * Vhkm
          + Kstar2 * Fl * Vhkm + Kstar2 * Vl * FQ3hkm)
        + (L3 * eKf ^ 2 * (Vm * Vhkl) + Kstar3 * C2 * (Vm * Vhkl)
          + Kstar3 * eKs * Dm * Vhkl + Kstar3 * eKs * Vm * L3hkl
          + Kstar2 * Dm * L3hkl + 2 * Kstar2 * Fm * Vhkl
          + Kstar2 * Fm * Vhkl + Kstar2 * Vm * FQ3hkl)) * nr ^ 2 := by
  rw [remMaster_identity dv dw d2v d2w d3v d3w d4v d4w d5v qw Pr Ph Pk Pl Pm Phw Pkw Plw Pmw Qhk Qhl Qhm Qkl Qkm Qlm Qhr Qkr Qlr Qmr Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qhkl Qhkm Qhlm Qklm Qhkr Qhlr Qhmr Qklr Qkmr Qlmr Qwhkl Qwhkm Qwhlm Qwklm Qhklm Qhklr Qhkmr Qhlmr Qklmr
    hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18]
  have hbk0 := remBlk0_bound d2v dw dv yw yv qw Qhklm Pr nr L2 eKf M4 C2 Ce0 eKs Kstar2
    hnr0 hL2_0 hM40 hC2_0 hCe00 heKs0 hKstar20 htay2 hqwM4 hd2n hacc0 hPrn hQlipTop
  have hbktop := remBlkTop_bound_dir d5v d4v d4w Ph Pk Pl Pm Phw Pkw Plw Pmw Pr Qhr Qkr Qlr Qmr (yw - yv)
    nr eKf eKs L5 C2 Kstar5 Kstar4 Vh Vk Vl Vm Dh Dk Dl Dm Fh Fk Fl Fm
    hnr0 heKf0 heKs0 hL5_0 hC2_0 hKstar50 hKstar40 hVh0 hVk0 hVl0 hVm0 hDh0 hDk0 hDl0 hDm0 hFh0 hFk0 hFl0 hFm0
    hcyc5 hQa hQb hQc htay5 hd5n hd4n hacc0 hPrn
    hPhV hPkV hPlV hPmV hPhwV hPkwV hPlwV hPmwV hδH hδK hδL hδM hFPh hFPk hFPl hFPm
  have hbk211_hk := remBlk211_bound_dir d4v d3v d3w Pl Pm Plw Pmw Pr Qlr Qmr Qhk Qwhk Qhkr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vl Vm Vhk Dl Dm Lhk Fl Fm FQhk
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVl0 hVm0 hVhk0 hDl0 hDm0 hLhk0 hFl0 hFm0 hFQhk0
    hcyc4_hk htay4 hd4n hd3n hacc0 hPrn hPlV hPmV hPlwV hPmwV
    hVhk hVwhk hδL hδM hQLhk hFPl hFPm hFQhk
  have hbk211_hl := remBlk211_bound_dir d4v d3v d3w Pk Pm Pkw Pmw Pr Qkr Qmr Qhl Qwhl Qhlr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vk Vm Vhl Dk Dm Lhl Fk Fm FQhl
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVk0 hVm0 hVhl0 hDk0 hDm0 hLhl0 hFk0 hFm0 hFQhl0
    hcyc4_hl htay4 hd4n hd3n hacc0 hPrn hPkV hPmV hPkwV hPmwV
    hVhl hVwhl hδK hδM hQLhl hFPk hFPm hFQhl
  have hbk211_hm := remBlk211_bound_dir d4v d3v d3w Pk Pl Pkw Plw Pr Qkr Qlr Qhm Qwhm Qhmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vk Vl Vhm Dk Dl Lhm Fk Fl FQhm
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVk0 hVl0 hVhm0 hDk0 hDl0 hLhm0 hFk0 hFl0 hFQhm0
    hcyc4_hm htay4 hd4n hd3n hacc0 hPrn hPkV hPlV hPkwV hPlwV
    hVhm hVwhm hδK hδL hQLhm hFPk hFPl hFQhm
  have hbk211_kl := remBlk211_bound_dir d4v d3v d3w Ph Pm Phw Pmw Pr Qhr Qmr Qkl Qwkl Qklr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vh Vm Vkl Dh Dm Lkl Fh Fm FQkl
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVh0 hVm0 hVkl0 hDh0 hDm0 hLkl0 hFh0 hFm0 hFQkl0
    hcyc4_kl htay4 hd4n hd3n hacc0 hPrn hPhV hPmV hPhwV hPmwV
    hVkl hVwkl hδH hδM hQLkl hFPh hFPm hFQkl
  have hbk211_km := remBlk211_bound_dir d4v d3v d3w Ph Pl Phw Plw Pr Qhr Qlr Qkm Qwkm Qkmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vh Vl Vkm Dh Dl Lkm Fh Fl FQkm
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVh0 hVl0 hVkm0 hDh0 hDl0 hLkm0 hFh0 hFl0 hFQkm0
    hcyc4_km htay4 hd4n hd3n hacc0 hPrn hPhV hPlV hPhwV hPlwV
    hVkm hVwkm hδH hδL hQLkm hFPh hFPl hFQkm
  have hbk211_lm := remBlk211_bound_dir d4v d3v d3w Ph Pk Phw Pkw Pr Qhr Qkr Qlm Qwlm Qlmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 Vh Vk Vlm Dh Dk Llm Fh Fk FQlm
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hVh0 hVk0 hVlm0 hDh0 hDk0 hLlm0 hFh0 hFk0 hFQlm0
    hcyc4_lm htay4 hd4n hd3n hacc0 hPrn hPhV hPkV hPhwV hPkwV
    hVlm hVwlm hδH hδK hQLlm hFPh hFPk hFQlm
  have hbk22_hk := remBlk22_bound_dir d3v d2v d2w Pr Qhk Qlm Qwhk Qwlm Qhkr Qlmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vhk Vlm VQ3hkr VQ3lmr VFqhk VFqlm Ccrhk Ccrlm Lhk Llm FQhk FQlm
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVhk0 hVlm0 hVQ3hkr0 hVQ3lmr0 hVFqhk0 hVFqlm0 hCcrhk0 hCcrlm0 hLhk0 hLlm0 hFQhk0 hFQlm0
    htay3 hd3n hd2n hacc0 hPrn hVhk hVlm hVwhk hVwlm
    hVQhkr hVQlmr hSQhkr hSQlmr hQLhk hQLlm hFQhkV hFQlmV hFQhk hFQlm
  have hbk22_hl := remBlk22_bound_dir d3v d2v d2w Pr Qhl Qkm Qwhl Qwkm Qhlr Qkmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vhl Vkm VQ3hlr VQ3kmr VFqhl VFqkm Ccrhl Ccrkm Lhl Lkm FQhl FQkm
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVhl0 hVkm0 hVQ3hlr0 hVQ3kmr0 hVFqhl0 hVFqkm0 hCcrhl0 hCcrkm0 hLhl0 hLkm0 hFQhl0 hFQkm0
    htay3 hd3n hd2n hacc0 hPrn hVhl hVkm hVwhl hVwkm
    hVQhlr hVQkmr hSQhlr hSQkmr hQLhl hQLkm hFQhlV hFQkmV hFQhl hFQkm
  have hbk22_hm := remBlk22_bound_dir d3v d2v d2w Pr Qhm Qkl Qwhm Qwkl Qhmr Qklr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vhm Vkl VQ3hmr VQ3klr VFqhm VFqkl Ccrhm Ccrkl Lhm Lkl FQhm FQkl
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVhm0 hVkl0 hVQ3hmr0 hVQ3klr0 hVFqhm0 hVFqkl0 hCcrhm0 hCcrkl0 hLhm0 hLkl0 hFQhm0 hFQkl0
    htay3 hd3n hd2n hacc0 hPrn hVhm hVkl hVwhm hVwkl
    hVQhmr hVQklr hSQhmr hSQklr hQLhm hQLkl hFQhmV hFQklV hFQhm hFQkl
  have hbk31_klm := remBlk31_bound_dir d3v d2v d2w Ph Phw Pr Qhr Qklm Qwklm Qklmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vh Vklm Dh L3klm Fh FQ3klm
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVh0 hVklm0 hDh0 hL3klm0 hFh0 hFQ3klm0
    hsA_klm htay3 hd3n hd2n hacc0 hPrn hPhV hPhwV hVklm hVwklm hδH hQL3klm hFPh hFQ3klm
  have hbk31_hlm := remBlk31_bound_dir d3v d2v d2w Pk Pkw Pr Qkr Qhlm Qwhlm Qhlmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vk Vhlm Dk L3hlm Fk FQ3hlm
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVk0 hVhlm0 hDk0 hL3hlm0 hFk0 hFQ3hlm0
    hsA_hlm htay3 hd3n hd2n hacc0 hPrn hPkV hPkwV hVhlm hVwhlm hδK hQL3hlm hFPk hFQ3hlm
  have hbk31_hkm := remBlk31_bound_dir d3v d2v d2w Pl Plw Pr Qlr Qhkm Qwhkm Qhkmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vl Vhkm Dl L3hkm Fl FQ3hkm
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVl0 hVhkm0 hDl0 hL3hkm0 hFl0 hFQ3hkm0
    hsA_hkm htay3 hd3n hd2n hacc0 hPrn hPlV hPlwV hVhkm hVwhkm hδL hQL3hkm hFPl hFQ3hkm
  have hbk31_hkl := remBlk31_bound_dir d3v d2v d2w Pm Pmw Pr Qmr Qhkl Qwhkl Qhklr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Vm Vhkl Dm L3hkl Fm FQ3hkl
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hVm0 hVhkl0 hDm0 hL3hkl0 hFm0 hFQ3hkl0
    hsA_hkl htay3 hd3n hd2n hacc0 hPrn hPmV hPmwV hVhkl hVwhkl hδM hQL3hkl hFPm hFQ3hkl
  rw [distrib15_nr (L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce0) (L5 * eKf ^ 2 * (Vh * Vk * Vl * Vm) + Kstar5 * C2 * (Vh * Vk * Vl * Vm) + Kstar5 * eKs * Dh * Vk * Vl * Vm + Kstar5 * eKs * Vh * Dk * Vl * Vm + Kstar5 * eKs * Vh * Vk * Dl * Vm + Kstar5 * eKs * Vh * Vk * Vl * Dm + Kstar4 * Vh * Vk * Vl * Fm + Kstar4 * Vh * Vk * Fl * Vm + Kstar4 * Vh * Vk * Dl * Dm + 2 * Kstar4 * Vh * Vk * Fl * Vm + Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Dl * Vm + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Vh * Dk * Vl * Dm + 2 * Kstar4 * Vh * Fk * Vl * Vm + Kstar4 * Fh * Vk * Vl * Vm + Kstar4 * Dh * Dk * Vl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm + Kstar4 * Dh * Vk * Dl * Vm + 2 * Kstar4 * Fh * Vk * Vl * Vm + Kstar4 * Dh * Vk * Vl * Dm + 2 * Kstar4 * Fh * Vk * Vl * Vm) (L4 * eKf ^ 2 * (Vl * Vm) * Vhk + Kstar4 * C2 * (Vl * Vm) * Vhk + Kstar4 * eKs * Dl * Vm * Vhk + Kstar4 * eKs * Vl * Dm * Vhk + Kstar4 * eKs * Vl * Vm * Lhk + Kstar3 * Vl * Vm * FQhk + Kstar3 * Vl * Fm * Vhk + Kstar3 * Vl * Dm * Lhk + 2 * Kstar3 * Vl * Fm * Vhk + Kstar3 * Fl * Vm * Vhk + Kstar3 * Dl * Dm * Vhk + 2 * Kstar3 * Fl * Vm * Vhk + Kstar3 * Dl * Vm * Lhk + 2 * Kstar3 * Fl * Vm * Vhk) (L4 * eKf ^ 2 * (Vk * Vm) * Vhl + Kstar4 * C2 * (Vk * Vm) * Vhl + Kstar4 * eKs * Dk * Vm * Vhl + Kstar4 * eKs * Vk * Dm * Vhl + Kstar4 * eKs * Vk * Vm * Lhl + Kstar3 * Vk * Vm * FQhl + Kstar3 * Vk * Fm * Vhl + Kstar3 * Vk * Dm * Lhl + 2 * Kstar3 * Vk * Fm * Vhl + Kstar3 * Fk * Vm * Vhl + Kstar3 * Dk * Dm * Vhl + 2 * Kstar3 * Fk * Vm * Vhl + Kstar3 * Dk * Vm * Lhl + 2 * Kstar3 * Fk * Vm * Vhl) (L4 * eKf ^ 2 * (Vk * Vl) * Vhm + Kstar4 * C2 * (Vk * Vl) * Vhm + Kstar4 * eKs * Dk * Vl * Vhm + Kstar4 * eKs * Vk * Dl * Vhm + Kstar4 * eKs * Vk * Vl * Lhm + Kstar3 * Vk * Vl * FQhm + Kstar3 * Vk * Fl * Vhm + Kstar3 * Vk * Dl * Lhm + 2 * Kstar3 * Vk * Fl * Vhm + Kstar3 * Fk * Vl * Vhm + Kstar3 * Dk * Dl * Vhm + 2 * Kstar3 * Fk * Vl * Vhm + Kstar3 * Dk * Vl * Lhm + 2 * Kstar3 * Fk * Vl * Vhm) (L4 * eKf ^ 2 * (Vh * Vm) * Vkl + Kstar4 * C2 * (Vh * Vm) * Vkl + Kstar4 * eKs * Dh * Vm * Vkl + Kstar4 * eKs * Vh * Dm * Vkl + Kstar4 * eKs * Vh * Vm * Lkl + Kstar3 * Vh * Vm * FQkl + Kstar3 * Vh * Fm * Vkl + Kstar3 * Vh * Dm * Lkl + 2 * Kstar3 * Vh * Fm * Vkl + Kstar3 * Fh * Vm * Vkl + Kstar3 * Dh * Dm * Vkl + 2 * Kstar3 * Fh * Vm * Vkl + Kstar3 * Dh * Vm * Lkl + 2 * Kstar3 * Fh * Vm * Vkl) (L4 * eKf ^ 2 * (Vh * Vl) * Vkm + Kstar4 * C2 * (Vh * Vl) * Vkm + Kstar4 * eKs * Dh * Vl * Vkm + Kstar4 * eKs * Vh * Dl * Vkm + Kstar4 * eKs * Vh * Vl * Lkm + Kstar3 * Vh * Vl * FQkm + Kstar3 * Vh * Fl * Vkm + Kstar3 * Vh * Dl * Lkm + 2 * Kstar3 * Vh * Fl * Vkm + Kstar3 * Fh * Vl * Vkm + Kstar3 * Dh * Dl * Vkm + 2 * Kstar3 * Fh * Vl * Vkm + Kstar3 * Dh * Vl * Lkm + 2 * Kstar3 * Fh * Vl * Vkm) (L4 * eKf ^ 2 * (Vh * Vk) * Vlm + Kstar4 * C2 * (Vh * Vk) * Vlm + Kstar4 * eKs * Dh * Vk * Vlm + Kstar4 * eKs * Vh * Dk * Vlm + Kstar4 * eKs * Vh * Vk * Llm + Kstar3 * Vh * Vk * FQlm + Kstar3 * Vh * Fk * Vlm + Kstar3 * Vh * Dk * Llm + 2 * Kstar3 * Vh * Fk * Vlm + Kstar3 * Fh * Vk * Vlm + Kstar3 * Dh * Dk * Vlm + 2 * Kstar3 * Fh * Vk * Vlm + Kstar3 * Dh * Vk * Llm + 2 * Kstar3 * Fh * Vk * Vlm) (L3 * eKf ^ 2 * (Vhk * Vlm) + Kstar3 * C2 * (Vhk * Vlm) + Kstar3 * eKs * Lhk * Vlm + Kstar3 * eKs * Vhk * Llm + Kstar2 * Vhk * FQlm + Kstar2 * Ccrhk * Ccrlm + Kstar2 * VQ3hkr * FQlm + Kstar2 * FQhk * Vlm + Kstar2 * FQhk * VQ3lmr + Kstar2 * FQhk * VFqlm) (L3 * eKf ^ 2 * (Vhl * Vkm) + Kstar3 * C2 * (Vhl * Vkm) + Kstar3 * eKs * Lhl * Vkm + Kstar3 * eKs * Vhl * Lkm + Kstar2 * Vhl * FQkm + Kstar2 * Ccrhl * Ccrkm + Kstar2 * VQ3hlr * FQkm + Kstar2 * FQhl * Vkm + Kstar2 * FQhl * VQ3kmr + Kstar2 * FQhl * VFqkm) (L3 * eKf ^ 2 * (Vhm * Vkl) + Kstar3 * C2 * (Vhm * Vkl) + Kstar3 * eKs * Lhm * Vkl + Kstar3 * eKs * Vhm * Lkl + Kstar2 * Vhm * FQkl + Kstar2 * Ccrhm * Ccrkl + Kstar2 * VQ3hmr * FQkl + Kstar2 * FQhm * Vkl + Kstar2 * FQhm * VQ3klr + Kstar2 * FQhm * VFqkl) (L3 * eKf ^ 2 * (Vh * Vklm) + Kstar3 * C2 * (Vh * Vklm) + Kstar3 * eKs * Dh * Vklm + Kstar3 * eKs * Vh * L3klm + Kstar2 * Dh * L3klm + 2 * Kstar2 * Fh * Vklm + Kstar2 * Fh * Vklm + Kstar2 * Vh * FQ3klm) (L3 * eKf ^ 2 * (Vk * Vhlm) + Kstar3 * C2 * (Vk * Vhlm) + Kstar3 * eKs * Dk * Vhlm + Kstar3 * eKs * Vk * L3hlm + Kstar2 * Dk * L3hlm + 2 * Kstar2 * Fk * Vhlm + Kstar2 * Fk * Vhlm + Kstar2 * Vk * FQ3hlm) (L3 * eKf ^ 2 * (Vl * Vhkm) + Kstar3 * C2 * (Vl * Vhkm) + Kstar3 * eKs * Dl * Vhkm + Kstar3 * eKs * Vl * L3hkm + Kstar2 * Dl * L3hkm + 2 * Kstar2 * Fl * Vhkm + Kstar2 * Fl * Vhkm + Kstar2 * Vl * FQ3hkm) (L3 * eKf ^ 2 * (Vm * Vhkl) + Kstar3 * C2 * (Vm * Vhkl) + Kstar3 * eKs * Dm * Vhkl + Kstar3 * eKs * Vm * L3hkl + Kstar2 * Dm * L3hkl + 2 * Kstar2 * Fm * Vhkl + Kstar2 * Fm * Vhkl + Kstar2 * Vm * FQ3hkl) (nr ^ 2)]
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk31_hkl)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk31_hkm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk31_hlm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk31_klm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk22_hm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk22_hl)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk22_hk)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_lm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_km)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_kl)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_hm)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_hl)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbk211_hk)
  exact (norm_add_le _ _).trans (add_le_add hbk0 hbktop)

end QIQTH.ExpMap
