/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderA

/-!
# Jet_5 quadratic-remainder — abstract assembly lemma (rung J5-5b, file B)

Banks `remAssembly`: over an abstract normed space with opaque multilinear atoms, the order-5 residual
head `(dw − dv) qw + (Θ₄w − Θ₄v − Θ₅v)` is bounded by `Cfull · nr²`, given all the tube-analytic data
(Taylor/accuracy/operator-norm/value/two-point/Lipschitz/residual bounds and the argument-permutation
symmetries) carried as hypotheses.  Proof: the abstract reassembly `remMaster_identity` then the
fifteen abstract block-shape bounds then a triangle assembly.  Opaque atoms → no fderiv `whnf`; the
heavy master `abel` lives in `remMaster_identity`.  Splitting the assembly off the concrete main
theorem keeps each Lean command inside one heartbeat budget.

## Honest firewall (binding)

Pure functional-analysis assembly ONLY.  Does NOT reach `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`,
`κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxHeartbeats 6400000
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abstract order-5 quadratic-remainder assembly.** -/
theorem remAssembly
    (dv dw : E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (d3v d3w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d4v d4w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d5v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (qw Pr Ph Pk Pl Pm Phw Pkw Plw Pmw Qhk Qhl Qhm Qkl Qkm Qlm Qhr Qkr Qlr Qmr Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qhkl Qhkm Qhlm Qklm Qhkr Qhlr Qhmr Qklr Qkmr Qlmr Qwhkl Qwhkm Qwhlm Qwklm Qhklm Qhklr Qhkmr Qhlmr Qklmr yv yw : E)
    (nr eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5 V Ddel Cd Ce Cq2 Cq3 Ccr VFq M4 : ℝ)
    (hnr0 : 0 ≤ nr) (heKf0 : 0 ≤ eKf) (heKs0 : 0 ≤ eKs)
    (hL2_0 : 0 ≤ L2) (hL3_0 : 0 ≤ L3) (hL4_0 : 0 ≤ L4) (hL5_0 : 0 ≤ L5)
    (hC2_0 : 0 ≤ C2) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3)
    (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5) (hV0 : 0 ≤ V) (hDdel0 : 0 ≤ Ddel)
    (hCd0 : 0 ≤ Cd) (hCe0 : 0 ≤ Ce) (hCq20 : 0 ≤ Cq2) (hCq30 : 0 ≤ Cq3)
    (hCcr0 : 0 ≤ Ccr) (hVFq0 : 0 ≤ VFq) (hM40 : 0 ≤ M4)
    (htay2 : ‖dw - dv - d2v (yw - yv)‖ ≤ L2 * (nr * eKf) ^ 2)
    (htay3 : ‖d2w - d2v - d3v (yw - yv)‖ ≤ L3 * (nr * eKf) ^ 2)
    (htay4 : ‖d3w - d3v - d4v (yw - yv)‖ ≤ L4 * (nr * eKf) ^ 2)
    (htay5 : ‖d4w - d4v - d5v (yw - yv)‖ ≤ L5 * (nr * eKf) ^ 2)
    (hacc0 : ‖yw - yv - Pr‖ ≤ C2 * nr ^ 2) (hPrn : ‖Pr‖ ≤ eKs * nr)
    (hd2n : ‖d2v‖ ≤ Kstar2) (hd3n : ‖d3v‖ ≤ Kstar3) (hd4n : ‖d4v‖ ≤ Kstar4) (hd5n : ‖d5v‖ ≤ Kstar5)
    (hPhV : ‖Ph‖ ≤ V)
    (hPkV : ‖Pk‖ ≤ V)
    (hPlV : ‖Pl‖ ≤ V)
    (hPmV : ‖Pm‖ ≤ V)
    (hPhwV : ‖Phw‖ ≤ V)
    (hPkwV : ‖Pkw‖ ≤ V)
    (hPlwV : ‖Plw‖ ≤ V)
    (hPmwV : ‖Pmw‖ ≤ V)
    (hVhk : ‖Qhk‖ ≤ Cq2)
    (hVhl : ‖Qhl‖ ≤ Cq2)
    (hVhm : ‖Qhm‖ ≤ Cq2)
    (hVkl : ‖Qkl‖ ≤ Cq2)
    (hVkm : ‖Qkm‖ ≤ Cq2)
    (hVlm : ‖Qlm‖ ≤ Cq2)
    (hVwhk : ‖Qwhk‖ ≤ Cq2)
    (hVwhl : ‖Qwhl‖ ≤ Cq2)
    (hVwhm : ‖Qwhm‖ ≤ Cq2)
    (hVwkl : ‖Qwkl‖ ≤ Cq2)
    (hVwkm : ‖Qwkm‖ ≤ Cq2)
    (hVwlm : ‖Qwlm‖ ≤ Cq2)
    (hVklm : ‖Qklm‖ ≤ Cq3)
    (hVhlm : ‖Qhlm‖ ≤ Cq3)
    (hVhkm : ‖Qhkm‖ ≤ Cq3)
    (hVhkl : ‖Qhkl‖ ≤ Cq3)
    (hVwklm : ‖Qwklm‖ ≤ Cq3)
    (hVwhlm : ‖Qwhlm‖ ≤ Cq3)
    (hVwhkm : ‖Qwhkm‖ ≤ Cq3)
    (hVwhkl : ‖Qwhkl‖ ≤ Cq3)
    (hVQhkr : ‖Qhkr‖ ≤ Cq3)
    (hVQhlr : ‖Qhlr‖ ≤ Cq3)
    (hVQhmr : ‖Qhmr‖ ≤ Cq3)
    (hVQklr : ‖Qklr‖ ≤ Cq3)
    (hVQkmr : ‖Qkmr‖ ≤ Cq3)
    (hVQlmr : ‖Qlmr‖ ≤ Cq3)
    (hδH : ‖Phw - Ph‖ ≤ Ddel * nr)
    (hδK : ‖Pkw - Pk‖ ≤ Ddel * nr)
    (hδL : ‖Plw - Pl‖ ≤ Ddel * nr)
    (hδM : ‖Pmw - Pm‖ ≤ Ddel * nr)
    (hQlipTop : ‖qw - Qhklm‖ ≤ Ce * nr)
    (hQLhk : ‖Qwhk - Qhk‖ ≤ Ce * nr)
    (hQLhl : ‖Qwhl - Qhl‖ ≤ Ce * nr)
    (hQLhm : ‖Qwhm - Qhm‖ ≤ Ce * nr)
    (hQLkl : ‖Qwkl - Qkl‖ ≤ Ce * nr)
    (hQLkm : ‖Qwkm - Qkm‖ ≤ Ce * nr)
    (hQLlm : ‖Qwlm - Qlm‖ ≤ Ce * nr)
    (hQL3klm : ‖Qwklm - Qklm‖ ≤ Ce * nr)
    (hQL3hlm : ‖Qwhlm - Qhlm‖ ≤ Ce * nr)
    (hQL3hkm : ‖Qwhkm - Qhkm‖ ≤ Ce * nr)
    (hQL3hkl : ‖Qwhkl - Qhkl‖ ≤ Ce * nr)
    (hFPh : ‖Phw - Ph - Qhr‖ ≤ Cd * nr ^ 2)
    (hFPk : ‖Pkw - Pk - Qkr‖ ≤ Cd * nr ^ 2)
    (hFPl : ‖Plw - Pl - Qlr‖ ≤ Cd * nr ^ 2)
    (hFPm : ‖Pmw - Pm - Qmr‖ ≤ Cd * nr ^ 2)
    (hFQhk : ‖Qwhk - Qhk - Qhkr‖ ≤ Cd * nr ^ 2)
    (hFQhl : ‖Qwhl - Qhl - Qhlr‖ ≤ Cd * nr ^ 2)
    (hFQhm : ‖Qwhm - Qhm - Qhmr‖ ≤ Cd * nr ^ 2)
    (hFQkl : ‖Qwkl - Qkl - Qklr‖ ≤ Cd * nr ^ 2)
    (hFQkm : ‖Qwkm - Qkm - Qkmr‖ ≤ Cd * nr ^ 2)
    (hFQlm : ‖Qwlm - Qlm - Qlmr‖ ≤ Cd * nr ^ 2)
    (hFQ3klm : ‖Qwklm - Qklm - Qklmr‖ ≤ Cd * nr ^ 2)
    (hFQ3hlm : ‖Qwhlm - Qhlm - Qhlmr‖ ≤ Cd * nr ^ 2)
    (hFQ3hkm : ‖Qwhkm - Qhkm - Qhkmr‖ ≤ Cd * nr ^ 2)
    (hFQ3hkl : ‖Qwhkl - Qhkl - Qhklr‖ ≤ Cd * nr ^ 2)
    (hSQhkr : ‖Qhkr‖ ≤ Ccr * nr)
    (hSQhlr : ‖Qhlr‖ ≤ Ccr * nr)
    (hSQhmr : ‖Qhmr‖ ≤ Ccr * nr)
    (hSQklr : ‖Qklr‖ ≤ Ccr * nr)
    (hSQkmr : ‖Qkmr‖ ≤ Ccr * nr)
    (hSQlmr : ‖Qlmr‖ ≤ Ccr * nr)
    (hFQhkV : ‖Qwhk - Qhk - Qhkr‖ ≤ VFq)
    (hFQhlV : ‖Qwhl - Qhl - Qhlr‖ ≤ VFq)
    (hFQhmV : ‖Qwhm - Qhm - Qhmr‖ ≤ VFq)
    (hFQklV : ‖Qwkl - Qkl - Qklr‖ ≤ VFq)
    (hFQkmV : ‖Qwkm - Qkm - Qkmr‖ ≤ VFq)
    (hFQlmV : ‖Qwlm - Qlm - Qlmr‖ ≤ VFq)
    (hqwM4 : ‖qw‖ ≤ M4)
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
      ≤ ((L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce)
      + (L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd)
      + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd)
      + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq)
      + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd)) * nr ^ 2 := by
  rw [remMaster_identity dv dw d2v d2w d3v d3w d4v d4w d5v qw Pr Ph Pk Pl Pm Phw Pkw Plw Pmw Qhk Qhl Qhm Qkl Qkm Qlm Qhr Qkr Qlr Qmr Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qhkl Qhkm Qhlm Qklm Qhkr Qhlr Qhmr Qklr Qkmr Qlmr Qwhkl Qwhkm Qwhlm Qwklm Qhklm Qhklr Qhkmr Qhlmr Qklmr
    hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs17 hs18]
  have hbk0 := remBlk0_bound d2v dw dv yw yv qw Qhklm Pr nr L2 eKf M4 C2 Ce eKs Kstar2
    hnr0 hL2_0 hM40 hC2_0 hCe0 heKs0 hKstar20 htay2 hqwM4 hd2n hacc0 hPrn hQlipTop
  have hbktop := remBlkTop_bound d5v d4v d4w Ph Pk Pl Pm Phw Pkw Plw Pmw Pr Qhr Qkr Qlr Qmr (yw - yv)
    nr eKf eKs L5 C2 Kstar5 Kstar4 V Ddel Cd
    hnr0 heKf0 heKs0 hL5_0 hC2_0 hKstar50 hKstar40 hV0 hDdel0 hCd0
    hcyc5 hQa hQb hQc htay5 hd5n hd4n hacc0 hPrn
    hPhV hPkV hPlV hPmV hPhwV hPkwV hPlwV hPmwV hδH hδK hδL hδM hFPh hFPk hFPl hFPm
  have hbk211_hk := remBlk211_bound d4v d3v d3w Pl Pm Plw Pmw Pr Qlr Qmr Qhk Qwhk Qhkr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_hk htay4 hd4n hd3n hacc0 hPrn hPlV hPmV hPlwV hPmwV
    hVhk hVwhk hδL hδM hQLhk hFPl hFPm hFQhk
  have hbk211_hl := remBlk211_bound d4v d3v d3w Pk Pm Pkw Pmw Pr Qkr Qmr Qhl Qwhl Qhlr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_hl htay4 hd4n hd3n hacc0 hPrn hPkV hPmV hPkwV hPmwV
    hVhl hVwhl hδK hδM hQLhl hFPk hFPm hFQhl
  have hbk211_hm := remBlk211_bound d4v d3v d3w Pk Pl Pkw Plw Pr Qkr Qlr Qhm Qwhm Qhmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_hm htay4 hd4n hd3n hacc0 hPrn hPkV hPlV hPkwV hPlwV
    hVhm hVwhm hδK hδL hQLhm hFPk hFPl hFQhm
  have hbk211_kl := remBlk211_bound d4v d3v d3w Ph Pm Phw Pmw Pr Qhr Qmr Qkl Qwkl Qklr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_kl htay4 hd4n hd3n hacc0 hPrn hPhV hPmV hPhwV hPmwV
    hVkl hVwkl hδH hδM hQLkl hFPh hFPm hFQkl
  have hbk211_km := remBlk211_bound d4v d3v d3w Ph Pl Phw Plw Pr Qhr Qlr Qkm Qwkm Qkmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_km htay4 hd4n hd3n hacc0 hPrn hPhV hPlV hPhwV hPlwV
    hVkm hVwkm hδH hδL hQLkm hFPh hFPl hFQkm
  have hbk211_lm := remBlk211_bound d4v d3v d3w Ph Pk Phw Pkw Pr Qhr Qkr Qlm Qwlm Qlmr (yw - yv)
    nr eKf eKs L4 C2 Kstar4 Kstar3 V Cq2 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL4_0 hC2_0 hKstar40 hKstar30 hV0 hCq20 hDdel0 hCe0 hCd0 hCd0
    hcyc4_lm htay4 hd4n hd3n hacc0 hPrn hPhV hPkV hPhwV hPkwV
    hVlm hVwlm hδH hδK hQLlm hFPh hFPk hFQlm
  have hbk22_hk := remBlk22_bound d3v d2v d2w Pr Qhk Qlm Qwhk Qwlm Qhkr Qlmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Cq2 Cq3 VFq Ccr Ce Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hCq20 hCq30 hVFq0 hCcr0 hCe0 hCd0
    htay3 hd3n hd2n hacc0 hPrn hVhk hVlm hVwhk hVwlm
    hVQhkr hVQlmr hSQhkr hSQlmr hQLhk hQLlm hFQhkV hFQlmV hFQhk hFQlm
  have hbk22_hl := remBlk22_bound d3v d2v d2w Pr Qhl Qkm Qwhl Qwkm Qhlr Qkmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Cq2 Cq3 VFq Ccr Ce Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hCq20 hCq30 hVFq0 hCcr0 hCe0 hCd0
    htay3 hd3n hd2n hacc0 hPrn hVhl hVkm hVwhl hVwkm
    hVQhlr hVQkmr hSQhlr hSQkmr hQLhl hQLkm hFQhlV hFQkmV hFQhl hFQkm
  have hbk22_hm := remBlk22_bound d3v d2v d2w Pr Qhm Qkl Qwhm Qwkl Qhmr Qklr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 Cq2 Cq3 VFq Ccr Ce Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hCq20 hCq30 hVFq0 hCcr0 hCe0 hCd0
    htay3 hd3n hd2n hacc0 hPrn hVhm hVkl hVwhm hVwkl
    hVQhmr hVQklr hSQhmr hSQklr hQLhm hQLkl hFQhmV hFQklV hFQhm hFQkl
  have hbk31_klm := remBlk31_bound d3v d2v d2w Ph Phw Pr Qhr Qklm Qwklm Qklmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 V Cq3 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hV0 hCq30 hDdel0 hCe0 hCd0 hCd0
    hsA_klm htay3 hd3n hd2n hacc0 hPrn hPhV hPhwV hVklm hVwklm hδH hQL3klm hFPh hFQ3klm
  have hbk31_hlm := remBlk31_bound d3v d2v d2w Pk Pkw Pr Qkr Qhlm Qwhlm Qhlmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 V Cq3 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hV0 hCq30 hDdel0 hCe0 hCd0 hCd0
    hsA_hlm htay3 hd3n hd2n hacc0 hPrn hPkV hPkwV hVhlm hVwhlm hδK hQL3hlm hFPk hFQ3hlm
  have hbk31_hkm := remBlk31_bound d3v d2v d2w Pl Plw Pr Qlr Qhkm Qwhkm Qhkmr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 V Cq3 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hV0 hCq30 hDdel0 hCe0 hCd0 hCd0
    hsA_hkm htay3 hd3n hd2n hacc0 hPrn hPlV hPlwV hVhkm hVwhkm hδL hQL3hkm hFPl hFQ3hkm
  have hbk31_hkl := remBlk31_bound d3v d2v d2w Pm Pmw Pr Qmr Qhkl Qwhkl Qhklr (yw - yv)
    nr eKf eKs L3 C2 Kstar3 Kstar2 V Cq3 Ddel Ce Cd Cd
    hnr0 heKf0 heKs0 hL3_0 hC2_0 hKstar30 hKstar20 hV0 hCq30 hDdel0 hCe0 hCd0 hCd0
    hsA_hkl htay3 hd3n hd2n hacc0 hPrn hPmV hPmwV hVhkl hVwhkl hδM hQL3hkl hFPm hFQ3hkl
  rw [show ((L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce)
      + (L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd)
      + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd)
      + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq)
      + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd)) * nr ^ 2
      = (L2 * eKf ^ 2 * M4 + Kstar2 * C2 * M4 + Kstar2 * eKs * Ce) * nr ^ 2 + (L5 * eKf ^ 2 * V ^ 4 + Kstar5 * C2 * V ^ 4 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar5 * eKs * Ddel * V ^ 3 + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd + Kstar4 * V ^ 2 * Ddel ^ 2 + 2 * Kstar4 * V ^ 3 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L4 * eKf ^ 2 * V ^ 2 * Cq2 + Kstar4 * C2 * V ^ 2 * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ddel * V * Cq2 + Kstar4 * eKs * Ce * V ^ 2 + Kstar3 * V ^ 2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * V * Ddel * Ce + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel ^ 2 * Cq2 + 2 * Kstar3 * V * Cq2 * Cd + Kstar3 * Ddel * Ce * V + 2 * Kstar3 * V * Cq2 * Cd) * nr ^ 2 + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) * nr ^ 2 + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) * nr ^ 2 + (L3 * eKf ^ 2 * Cq2 ^ 2 + Kstar3 * C2 * Cq2 ^ 2 + Kstar3 * eKs * Ce * Cq2 + Kstar3 * eKs * Ce * Cq2 + Kstar2 * Cq2 * Cd + Kstar2 * Ccr ^ 2 + Kstar2 * Cq3 * Cd + Kstar2 * Cd * Cq2 + Kstar2 * Cd * Cq3 + Kstar2 * Cd * VFq) * nr ^ 2 + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) * nr ^ 2 + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) * nr ^ 2 + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) * nr ^ 2 + (L3 * eKf ^ 2 * V * Cq3 + Kstar3 * C2 * V * Cq3 + Kstar3 * eKs * Ddel * Cq3 + Kstar3 * eKs * Ce * V + Kstar2 * Ddel * Ce + 2 * Kstar2 * Cq3 * Cd + Kstar2 * Cq3 * Cd + Kstar2 * V * Cd) * nr ^ 2 from by ring]
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
