/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemBlkTop
import QIQTH.ExpJet5RemBlkCross

/-!
# Jet₅ quadratic-remainder — abstract master reassembly identity (rung J5-5b, file A)

Banks the pure algebraic reassembly `remMaster_identity`: the order-5 residual head
`(dw − dv) qw + (Θ₄w − Θ₄v − Θ₅v)` (source in `expJet4Rhs`/`expJet5Rhs` order) equals the sum of the
fifteen abstract block-LHS expressions (Block-0, the Top block, six `(2+1+1)`, three `(2+2)`, four
`(3+1)`), given the eighteen argument-permutation symmetry facts of the concrete `D²F`/`D³F` that
reconcile the `(2+2)`/`(3+2)` source orderings with the block orderings.  Opaque multilinear atoms
(so the quintuply-nested-CLM `whnf` never fires); `simp only [sub_apply]; rw [symmetry]; abel`.  The
decomposition + eighteen reconciliations validated numerically (fully-symmetric random tensors,
residual ≤ 1.8e-14).

## Honest firewall (binding)

Pure multilinear-algebra reassembly ONLY.  Does NOT by itself prove
`expJet5_remainder_quadratic_bound`; does NOT reach `expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`,
`κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abstract order-5 master reassembly identity.** -/
theorem remMaster_identity
    (dv dw : E →L[ℝ] E)
    (d2v d2w : E →L[ℝ] E →L[ℝ] E)
    (d3v d3w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d4v d4w : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (d5v : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (qw Pr Ph Pk Pl Pm Phw Pkw Plw Pmw : E)
    (Qhk Qhl Qhm Qkl Qkm Qlm Qhr Qkr Qlr Qmr : E)
    (Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm : E)
    (Qhkl Qhkm Qhlm Qklm Qhkr Qhlr Qhmr Qklr Qkmr Qlmr : E)
    (Qwhkl Qwhkm Qwhlm Qwklm : E)
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : E)
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
    (hs18 : d2v Qhkl Qmr = d2v Qmr Qhkl) :
    (dw - dv) qw
      + ((d4w Phw Pkw Plw Pmw + d3w Plw Pmw Qwhk + d3w Pkw Pmw Qwhl + d3w Pkw Plw Qwhm + d3w Phw Pmw Qwkl + d3w Phw Plw Qwkm + d3w Phw Pkw Qwlm + d2w Qwhk Qwlm + d2w Qwhl Qwkm + d2w Qwhm Qwkl + d2w Phw Qwklm + d2w Pkw Qwhlm + d2w Plw Qwhkm + d2w Pmw Qwhkl)
         - (d4v Ph Pk Pl Pm + d3v Pl Pm Qhk + d3v Pk Pm Qhl + d3v Pk Pl Qhm + d3v Ph Pm Qkl + d3v Ph Pl Qkm + d3v Ph Pk Qlm + d2v Qhk Qlm + d2v Qhl Qkm + d2v Qhm Qkl + d2v Ph Qklm + d2v Pk Qhlm + d2v Pl Qhkm + d2v Pm Qhkl)
         - (d5v Ph Pk Pl Pm Pr + d4v Pl Pm Pr Qhk + d4v Pk Pm Pr Qhl + d4v Pk Pl Pr Qhm + d4v Pk Pl Pm Qhr + d4v Ph Pm Pr Qkl + d4v Ph Pl Pr Qkm + d4v Ph Pl Pm Qkr + d4v Ph Pk Pr Qlm + d4v Ph Pk Pm Qlr + d4v Ph Pk Pl Qmr + d3v Ph Qkl Qmr + d3v Ph Qkm Qlr + d3v Ph Qkr Qlm + d3v Pk Qhl Qmr + d3v Pk Qhm Qlr + d3v Pk Qhr Qlm + d3v Pl Qhk Qmr + d3v Pl Qhm Qkr + d3v Pl Qhr Qkm + d3v Pm Qhk Qlr + d3v Pm Qhl Qkr + d3v Pm Qhr Qkl + d3v Pr Qhk Qlm + d3v Pr Qhl Qkm + d3v Pr Qhm Qkl + d3v Pm Pr Qhkl + d3v Pl Pr Qhkm + d3v Pl Pm Qhkr + d3v Pk Pr Qhlm + d3v Pk Pm Qhlr + d3v Pk Pl Qhmr + d3v Ph Pr Qklm + d3v Ph Pm Qklr + d3v Ph Pl Qkmr + d3v Ph Pk Qlmr + d2v Qhkl Qmr + d2v Qhkm Qlr + d2v Qhkr Qlm + d2v Qhlm Qkr + d2v Qhlr Qkm + d2v Qhmr Qkl + d2v Qklm Qhr + d2v Qklr Qhm + d2v Qkmr Qhl + d2v Qlmr Qhk + d2v Ph Qklmr + d2v Pk Qhlmr + d2v Pl Qhkmr + d2v Pm Qhklr + d2v Pr Qhklm))
    = ((dw - dv) qw - d2v Pr Qhklm)
        + (d4w Phw Pkw Plw Pmw - d4v Ph Pk Pl Pm - d5v Ph Pk Pl Pm Pr - d4v Pk Pl Pm Qhr - d4v Ph Pl Pm Qkr - d4v Ph Pk Pm Qlr - d4v Ph Pk Pl Qmr)
        + (d3w Plw Pmw Qwhk - d3v Pl Pm Qhk - d4v Pl Pm Pr Qhk - d3v Qlr Pm Qhk - d3v Pl Qmr Qhk - d3v Pl Pm Qhkr)
        + (d3w Pkw Pmw Qwhl - d3v Pk Pm Qhl - d4v Pk Pm Pr Qhl - d3v Qkr Pm Qhl - d3v Pk Qmr Qhl - d3v Pk Pm Qhlr)
        + (d3w Pkw Plw Qwhm - d3v Pk Pl Qhm - d4v Pk Pl Pr Qhm - d3v Qkr Pl Qhm - d3v Pk Qlr Qhm - d3v Pk Pl Qhmr)
        + (d3w Phw Pmw Qwkl - d3v Ph Pm Qkl - d4v Ph Pm Pr Qkl - d3v Qhr Pm Qkl - d3v Ph Qmr Qkl - d3v Ph Pm Qklr)
        + (d3w Phw Plw Qwkm - d3v Ph Pl Qkm - d4v Ph Pl Pr Qkm - d3v Qhr Pl Qkm - d3v Ph Qlr Qkm - d3v Ph Pl Qkmr)
        + (d3w Phw Pkw Qwlm - d3v Ph Pk Qlm - d4v Ph Pk Pr Qlm - d3v Qhr Pk Qlm - d3v Ph Qkr Qlm - d3v Ph Pk Qlmr)
        + (d2w Qwhk Qwlm - d2v Qhk Qlm - d3v Pr Qhk Qlm - d2v Qhkr Qlm - d2v Qhk Qlmr)
        + (d2w Qwhl Qwkm - d2v Qhl Qkm - d3v Pr Qhl Qkm - d2v Qhlr Qkm - d2v Qhl Qkmr)
        + (d2w Qwhm Qwkl - d2v Qhm Qkl - d3v Pr Qhm Qkl - d2v Qhmr Qkl - d2v Qhm Qklr)
        + (d2w Phw Qwklm - d2v Ph Qklm - d3v Ph Pr Qklm - d2v Qhr Qklm - d2v Ph Qklmr)
        + (d2w Pkw Qwhlm - d2v Pk Qhlm - d3v Pk Pr Qhlm - d2v Qkr Qhlm - d2v Pk Qhlmr)
        + (d2w Plw Qwhkm - d2v Pl Qhkm - d3v Pl Pr Qhkm - d2v Qlr Qhkm - d2v Pl Qhkmr)
        + (d2w Pmw Qwhkl - d2v Pm Qhkl - d3v Pm Pr Qhkl - d2v Qmr Qhkl - d2v Pm Qhklr) := by
  simp only [ContinuousLinearMap.sub_apply]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18]
  abel

end QIQTH.ExpMap
