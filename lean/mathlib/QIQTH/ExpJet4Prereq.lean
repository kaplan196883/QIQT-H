/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMapContDiff4

/-!
# Jet₄ order-4 prerequisites — the three D⁴F primitives for the quadratic-remainder cancellation

`D⁴F := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))` is the fourth Fréchet
derivative of the geodesic field.  The order-4 quadratic-remainder cancellation
(`expJet4_remainder_quadratic_bound`) consumes three order-4 primitives that are faithful one-order-up
mirrors of the landed order-3 lemmas in `ExpMapContDiff3.lean`:

* `expJet_fderiv4_lipschitzOnWith` — `D⁴F` is Lipschitz on the confined tube ball
  (mirror of `expJet_fderiv3_lipschitzOnWith`).
* `geodesicField_D3F_second_order_taylor` — the first-order Taylor remainder of `D³F` about `x` is
  `≤ L·‖y − x‖²` given a `D⁴F`-Lipschitz constant `L` (mirror of
  `geodesicField_D2F_second_order_taylor`).
* the D⁴F argument-permutation symmetry cluster `fderiv4_geodesicField_symm_ab/_bc/_cd/_cyc`
  (mirror of `fderiv3_geodesicField_symm_ab/_bc/_cyc`).

## Honest firewall (binding)

**What is proven here:** the `D⁴F` Lipschitz regularity, the `D³F`/`D⁴F` first-order Taylor bound
(carrying the `D⁴F`-Lipschitz constant as an INPUT exactly as the order-3 original — the analytic
content is the Taylor/MVT argument), and the full permutation symmetry of `D⁴F` (proved outright).

**What is NOT closed:** this does NOT build the Jet₄ fourth-variation fundamental solution, does NOT
discharge `expJet4_remainder_quadratic_bound`, does NOT reach `κ = 1/6`, the heat-kernel parametrix,
or `a₁ = R/6`, and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁴F` is a QUADRUPLY-nested continuous-linear-map space
-- `E →L E →L E →L E →L E`; its normed-group instance chains one level deeper than the D³F case, so
-- we raise the pending-instance synthesis depth to let it resolve.
set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### Target 1 — `D⁴F` is Lipschitz on the confined tube ball -/

/-- **`D⁴F` is Lipschitz on the confined tube ball.**  The direct `D⁴F` analog of
    `expJet_fderiv3_lipschitzOnWith`.  `D⁴F = fderiv (fderiv (fderiv (fderiv F)))` is `C^∞`
    (`contDiff_fderiv4_geodesicField`), hence `C¹`, and the tube ball
    `Metric.closedBall (p,0) (expConst · expRho)` is compact and convex; a `C¹` map is Lipschitz on
    a compact convex set (`ContDiffOn.exists_lipschitzOnWith`). -/
theorem expJet_fderiv4_lipschitzOnWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Ld4f : NNReal, LipschitzOnWith Ld4f
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) :=
  ((contDiff_fderiv4_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-! ### Target 2 — `D³F` first-order Taylor remainder is quadratic on the confined tube ball -/

/-- **`D³F` second-order Taylor remainder is quadratic on the confined tube ball.**  With `L` a
    Lipschitz constant of `D⁴F = fderiv (fderiv (fderiv (fderiv F)))` on the tube ball
    `closedBall (p,0) (expConst·expRho)` (from `expJet_fderiv4_lipschitzOnWith`), the first-order
    Taylor remainder of `D³F = fderiv (fderiv (fderiv (geodesicField g gi)))` about `x` is bounded by
    `L·‖y − x‖²` for `x, y` in that ball.  The `D³F`/`D⁴F` mirror of
    `geodesicField_D2F_second_order_taylor`. -/
theorem geodesicField_D3F_second_order_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLip : LipschitzOnWith L.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (x y : Point n × Point n)
    (hx : x ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p))
    (hy : y ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p)) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) y
        - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x
        - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) (y - x)‖
      ≤ L * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆
      Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) :=
    (convex_closedBall _ _).segment_subset hx hy
  have hdiff : ∀ z ∈ segment ℝ x y,
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) z :=
    fun z _ => ((contDiff_fderiv3_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) z
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    have hd := hLip.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL0] at hd
    calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) z
              - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x‖
        ≤ L * ‖z - x‖ := hd
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL0
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
    (φ := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x)
    (C := L * ‖y - x‖) hdiff hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) y
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) (y - x)‖
      ≤ L * ‖y - x‖ * ‖y - x‖ := hmv
    _ = L * ‖y - x‖ ^ 2 := by ring

/-! ### Target 3 — `D⁴F` argument-permutation symmetry

Mathlib supplies second-derivative symmetry only (`ContDiffAt.isSymmSndFDerivAt`); it has **no**
general "iterated Fréchet derivative is symmetric under all argument permutations" API.  We bridge
this for `D⁴F` of the (`C^∞`) geodesic field by proving the three adjacent transpositions that
generate the full symmetric group `S₄` on the four arguments:
* `fderiv4_geodesicField_symm_ab` — swap arguments 1,2, from second-derivative symmetry of the
  (`C^∞`) function `D²F = fderiv (fderiv F)` (`D⁴F = D²(D²F)`, the top-pair symmetry);
* `fderiv4_geodesicField_symm_bc` — swap arguments 2,3, by lifting the D³F first-two-argument
  symmetry (`fderiv3_geodesicField_symm_ab`) through the outer `fderiv` (the outer-pair `flipₗᵢ` is a
  linear isometry, so it commutes with `fderiv`);
* `fderiv4_geodesicField_symm_cd` — swap arguments 3,4, by lifting the D³F last-two-argument symmetry
  (`fderiv3_geodesicField_symm_bc`) through the outer `fderiv` (post-composing the inner `flipₗᵢ`).
Composing the three yields every permutation; `fderiv4_geodesicField_symm_cyc` gives the cyclic
`(a,b,c,d) ↦ (b,c,d,a)` used by the Rung-4 cancellation. -/

/-- **`D⁴F` is symmetric in its first two arguments.**  `D⁴F(x) a b c d = D⁴F(x) b a c d`.
    `D⁴F = D²(D²F)` where `D²F = fderiv (fderiv F)` is `C^∞` (`contDiff_fderiv2_geodesicField`); its
    second derivative is a symmetric bilinear map (`ContDiffAt.isSymmSndFDerivAt`), i.e. `D⁴F(x) a b =
    D⁴F(x) b a` as elements of `E →L E →L E`; apply that CLM equality at `c` then `d`. -/
theorem fderiv4_geodesicField_symm_ab (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a b c d
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) b a c d :=
  DFunLike.congr_fun
    (DFunLike.congr_fun
      (((contDiff_fderiv2_geodesicField g gi hC).contDiffAt.isSymmSndFDerivAt le_top) a b) c) d

/-- **`D⁴F` is symmetric in its second and third arguments.**  `D⁴F(x) a b c d = D⁴F(x) a c b d`.
    `D⁴F = fderiv (D³F)`; for each `y`, `D³F(y)` is symmetric in its first two arguments
    (`fderiv3_geodesicField_symm_ab`), i.e. `D³F(y) = (D³F(y))`-with-its-outer-pair-flipped; the
    outer-pair flip `flipₗᵢ ℝ E E (E →L E)` is a linear isometry, so it commutes with the outer
    `fderiv` (`LinearIsometryEquiv.comp_fderiv`): `D⁴F(x) = iso.comp (D⁴F(x))`, giving
    `D⁴F(x) a b c d = D⁴F(x) a c b d`. -/
theorem fderiv4_geodesicField_symm_bc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a b c d
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a c b d := by
  set iso := ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
    ((Point n × Point n) →L[ℝ] (Point n × Point n)) with hiso
  -- `D³F = ⇑iso ∘ D³F` (pointwise outer-pair-flip invariance of `D³F y`, from `_symm_ab`).
  have hcomp : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      = ⇑iso ∘ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) := by
    funext y
    simp only [Function.comp_apply, hiso, ContinuousLinearMap.coe_flipₗᵢ]
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w =>
      ContinuousLinearMap.ext fun z => ?_
    rw [ContinuousLinearMap.flip_apply]
    exact fderiv3_geodesicField_symm_ab g gi hC y u w z
  -- differentiate: `D⁴F x = (↑iso).comp (D⁴F x)` since `iso` (a linear isometry) commutes with fderiv.
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x
      = (iso : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
              ((Point n × Point n) →L[ℝ] (Point n × Point n)))
            →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
              ((Point n × Point n) →L[ℝ] (Point n × Point n)))).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) := by
    conv_lhs => rw [hcomp]
    exact iso.comp_fderiv
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hiso, LinearIsometryEquiv.coe_coe'', ContinuousLinearMap.coe_flipₗᵢ,
    ContinuousLinearMap.flip_apply]

/-- **`D⁴F` is symmetric in its third and fourth arguments.**  `D⁴F(x) a b c d = D⁴F(x) a b d c`.
    `D⁴F = fderiv (D³F)`; for each `y`, `D³F(y)` is symmetric in its last two arguments
    (`fderiv3_geodesicField_symm_bc`).  Post-composing the inner-pair flip `flipₗᵢ ℝ E E E` (a linear
    map on the codomain of `D³F`) leaves `D³F` invariant; post-composition is a continuous-linear
    operation, so it commutes with the outer `fderiv` (`HasFDerivAt.comp` with the post-composition
    CLM `compL flip`): `D⁴F(x) = L.comp (D⁴F(x))`, giving `D⁴F(x) a b c d = D⁴F(x) a b d c`. -/
theorem fderiv4_geodesicField_symm_cd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a b c d
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a b d c := by
  -- the inner-pair flip as a CLM on `D²F`'s codomain `E →L E →L E`.
  set flipC : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
      (Point n × Point n)).toLinearIsometry.toContinuousLinearMap with hflipC
  -- post-composition by `flipC` as a CLM on `D³F`'s codomain `E →L (E →L E →L E)`.
  set L := ContinuousLinearMap.compL ℝ (Point n × Point n)
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)) flipC with hL
  -- `D³F = ⇑L ∘ D³F` (pointwise inner-pair-flip invariance of `D³F y`, from `_symm_bc`).
  have hcomp : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      = ⇑L ∘ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) := by
    funext y
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w =>
      ContinuousLinearMap.ext fun z => ?_
    simp only [Function.comp_apply, hL, hflipC, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.coe_flipₗᵢ,
      ContinuousLinearMap.flip_apply]
    exact fderiv3_geodesicField_symm_bc g gi hC y u w z
  -- differentiate through the post-composition CLM `L`.
  have hdiffD3 : HasFDerivAt (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) x :=
    ((contDiff_fderiv3_geodesicField g gi hC).differentiable (by simp)).differentiableAt.hasFDerivAt
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x
      = L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) := by
    conv_lhs => rw [hcomp]
    exact (L.hasFDerivAt.comp x hdiffD3).fderiv
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hL, hflipC, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.coe_flipₗᵢ, ContinuousLinearMap.flip_apply]

/-- **`D⁴F` is fully symmetric: the cyclic permutation `(a,b,c,d) ↦ (b,c,d,a)`.**  Obtained by
    composing the three adjacent transpositions (`_ab`, then `_bc`, then `_cd`).  This is the
    permutation the Rung-4 cancellation uses to identify the pure `D⁴F` contraction of the four first
    variations with its `expJet4Rhs` counterpart.  Together with the three transpositions it exhibits
    the full `S₄` symmetry of `D⁴F`. -/
theorem fderiv4_geodesicField_symm_cyc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) a b c d
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x) b c d a := by
  rw [fderiv4_geodesicField_symm_ab g gi hC x a b c d,
    fderiv4_geodesicField_symm_bc g gi hC x b a c d,
    fderiv4_geodesicField_symm_cd g gi hC x b c a d]

end QIQTH.ExpMap
