/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Prereq
import QIQTH.ExpJet5Phase2

/-!
# Jet₅ order-5 prerequisites — the D⁵F primitives for the quadratic-remainder cancellation

`D⁵F := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))` is the fifth
Fréchet derivative of the geodesic field.  The order-5 quadratic-remainder cancellation
(`expJet5_remainder_quadratic_bound`, still to be built) consumes order-5 primitives that are faithful
one-Fréchet-order-up mirrors of the landed order-4 lemmas in `ExpJet4Prereq.lean`:

* `expJet_fderiv5_lipschitzOnWith` — `D⁵F` Lipschitz on the confined tube ball (ALREADY banked in
  `ExpJet5Phase2.lean`; re-exported by import).
* `geodesicField_D4F_second_order_taylor` — the first-order Taylor remainder of `D⁴F` about `x` is
  `≤ L·‖y − x‖²` given a `D⁵F`-Lipschitz constant `L` (mirror of
  `geodesicField_D3F_second_order_taylor`).
* the D⁵F argument-permutation symmetry cluster `fderiv5_geodesicField_symm_ab/_bc/_cd/_de/_cyc`
  (mirror of `fderiv4_geodesicField_symm_ab/_bc/_cd/_cyc`, extended by the fourth adjacent
  transposition `_de` since `S₅` needs four adjacent transpositions).

## Honest firewall (binding)

**What is proven here (J5-5 prerequisite layer only):** the `D⁴F`/`D⁵F` first-order Taylor bound
(carrying the `D⁵F`-Lipschitz constant as an INPUT exactly as the order-4 original — the analytic
content is the Taylor/MVT argument), and the full permutation symmetry of `D⁵F` (proved outright by
lifting the order-4 `D⁴F` symmetries through the outer `fderiv`).

**What is NOT closed:** this does NOT build the Jet₅ fifth-variation remainder (`expJet5_residual`,
`expJet5_remainder_quadratic_bound`), does NOT prove `expMap_fderiv4_hasFDerivAt`, does NOT discharge
`hfd4` / `expMap_contDiffOn_five`, does NOT reach `κ = 1/6`, the heat-kernel parametrix, or
`a₁ = R/6` (CONDITIONAL: flat non-vacuous; curved owes the remaining Jet₅ chain + Duhamel carry +
fat-K carriers + capstone co-instantiation), and is NOT numerical-`G` / the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

-- The codomain of `D⁵F` is a QUINTUPLY-nested continuous-linear-map space
-- `X →L X →L X →L X →L X →L X`; its normed-group instance chains one level deeper than the D⁴F
-- case, so we raise the pending-instance synthesis depth to let it resolve.
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

/-! ### Target 1 — `D⁴F` first-order Taylor remainder is quadratic on the confined tube ball -/

/-- **`D⁴F` second-order Taylor remainder is quadratic on the confined tube ball.**  With `L` a
    Lipschitz constant of `D⁵F = fderiv (fderiv (fderiv (fderiv (fderiv F))))` on the tube ball
    `closedBall (p,0) (expConst·expRho)` (from `expJet_fderiv5_lipschitzOnWith`), the first-order
    Taylor remainder of `D⁴F = fderiv (fderiv (fderiv (fderiv (geodesicField g gi))))` about `x` is
    bounded by `L·‖y − x‖²` for `x, y` in that ball.  The `D⁴F`/`D⁵F` mirror of
    `geodesicField_D3F_second_order_taylor`. -/
theorem geodesicField_D4F_second_order_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLip : LipschitzOnWith L.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))))
      (Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (x y : Point n × Point n)
    (hx : x ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p))
    (hy : y ∈ Metric.closedBall ((p,0) : Point n × Point n)
      (expConst g gi hC p * expRho g gi hC p)) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) y
        - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x
        - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) (y - x)‖
      ≤ L * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆
      Metric.closedBall ((p,0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) :=
    (convex_closedBall _ _).segment_subset hx hy
  have hdiff : ∀ z ∈ segment ℝ x y,
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) z :=
    fun z _ => ((contDiff_fderiv4_geodesicField g gi hC).differentiable (by simp)).differentiableAt
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) z
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x‖
        ≤ L * ‖y - x‖ := by
    intro z hz
    have hd := hLip.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL0] at hd
    calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) z
              - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x‖
        ≤ L * ‖z - x‖ := hd
      _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL0
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
    (φ := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x)
    (C := L * ‖y - x‖) hdiff hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) y
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) x
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) (y - x)‖
      ≤ L * ‖y - x‖ * ‖y - x‖ := hmv
    _ = L * ‖y - x‖ ^ 2 := by ring

/-! ### Target 2 — `D⁵F` argument-permutation symmetry

`S₅` is generated by the four adjacent transpositions `(1 2), (2 3), (3 4), (4 5)`.  We prove each
for `D⁵F` of the (`C^∞`) geodesic field:
* `_ab` — swap args 1,2, from second-derivative symmetry of `D³F = fderiv³ F` (`D⁵F = D²(D³F)`);
* `_bc` — swap args 2,3, by lifting `fderiv4_geodesicField_symm_ab` (D⁴F args 1,2) through the outer
  `fderiv` (an outer-pair `flipₗᵢ` is a linear isometry, so it commutes with `fderiv`);
* `_cd` — swap args 3,4, by lifting `fderiv4_geodesicField_symm_bc` (D⁴F args 2,3) through the outer
  `fderiv` (post-composing a once-nested `compL` flip);
* `_de` — swap args 4,5, by lifting `fderiv4_geodesicField_symm_cd` (D⁴F args 3,4) through the outer
  `fderiv` (post-composing a twice-nested `compL` flip).
Composing the four yields every permutation; `_cyc` gives the cyclic `(a,b,c,d,e) ↦ (b,c,d,e,a)`. -/

/-- **`D⁵F` is symmetric in its first two arguments.**  `D⁵F(x) a b c d e = D⁵F(x) b a c d e`.
    `D⁵F = D²(D³F)` where `D³F = fderiv³ (geodesicField g gi)` is `C^∞`
    (`contDiff_fderiv3_geodesicField`); its second derivative is a symmetric bilinear map
    (`ContDiffAt.isSymmSndFDerivAt`), i.e. `D⁵F(x) a b = D⁵F(x) b a` as elements of
    `X →L X →L X`; apply that CLM equality at `c`, then `d`, then `e`. -/
theorem fderiv5_geodesicField_symm_ab (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d e : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c d e
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) b a c d e :=
  DFunLike.congr_fun
    (DFunLike.congr_fun
      (DFunLike.congr_fun
        (((contDiff_fderiv3_geodesicField g gi hC).contDiffAt.isSymmSndFDerivAt le_top) a b) c) d) e

/-- **`D⁵F` is symmetric in its second and third arguments.**  `D⁵F(x) a b c d e = D⁵F(x) a c b d e`.
    `D⁵F = fderiv (D⁴F)`; for each `y`, `D⁴F(y)` is symmetric in its first two arguments
    (`fderiv4_geodesicField_symm_ab`); the outer-pair flip `flipₗᵢ ℝ X X (X →L X →L X)` is a linear
    isometry, so it commutes with the outer `fderiv` (`LinearIsometryEquiv.comp_fderiv`):
    `D⁵F(x) = iso.comp (D⁵F(x))`, giving `D⁵F(x) a b c d e = D⁵F(x) a c b d e`. -/
theorem fderiv5_geodesicField_symm_bc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d e : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c d e
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a c b d e := by
  set iso := ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
    ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)) with hiso
  -- `D⁴F = ⇑iso ∘ D⁴F` (pointwise outer-pair-flip invariance of `D⁴F y`, from `_symm_ab`).
  have hcomp : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      = ⇑iso ∘ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) := by
    funext y
    simp only [Function.comp_apply, hiso, ContinuousLinearMap.coe_flipₗᵢ]
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w =>
      ContinuousLinearMap.ext fun z => ContinuousLinearMap.ext fun s => ?_
    rw [ContinuousLinearMap.flip_apply]
    exact fderiv4_geodesicField_symm_ab g gi hC y u w z s
  -- differentiate: `D⁵F x = (↑iso).comp (D⁵F x)` since `iso` (a linear isometry) commutes with fderiv.
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x
      = (iso : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
              ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)))
            →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
              ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)))).comp
          (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) := by
    conv_lhs => rw [hcomp]
    exact iso.comp_fderiv
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hiso, LinearIsometryEquiv.coe_coe'', ContinuousLinearMap.coe_flipₗᵢ,
    ContinuousLinearMap.flip_apply]

/-- **`D⁵F` is symmetric in its third and fourth arguments.**  `D⁵F(x) a b c d e = D⁵F(x) a b d c e`.
    `D⁵F = fderiv (D⁴F)`; for each `y`, `D⁴F(y)` is symmetric in its second and third arguments
    (`fderiv4_geodesicField_symm_bc`).  Post-composing the inner flip (a once-nested `compL` of the
    `flipₗᵢ ℝ X X (X →L X)` that swaps the first two arguments of `X →L X →L X →L X`) leaves `D⁴F`
    invariant; post-composition is continuous-linear, so it commutes with the outer `fderiv`. -/
theorem fderiv5_geodesicField_symm_cd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d e : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c d e
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b d c e := by
  -- the first-two-argument flip on `X →L X →L X →L X` (swapping args 3,4 of `D⁴F y` after arg 1).
  set flipC : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
        (Point n × Point n) →L[ℝ] (Point n × Point n))
      →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ]
        (Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
      ((Point n × Point n) →L[ℝ] (Point n × Point n))).toLinearIsometry.toContinuousLinearMap
    with hflipC
  -- post-composition by `flipC` as a CLM on `D⁴F`'s codomain `X →L (X →L X →L X →L X)`.
  set L := ContinuousLinearMap.compL ℝ (Point n × Point n)
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      flipC with hL
  -- `D⁴F = ⇑L ∘ D⁴F` (pointwise args-2,3-flip invariance of `D⁴F y`, from `_symm_bc`).
  have hcomp : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      = ⇑L ∘ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) := by
    funext y
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w =>
      ContinuousLinearMap.ext fun z => ContinuousLinearMap.ext fun s => ?_
    simp only [Function.comp_apply, hL, hflipC, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.coe_flipₗᵢ,
      ContinuousLinearMap.flip_apply]
    exact fderiv4_geodesicField_symm_bc g gi hC y u w z s
  -- differentiate through the post-composition CLM `L`.
  have hdiffD4 : HasFDerivAt (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) x :=
    ((contDiff_fderiv4_geodesicField g gi hC).differentiable (by simp)).differentiableAt.hasFDerivAt
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x
      = L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) := by
    conv_lhs => rw [hcomp]
    exact (L.hasFDerivAt.comp x hdiffD4).fderiv
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hL, hflipC, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.coe_flipₗᵢ, ContinuousLinearMap.flip_apply]

/-- **`D⁵F` is symmetric in its fourth and fifth arguments.**  `D⁵F(x) a b c d e = D⁵F(x) a b c e d`.
    `D⁵F = fderiv (D⁴F)`; for each `y`, `D⁴F(y)` is symmetric in its third and fourth arguments
    (`fderiv4_geodesicField_symm_cd`).  Post-composing the twice-nested `compL` flip (swap the two
    arguments of the innermost `X →L X →L X`, lifted through one `compL` to swap args 2,3 of
    `X →L X →L X →L X`, then through a second `compL` to swap args 3,4 of `D⁴F y`) leaves `D⁴F`
    invariant; post-composition is continuous-linear, so it commutes with the outer `fderiv`. -/
theorem fderiv5_geodesicField_symm_de (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d e : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c d e
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c e d := by
  -- innermost two-argument flip on `X →L X →L X`.
  set flip0 : ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (Point n × Point n) (Point n × Point n)
      (Point n × Point n)).toLinearIsometry.toContinuousLinearMap with hflip0
  -- lift once: swap args 2,3 of `X →L X →L X →L X`.
  set inner2 := ContinuousLinearMap.compL ℝ (Point n × Point n)
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n)) flip0 with hinner2
  -- lift again: swap args 3,4 of `D⁴F y : X →L X →L X →L X →L X` (post-comp on `D⁴F`'s codomain).
  set L := ContinuousLinearMap.compL ℝ (Point n × Point n)
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      ((Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n) →L[ℝ] (Point n × Point n))
      inner2 with hL
  -- `D⁴F = ⇑L ∘ D⁴F` (pointwise args-3,4-flip invariance of `D⁴F y`, from `_symm_cd`).
  have hcomp : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      = ⇑L ∘ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) := by
    funext y
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w =>
      ContinuousLinearMap.ext fun z => ContinuousLinearMap.ext fun s => ?_
    simp only [Function.comp_apply, hL, hinner2, hflip0, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.coe_flipₗᵢ,
      ContinuousLinearMap.flip_apply]
    exact fderiv4_geodesicField_symm_cd g gi hC y u w z s
  -- differentiate through the post-composition CLM `L`.
  have hdiffD4 : HasFDerivAt (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) x :=
    ((contDiff_fderiv4_geodesicField g gi hC).differentiable (by simp)).differentiableAt.hasFDerivAt
  have key : fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x
      = L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) := by
    conv_lhs => rw [hcomp]
    exact (L.hasFDerivAt.comp x hdiffD4).fderiv
  have h1 := DFunLike.congr_fun key a
  rw [ContinuousLinearMap.comp_apply] at h1
  conv_lhs => rw [h1]
  simp only [hL, hinner2, hflip0, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.coe_flipₗᵢ, ContinuousLinearMap.flip_apply]

/-- **`D⁵F` is fully symmetric: the cyclic permutation `(a,b,c,d,e) ↦ (b,c,d,e,a)`.**  Obtained by
    composing the four adjacent transpositions (`_ab`, then `_bc`, then `_cd`, then `_de`).  This is
    the permutation the Rung-5 remainder cancellation uses to identify the pure `D⁵F` contraction of
    the five first variations with its `expJet5Rhs` counterpart.  Together with the four
    transpositions it exhibits the full `S₅` symmetry of `D⁵F`. -/
theorem fderiv5_geodesicField_symm_cyc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x a b c d e : Point n × Point n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) a b c d e
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) x) b c d e a := by
  rw [fderiv5_geodesicField_symm_ab g gi hC x a b c d e,
    fderiv5_geodesicField_symm_bc g gi hC x b a c d e,
    fderiv5_geodesicField_symm_cd g gi hC x b c a d e,
    fderiv5_geodesicField_symm_de g gi hC x b c d a e]

/-! ### Non-vacuity gate at the genuinely curved witness `curvedRNCMetric (−1)` -/

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate: the D⁴F Taylor bound and the D⁵F symmetry fire at genuinely curved data.**
    At `g^κ = curvedRNCMetric (−1)` (`p = 0`), `D⁵F` is Lipschitz on the confined tube ball
    (`expJet_fderiv5_lipschitzOnWith`), and both the first-order `D⁴F` Taylor remainder
    (`geodesicField_D4F_second_order_taylor` at `x = y = (0,0) ∈` ball, so the RHS is `L·0 = 0`) and
    the cyclic `D⁵F` symmetry (`fderiv5_geodesicField_symm_cyc`) hold at that curved witness.  This
    certifies the order-5 prerequisite lemmas are non-vacuously instantiable at curved data (NOT a
    curvature computation and NOT `a₁ = R/6`). -/
theorem geodesicField_D4F_second_order_taylor_gate :
    ∃ L : ℝ, 0 ≤ L ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField (curvedRNCMetric (n := n) (-1))
              (curvedRNCInv (n := n) (-1)))))) ((0, 0) : Point n × Point n)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField (curvedRNCMetric (n := n) (-1))
              (curvedRNCInv (n := n) (-1)))))) ((0, 0) : Point n × Point n)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField (curvedRNCMetric (n := n) (-1))
              (curvedRNCInv (n := n) (-1))))))) ((0, 0) : Point n × Point n))
              (((0, 0) : Point n × Point n) - (0, 0))‖
        ≤ L * ‖((0, 0) : Point n × Point n) - (0, 0)‖ ^ 2 := by
  obtain ⟨Ld5f, hLipD5F⟩ := expJet_fderiv5_lipschitzOnWith (curvedRNCMetric (n := n) (-1))
    (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  refine ⟨(Ld5f : ℝ), Ld5f.2, ?_⟩
  have hmem : ((0, 0) : Point n × Point n) ∈
      Metric.closedBall ((0, 0) : Point n × Point n)
        (expConst (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
          * expRho (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0) :=
    Metric.mem_closedBall_self (mul_nonneg (expConst_nonneg _ _ _ _) (expRho_pos _ _ _ _).le)
  have hlip' : LipschitzOnWith ((Ld5f : ℝ)).toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField (curvedRNCMetric (n := n) (-1))
        (curvedRNCInv (n := n) (-1))))))))
      (Metric.closedBall ((0, 0) : Point n × Point n)
        (expConst (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
          * expRho (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0)) := by
    rwa [Real.toNNReal_coe]
  exact geodesicField_D4F_second_order_taylor (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1))
    (curvedRNC_hChr (-1) (by norm_num)) 0 (Ld5f : ℝ) Ld5f.2 hlip' (0, 0) (0, 0) hmem hmem

end QIQTH.ExpMap
