/-
  ExpJacobianRegularity — the van-Vleck / exp-Jacobian determinant is `C²` on the exp ball
  (a REGULARITY FLOOR brick of the off-radial van-Vleck campaign,
  docs/qg_roadmap/JACOBI_FIELD_PLAN.md).

  Setting.  `Point n = Fin n → ℝ`; `exp_p := expMap g gi hC p`; the exp ball
  `Metric.ball 0 (expRho g gi hC p)`.  The exp differential is assembled entrywise into
  `expJacobianMat g gi hC p x a i = (fderiv ℝ exp_p x) (Pi.single i 1) a` (QIQTH.JacobianDet),
  and its determinant is the exp-map Jacobian `J(x) = expJacobianDet g gi hC p x`.

  This file proves ONLY REGULARITY:
  * `expJacobianMat_entry_contDiffOn_two` — each Jacobian-matrix entry `x ↦ D(exp_p)_x·e_i|_a`
    is `C²` on the (open) exp ball;
  * `expJacobianDet_contDiffOn_two` — the exp-Jacobian determinant `J = det (D exp_p)` is `C²`
    on the exp ball.

  Mechanism.  `exp_p` is `C³` on the ball (`QIQTH.ExpMap.expMap_contDiffOn_three`); the `fderiv`
  of a `C³` map is `C²` on the open ball (`ContDiffOn.fderiv_of_isOpen` with `2 + 1 ≤ 3`); each
  entry is that `C²` `fderiv` post-composed with a fixed continuous-linear evaluation
  `L ↦ (L e_i) a`; and `det` is a finite signed sum of finite products of entries
  (`Matrix.det_apply'`), so it is `C²` by `ContDiffOn.sum` / `contDiffOn_prod` / `ContDiffOn.mul`.

  ## What this is NOT.
  This establishes only that `J` is `C²` on the ball — hence its second radial/covariant
  derivative EXISTS off-centre.  It does NOT prove the Jacobi identity `B'' = −R̃ B`, the
  van-Vleck radial ODE, or `a₁ = R/6`; those remain the documented geometric walls.
-/
import Mathlib
import QIQTH.ExpMapContDiff3
import QIQTH.JacobianDet

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.JacobianDet
open Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-- **Each exp-Jacobian matrix entry is `C²` on the exp ball.**  `exp_p` is `C³` on the ball, so
    `x ↦ fderiv ℝ exp_p x` is `C²` there (`ContDiffOn.fderiv_of_isOpen`, `2 + 1 ≤ 3`); the entry
    `x ↦ (fderiv ℝ exp_p x) (Pi.single i 1) a` is that `C²` map post-composed with the fixed
    continuous-linear evaluation `L ↦ (L (Pi.single i 1)) a`, hence `C²`.  REGULARITY ONLY. -/
theorem expJacobianMat_entry_contDiffOn_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (a i : Fin n) :
    ContDiffOn ℝ 2 (fun x => expJacobianMat g gi hC p x a i)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  -- The differential of the `C³` exp map is `C²` on the open ball.
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ (expMap g gi hC p))
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    (expMap_contDiffOn_three g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  -- The fixed continuous-linear evaluation `L ↦ (L (Pi.single i 1)) a`.
  have key : ContDiffOn ℝ 2
      (((ContinuousLinearMap.proj a).comp
          (ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1)))
        ∘ fderiv ℝ (expMap g gi hC p))
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    hfd.continuousLinearMap_comp _
  refine key.congr (fun x _ => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.apply_apply, expJacobianMat]

/-- **The exp-Jacobian determinant `J = det (D exp_p)` is `C²` on the exp ball.**  Expanding
    `det` with `Matrix.det_apply'` writes `J(x)` as a finite signed sum of finite products of the
    matrix entries, each of which is `C²` by `expJacobianMat_entry_contDiffOn_two`; finite sums
    (`ContDiffOn.sum`) of constant multiples (`ContDiffOn.mul`) of finite products
    (`contDiffOn_prod`) of `C²` functions are `C²`.  REGULARITY ONLY: this only shows the
    van-Vleck Jacobian determinant admits a second radial/covariant derivative off-centre; it does
    NOT prove the Jacobi identity `B'' = −R̃ B` or `a₁ = R/6`. -/
theorem expJacobianDet_contDiffOn_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ContDiffOn ℝ 2 (expJacobianDet g gi hC p)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  have hrw : expJacobianDet g gi hC p
      = fun x => ∑ σ : Equiv.Perm (Fin n),
          (Equiv.Perm.sign σ : ℝ) * ∏ i, expJacobianMat g gi hC p x (σ i) i := by
    funext x
    rw [expJacobianDet, Matrix.det_apply']
  rw [hrw]
  apply ContDiffOn.sum
  intro σ _
  refine ContDiffOn.mul contDiffOn_const ?_
  apply contDiffOn_prod
  intro i _
  exact expJacobianMat_entry_contDiffOn_two g gi hC p (σ i) i

end QIQTH.JacobianRegularity
