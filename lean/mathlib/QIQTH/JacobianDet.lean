/-
  JacobianDet — the pullback-determinant = (exp-Jacobian)² bridge (Phase K1 of the Jacobi-field
  campaign, docs/qg_roadmap/JACOBI_FIELD_PLAN.md).

  Setting.  `Point n = Fin n → ℝ`; the ambient metric `g`, its inverse `gi`, and the geodesic
  exponential map `exp_p := expMap g gi hC p`.  The pullback metric (`QIQTH.PullbackMetric`) is
      `g̃(x)_{ij} = ∑_{a,b} g(exp_p x)_{ab} · (D exp_p x · e_i)_a · (D exp_p x · e_j)_b`,
  which is exactly the tensorial product `g̃ = (D exp_p)ᵀ · (g ∘ exp_p) · (D exp_p)`.

  This file assembles the exp-map differential `D exp_p x = fderiv exp_p x` into a matrix
  `expJacobianMat`, defines its determinant `expJacobianDet = J(x)`, and PROVES the van-Vleck ↔
  exp-Jacobian bridge
      `det g̃(x) = J(x)² · det (g ∘ exp_p)(x)`,
  via `det ((D exp)ᵀ · (g∘exp) · (D exp)) = (det D exp)² · det (g∘exp)`
  (`Matrix.det_mul` twice + `Matrix.det_transpose`).  The van-Vleck determinant is `Θ = (det g̃)^{-1/2}`,
  so this identity is the bridge from the van-Vleck object to the exp-map Jacobian `J` whose radial ODE
  (the Jacobi equation) governs it.  This brick is K1 ONLY: it is the algebraic factorization, NOT the
  Jacobi equation (K3), the van-Vleck ODE (K4), or `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PullbackMetric

namespace QIQTH.JacobianDet

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric
open Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **The exp-map differential `D(exp_p)_x` as a matrix.**  Entry `(a, i)` is the `a`-component of
    `D exp_p x` applied to the `i`-th coordinate basis vector `e_i = Pi.single i 1`; i.e. the columns of
    `expJacobianMat` are the images of the coordinate basis under the exponential differential.  This
    is exactly the Jacobian factor appearing in `expPullbackMetric`. -/
noncomputable def expJacobianMat (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a i => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a

/-- **The exp differential at the centre is the identity.**  `D exp_p 0 = id` (`fderiv_expMap_zero`),
    so the assembled Jacobian matrix is the identity matrix at `x = 0`. -/
theorem expJacobianMat_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    expJacobianMat g gi hC p 0 = 1 := by
  ext a i
  simp only [expJacobianMat, fderiv_expMap_zero, ContinuousLinearMap.id_apply, Pi.single_apply,
    Matrix.one_apply]

/-- **The exp-map Jacobian determinant** `J(x) = det D(exp_p)_x`. -/
noncomputable def expJacobianDet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) : ℝ :=
  Matrix.det (expJacobianMat g gi hC p x)

/-- **`J(0) = 1`** — the Jacobian determinant is `1` at the centre of the exp-normal coordinates. -/
theorem expJacobianDet_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    expJacobianDet g gi hC p 0 = 1 := by
  rw [expJacobianDet, expJacobianMat_zero, Matrix.det_one]

/-- **The matrix-product form of the pullback metric.**  The pullback metric equals the tensorial
    triple product `g̃ = (D exp_p)ᵀ · (g ∘ exp_p) · (D exp_p)`, matching its definition
    `g̃_{ij} = ∑_{a,b} (g∘exp)_{ab} · J_{ai} · J_{bj}`. -/
theorem expPullbackMetric_eq_jacMul (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) :
    (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)
      = (expJacobianMat g gi hC p x)ᵀ
          * (Matrix.of fun a b => g (expMap g gi hC p x) a b)
          * (expJacobianMat g gi hC p x) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, expPullbackMetric,
    expJacobianMat]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- **THE PULLBACK-DETERMINANT BRIDGE (van-Vleck ↔ exp-Jacobian).**
    `det g̃(x) = J(x)² · det (g ∘ exp_p)(x)`, from
    `det ((D exp)ᵀ (g∘exp) (D exp)) = (det (D exp)ᵀ)(det (g∘exp))(det (D exp)) = (det D exp)² · det(g∘exp)`
    (`Matrix.det_mul` twice + `Matrix.det_transpose`).  Since the van-Vleck determinant is
    `Θ = (det g̃)^{-1/2}`, this exhibits `Θ` in terms of the exp-map Jacobian `J`. -/
theorem det_expPullback_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) :
    Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)
      = (expJacobianDet g gi hC p x) ^ 2
          * Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b) := by
  rw [expPullbackMetric_eq_jacMul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    expJacobianDet]
  ring

end QIQTH.JacobianDet
