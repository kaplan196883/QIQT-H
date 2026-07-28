import Mathlib
import QIQTH.ExpDiffVariation
import QIQTH.JacobianDet

/-!
# EXP-JET3-2 — `expJacobianMat` is the matrix of Jacobi-field positions at `t = 1`

Building on EXP-JET3-1 (`expDiff_flow_isGeodesicVariation`, `QIQTH/ExpDiffVariation.lean`),
this file identifies the exp-Jacobian matrix entrywise with the geodesic-variation (Jacobi)
flow `Φ`.

From EXP-JET3-1 we have the operator flow `Φ : ℝ → (Point n × Point n) →L (Point n × Point n)`
with `Φ 0 = id`, the geodesic-variation law
`d/dt (Φ t) w = DF(expTube t) ((Φ t) w)` (within `[0,1]`), and
`fderiv (expMap p) v = expJetPi ∘ (Φ 1) ∘ expJetIota`.  Since
`expJacobianMat p v a i = (fderiv (expMap p) v) (Pi.single i 1) a`, unfolding through the flow
gives

`expJacobianMat p v a i = ((Φ 1) (0, e_i)).1 a`,

i.e. the `(a,i)` entry is the `a`-component of the **position part** of `Φ(1)(0, e_i)` — the
Jacobi field with initial condition `(position, velocity) = (0, e_i)` evaluated at `t = 1`.
Thus the exp-Jacobian matrix *is* the matrix of Jacobi-field positions at `t = 1`, and (together
with EXP-JET3-1's variational law, bundled into the statement) its columns are geodesic
variation fields.

## Honest scope
This brick proves only the entrywise identification `expJacobianMat = position-part of Φ(1)`.
It does **not** yet:
* show `expJacobianMat` satisfies the second-order / covariant matrix Jacobi ODE `Y'' = −R̃ Y`;
* connect `Matrix.det (expJacobianMat …) = expJacobianDet …` along the radial ray;
* discharge the Raychaudhuri `Y` / `hYexp` hypothesis (EXP-JET3-3);
* say anything about `a₁ = R/6`.
Those remain downstream.
-/

set_option maxHeartbeats 1000000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

/-- **EXP-JET3-2 — the exp-Jacobian matrix is the matrix of Jacobi-field positions at `t = 1`.**

Bundles the geodesic-variation flow `Φ` of EXP-JET3-1 (with `Φ 0 = id` and the variational law)
together with the entrywise identity that `expJacobianMat g gi hC p v` equals the matrix whose
`(a,i)` entry is the `a`-component of the position part of `Φ(1)(0, e_i)`. -/
theorem expJacobianMat_eq_flow
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < QIQTH.ExpMap.expRho g gi hC p) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      (∀ (w : Point n × Point n), ∀ t ∈ Set.Icc (0:ℝ) 1,
         HasDerivWithinAt (fun s => (Φ s) w)
           (fderiv ℝ (geodesicField g gi) (QIQTH.ExpMap.expTube g gi hC p v t) ((Φ t) w))
           (Set.Icc (0:ℝ) 1) t) ∧
      QIQTH.JacobianDet.expJacobianMat g gi hC p v
        = fun a i => ((Φ 1) ((0 : Point n), (Pi.single i 1 : Point n))).1 a := by
  obtain ⟨Φ, hΦ0, hFD, hvar⟩ := expDiff_flow_isGeodesicVariation g gi hC p v hv
  refine ⟨Φ, hΦ0, hvar, ?_⟩
  funext a i
  simp only [QIQTH.JacobianDet.expJacobianMat, hFD.fderiv, ContinuousLinearMap.comp_apply,
    expJetIota_apply, expJetPi_apply]

end QIQTH.ExpMap
