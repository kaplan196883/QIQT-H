import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicVariation

/-!
# EXP-JET3-1 — the columns of `D exp_p` are Jacobi fields (geodesic variation flow)

This is the FOUNDATION of the `Y = D exp` identification
(`docs/qg_roadmap/MATRIX_JACOBI_PLAN.md`).

The differential of the exponential map is produced (in `hasFDerivAt_expMap`) as the
time-`1` value of an **operator flow** `Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))`
satisfying the linearized (CLM-valued) geodesic ODE
`Φ'(t) = expJetPsi t (Φ t) = DF(expTube t) ∘ Φ(t)` (within `[0,1]`), with `Φ 0 = id` and
`fderiv exp_p v = π ∘ Φ(1) ∘ ι`, `F = geodesicField`, `DF = fderiv ℝ F`.

Evaluating this operator flow at a **fixed** direction `w : Point n × Point n` gives the
vector field `V_w(t) := (Φ t) w`.  Because evaluation-at-`w` is a continuous linear map, `V_w`
inherits the flow's derivative law:

  `V_w'(t) = (Φ'(t)) w = (DF(expTube t) ∘ Φ(t)) w = DF(expTube t) (V_w t)`  (within `[0,1]`).

This is exactly the geodesic variational (first-order Jacobi) equation
`V' = DF(γ)·V` of `QIQTH.ExpMap.IsGeodesicVariationAt` along the geodesic phase-space tube
`γ = expTube p v`.  So the columns of `D exp_p` are Jacobi fields.

## Scope (stated honestly)
* This brick establishes ONLY the variational-field property of the exp-differential flow
  applied to a fixed direction (within `[0,1]`).
* It does NOT yet assemble the columns into `expJacobianMat` as a matrix Jacobi field, NOR
  prove `det Y = expJacobianDet` — those are later EXP-JET3 bricks.
* It does NOT discharge `hYexp` in the van-Vleck bridge, and it is NOT `a₁ = R/6`.
* The flow law is stated with `HasDerivWithinAt … (Set.Icc 0 1)` — the honest within-interval
  form matching `Φ`'s law — NOT full `HasDerivAt` (which the endpoints do not supply).
-/

set_option maxHeartbeats 1000000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **EXP-JET3-1 — the exp-differential flow, applied to a fixed direction, is a geodesic
variation field.**

`hasFDerivAt_expMap` produces the operator flow `Φ` with `Φ 0 = id`,
`fderiv exp_p v = π ∘ Φ(1) ∘ ι`, and the linearized law `Φ'(t) = DF(expTube t) ∘ Φ(t)`
(within `[0,1]`).  For any fixed `w`, the field `V_w(t) = (Φ t) w` then satisfies
`V_w'(t) = DF(expTube t) (V_w t)` (within `[0,1]`) — the geodesic variational equation along
the geodesic tube `expTube p v`.  Hence the columns of `D exp_p` are Jacobi fields. -/
theorem expDiff_flow_isGeodesicVariation
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < QIQTH.ExpMap.expRho g gi hC p) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      HasFDerivAt (QIQTH.ExpMap.expMap g gi hC p)
        (QIQTH.ExpMap.expJetPi.comp ((Φ 1).comp QIQTH.ExpMap.expJetIota)) v ∧
      (∀ (w : Point n × Point n), ∀ t ∈ Set.Icc (0:ℝ) 1,
         HasDerivWithinAt (fun s => (Φ s) w)
           (fderiv ℝ (geodesicField g gi) (QIQTH.ExpMap.expTube g gi hC p v t) ((Φ t) w))
           (Set.Icc (0:ℝ) 1) t) := by
  obtain ⟨Φ, hΦ0, hΦderiv, hFD⟩ := hasFDerivAt_expMap g gi hC p v hv
  refine ⟨Φ, hΦ0, hFD, ?_⟩
  intro w t ht
  -- The flow law at `t`: `Φ'(t) = DF(expTube t) ∘ Φ(t)` within `[0,1]`.
  have hΦt : HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0:ℝ) 1) t :=
    hΦderiv t ht
  -- Evaluation-at-`w` is a CLM; compose to differentiate `V_w(s) = (Φ s) w`.
  have hcomp :=
    (ContinuousLinearMap.apply ℝ (Point n × Point n) w).hasFDerivAt.comp_hasDerivWithinAt t hΦt
  -- Rewrite both the function `(apply w) ∘ Φ = fun s => (Φ s) w` and the derivative value
  -- `(apply w) (DF(expTube t) ∘ Φ t) = DF(expTube t) ((Φ t) w)`.
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, expJetPsi_apply,
    ContinuousLinearMap.comp_apply] using hcomp

end QIQTH.ExpMap
