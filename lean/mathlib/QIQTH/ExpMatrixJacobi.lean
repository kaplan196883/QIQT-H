import Mathlib
import QIQTH.ExpDiffVariation
import QIQTH.ExpJacobianFlow
import QIQTH.JacobianDet

/-!
# The exp-derived matrix Jacobi field `B(t)` (EXP-JET3 B-side)

This file records the **matrix Jacobi field** built from the geodesic-variation flow `Φ_v` of
`expDiff_flow_isGeodesicVariation` (EXP-JET3-1) / `expJacobianMat_eq_flow` (EXP-JET3-2).  For the
flow `Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))` (with `Φ 0 = id` and the geodesic
first-variation law on `[0,1]`), define the `n × n` matrix

    `B(t) := Matrix.of (fun a i => ((Φ t) ((0 : Point n), (Pi.single i 1 : Point n))).1 a)`,

whose `i`-th **column** is the *position part* `π (Φ_t (0, e_i))` of the geodesic-variation Jacobi
field launched with initial velocity `e_i` (and zero initial position).  `B` is the matrix whose
columns solve the (first-order, position-part) Jacobi flow along the radial geodesic
`t ↦ expTube p v t`.

## What landed (FLOOR — endpoints + flow), axiom-free (std-3)

* `expMatrixJacobi_flow` — ONE existential bundling the flow `Φ` of EXP-JET3-1/2 together with:
  - `Φ 0 = id`;
  - the geodesic first-variation law `d/dt (Φ_t w) = DF(expTube t)·(Φ_t w)` on `[0,1]`
    (`F = geodesicField`);
  - **`B(0) = 0`** — the position part of the Jacobi field vanishes at the source (`Φ 0 = id`,
    `(id (0, e_i)).1 = 0`);
  - **`B(1) = expJacobianMat g gi hC p v`** — the endpoint matrix Jacobi field IS the exp-map
    Jacobian matrix (EXP-JET3-2, re-bundled entrywise through `Matrix.of`).

These are exactly the two endpoint boundary conditions of a matrix Jacobi field: `B(0) = 0` (the
variations emanate from the common source `p`) and `B(1) = D exp_p v` (the endpoint spread is the
exp-map differential).

## What is CHECKPOINTED (TARGET — the interior second-order matrix Jacobi ODE)

The deep target is the interior curvature/covariant form

    `B''(t) = − R̃(t) · B(t)`   on `(0,1)`

(`R̃` the tidal / directional-curvature endomorphism), which is what discharges the B-side
hypotheses of the van-Vleck Ricci radial ODE `vanVleck_radialDeriv_ricci_form` (it needs a `B` with
expansion-derivative `θ_B' = −Ric` obtained by tracing `B'' = −R̃ B`).  This is NOT landed here.
The precise gap:

  1. **Interior second derivative.**  The flow `Φ` is only supplied as `HasDerivWithinAt … (Icc 0 1)`
     (first order).  Getting `B''` requires differentiating the coefficient
     `t ↦ fderiv (geodesicField g gi) (expTube … t) ((Φ t) w)` a second time — i.e. joint
     `C¹`-in-`t` regularity of `expTube` and of the flow `Φ`, plus a chain rule — which the
     first-variation law alone does not expose.
  2. **Covariant identification (M2b-3).**  Even given the coordinate `B''`, rewriting the
     first-order geodesic-field Jacobian `DF` into the second-order *covariant* Jacobi operator
     `−R̃` (the tidal endomorphism `jacobiOperator`) needs the M2b-3 covariant-identification step.
  3. **`∀τ`-vs-`[0,1]` restriction.**  `covariant_jacobi_equation` (M2b-3) requires GLOBAL `∀τ`
     hypotheses `hγ`/`hVar`; the flow here supplies them only on `[0,1]` (resp. the exp tube's
     `(-2,2)` window), so it must be adapted to `derivWithin`/interior form before it applies.

None of (1)–(3) is `sorry`'d or faked below.  This file is the honest B-side FLOOR: the flow plus
its two endpoints.  It does **not** claim `B'' = −R̃ B`, and it does **not** claim `a₁ = R/6`.
-/

set_option maxHeartbeats 2000000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

/-- **The exp-derived matrix Jacobi field `B(t)`, with its flow and endpoints.**

Bundles the geodesic-variation flow `Φ` (EXP-JET3-1 / `expJacobianMat_eq_flow`, EXP-JET3-2) with:
* `Φ 0 = id`;
* the geodesic first-variation (Jacobi) law on `[0,1]`;
* `B(0) = 0` — the position part of the flow's Jacobi field vanishes at the source `p`
  (immediate from `Φ 0 = id`);
* `B(1) = expJacobianMat g gi hC p v` — the endpoint matrix Jacobi field is the exp-map Jacobian
  matrix,

where `B(t) := Matrix.of (fun a i => ((Φ t) ((0, e_i))).1 a)` has as its `i`-th column the position
part of `Φ_t (0, e_i)` (`e_i = Pi.single i 1`).

This is the reachable B-side FLOOR of the matrix-Jacobi endgame: the two boundary conditions of the
matrix Jacobi field, obtained purely from EXP-JET3-1/2.  The interior second-order ODE
`B'' = −R̃ B` is CHECKPOINTED (see the module docstring), not proved. -/
theorem expMatrixJacobi_flow
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < QIQTH.ExpMap.expRho g gi hC p) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      (∀ (w : Point n × Point n), ∀ t ∈ Set.Icc (0:ℝ) 1,
         HasDerivWithinAt (fun s => (Φ s) w)
           (fderiv ℝ (geodesicField g gi) (QIQTH.ExpMap.expTube g gi hC p v t) ((Φ t) w))
           (Set.Icc (0:ℝ) 1) t) ∧
      (Matrix.of (fun a i => ((Φ 0) ((0 : Point n), (Pi.single i 1 : Point n))).1 a)
        : Matrix (Fin n) (Fin n) ℝ) = 0 ∧
      (Matrix.of (fun a i => ((Φ 1) ((0 : Point n), (Pi.single i 1 : Point n))).1 a)
        : Matrix (Fin n) (Fin n) ℝ)
        = QIQTH.JacobianDet.expJacobianMat g gi hC p v := by
  obtain ⟨Φ, hΦ0, hvar, heq⟩ := expJacobianMat_eq_flow g gi hC p v hv
  refine ⟨Φ, hΦ0, hvar, ?_, ?_⟩
  · -- `B(0) = 0`: from `Φ 0 = id`, `(id (0, e_i)).1 = 0`.
    ext a i
    simp only [Matrix.of_apply, hΦ0, ContinuousLinearMap.id_apply, Matrix.zero_apply,
      Pi.zero_apply]
  · -- `B(1) = expJacobianMat`: restate EXP-JET3-2 through `Matrix.of`.
    ext a i
    rw [heq]
    rfl

end QIQTH.ExpMap
