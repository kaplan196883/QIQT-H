/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Log-det bridge — the Jacobi determinant `log det Y` obeys the geodesic Raychaudhuri equation

This file connects the **Raychaudhuri expansion scalar** `θ := tr(Y' Y⁻¹)` to the log-derivative
of the Jacobi determinant, and then packages the geodesic Raychaudhuri equation as the second-order
behaviour of the potential `log det Y`:
```
  d/dτ log det Y = tr(Y' Y⁻¹) = θ            (M4a, the regularized expansion)
  θ'             = −Ric(v,v) − tr(Θ²)         (M4-full geodesic Raychaudhuri, Θ := Y' Y⁻¹)
```
So the *first* derivative of the Jacobi-determinant potential `log det Y` is the expansion `θ`, and
that expansion obeys the geodesic Raychaudhuri equation. This is exactly the determinant form that
connects to the van-Vleck determinant.

## Assembly

* `QIQTH.JacobiFormula.hasDerivAt_log_det_matrix` (**M4a**): `d/dτ log det W = tr((W τ)⁻¹ · W' τ)`.
  Its derivative is written with the LEFT product `(Y τ)⁻¹ * Y' τ`; we rewrite to the RIGHT product
  `Y' τ * (Y τ)⁻¹` (matching `geodesic_raychaudhuri`'s `Θ`) via `Matrix.trace_mul_comm`.
* `QIQTH.ExpMap.geodesic_raychaudhuri` (**M4-full**): `θ' = −Ric(v,v) − tr(Θ²)`.

## Honest scope

This works with the **abstract matrix** `Y` (the matrix Jacobi field). The geometric identification
`Y = D exp_p`, which connects `det Y` to the exp-Jacobian `J` and thence to `det g̃` (the K1/K2
bridge), is the NEXT step and is **not** performed here. In particular this file does **NOT** give
the van-Vleck radial ODE `r∂_r log det g̃ → Ric`, and is unrelated to the heat-kernel coefficient
`a₁ = R/6` (**M6**).

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.JacobiFormula
import QIQTH.GeodesicRaychaudhuri
import QIQTH.Curvature

namespace QIQTH.ExpMap

open QIQTH.Curvature Matrix

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- **Log-det first derivative = the Raychaudhuri expansion `θ` (M4a bridge).**

For an invertible matrix Jacobi field `Y` with `HasDerivAt Y (Y' τ) τ`, the log-determinant
potential has derivative equal to the expansion scalar
```
  d/dτ log det Y = tr(Y' Y⁻¹) = θ.
```
This is `QIQTH.JacobiFormula.hasDerivAt_log_det_matrix`, whose derivative is stated with the LEFT
product `(Y τ)⁻¹ * Y' τ`, rewritten to the RIGHT product `Y' τ * (Y τ)⁻¹` via `Matrix.trace_mul_comm`
so it matches the `Θ := Y' Y⁻¹` used in `geodesic_raychaudhuri`. -/
theorem raychaudhuri_logdet_firstderiv (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hu : IsUnit (Y τ)) :
    HasDerivAt (fun s => Real.log (Y s).det) ((Y' τ * (Y τ)⁻¹).trace) τ := by
  have h := QIQTH.JacobiFormula.hasDerivAt_log_det_matrix Y Y' hY
    ((Matrix.isUnit_iff_isUnit_det (Y τ)).mp hu)
  rwa [Matrix.trace_mul_comm] at h

/-- **The Jacobi-determinant potential `log det Y` obeys the geodesic Raychaudhuri equation.**

Packaging `raychaudhuri_logdet_firstderiv` (M4a) with `geodesic_raychaudhuri` (M4-full): the first
derivative of the potential `log det Y` is the expansion `θ := tr(Y' Y⁻¹)`, and that expansion `θ`
satisfies
```
  θ' = −Ric(v,v) − tr(Θ²),      Θ := Y' Y⁻¹.
```
So the Jacobi-determinant potential `log det Y` has expansion `θ` obeying the geodesic Raychaudhuri
equation — the determinant form that connects to the van-Vleck determinant. The carried hypotheses
(`hjac` the matrix Jacobi ODE `Y'' = −R̃ Y`, `htr` the Ricci trace `tr R̃ = Ric(v,v)`) are those of
`geodesic_raychaudhuri`, discharged elsewhere in the campaign. -/
theorem raychaudhuri_logdet (Y Y' Y'' Rt : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (x v : Point n) (g gi : Point n → Fin n → Fin n → ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hY' : HasDerivAt Y' (Y'' τ) τ)
    (hjac : Y'' τ = -(Rt τ) * Y τ) (hu : IsUnit (Y τ))
    (htr : (Rt τ).trace = ∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν) :
    HasDerivAt (fun s => Real.log (Y s).det) ((Y' τ * (Y τ)⁻¹).trace) τ
    ∧ HasDerivAt (fun s => (Y' s * (Y s)⁻¹).trace)
        (-(∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν)
          - ((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace) τ :=
  ⟨raychaudhuri_logdet_firstderiv Y Y' hY hu,
   geodesic_raychaudhuri Y Y' Y'' Rt x v g gi hY hY' hjac hu htr⟩

end QIQTH.ExpMap
