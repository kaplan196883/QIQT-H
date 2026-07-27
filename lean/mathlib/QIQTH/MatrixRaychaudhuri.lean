/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Abstract matrix Raychaudhuri / Riccati equation (phase M4b)

From the **matrix Jacobi ODE** `Y'' = −A(τ) Y` (with `A` an *abstract* matrix-valued curvature
source, and `Y` invertible at the point in question), the **expansion tensor** `Θ := Y' Y⁻¹`
satisfies the **matrix Riccati equation**
```
  Θ' = −A − Θ² ,
```
and, taking the trace, the scalar `θ := tr Θ` satisfies the **Raychaudhuri equation**
```
  θ' = −tr A − tr(Θ²) .
```
The computation is the textbook one: with `(Y⁻¹)' = −Y⁻¹ Y' Y⁻¹` and `Y'' = −A Y`,
```
  Θ' = Y'' Y⁻¹ + Y' (Y⁻¹)'
     = (−A Y) Y⁻¹ + Y' (−Y⁻¹ Y' Y⁻¹)
     = −A (Y Y⁻¹) − (Y' Y⁻¹)(Y' Y⁻¹)
     = −A − Θ² .
```

## Honest scope

`A` is **abstract**.  This file provides only the *algebraic/analytic* Raychaudhuri equation from an
assumed matrix Jacobi ODE.  It does **not**:

* derive the matrix Jacobi ODE `Y'' = −R(τ) Y` from the geometry, nor identify `Y` with the
  differential of the exponential map `D exp_p` (this is the off-radial wall **M2b**);
* establish that the source `tr A` equals the Ricci curvature `Ric(v,v)` along the geodesic
  (the scalar/constant-curvature case is `QIQTH.RaychaudhuriConstCurv.jacobi_logderiv_riccati`,
  and the Ricci source term is `QIQTH.ExpMap.covariantJacobi_trace_at_center`);
* give the heat-kernel coefficient `a₁ = R/6` (**M6**).

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib

namespace QIQTH.MatrixRaychaudhuri

open Matrix

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- **Derivative of the matrix inverse along a curve.**
If `Y : ℝ → Matrix (Fin n) (Fin n) ℝ` is differentiable at `τ` with derivative `Y' τ`, and `Y τ` is
invertible (a unit), then `s ↦ (Y s)⁻¹` is differentiable at `τ` with derivative
`−(Y τ)⁻¹ (Y' τ) (Y τ)⁻¹`.

The proof composes the Mathlib derivative of `Ring.inverse` at a unit of a complete normed algebra
(`hasFDerivAt_ringInverse`, whose Fréchet derivative is `t ↦ −x⁻¹ t x⁻¹ = −mulLeftRight ℝ _ x⁻¹ x⁻¹`)
with `hY`, and bridges the nonsingular matrix inverse to `Ring.inverse` via
`Matrix.nonsing_inv_eq_ringInverse` (unconditional, so no neighbourhood argument is needed). -/
theorem hasDerivAt_matrix_inv (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hu : IsUnit (Y τ)) :
    HasDerivAt (fun s => (Y s)⁻¹) (-(Y τ)⁻¹ * Y' τ * (Y τ)⁻¹) τ := by
  -- Pick the unit witnessing `IsUnit (Y τ)`.
  set u := hu.unit with hu_def
  have hus : (↑u : Matrix (Fin n) (Fin n) ℝ) = Y τ := hu.unit_spec
  have hui : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) = (Y τ)⁻¹ := by
    rw [Matrix.coe_units_inv, hus]
  -- The Fréchet derivative of `Ring.inverse` at the unit `Y τ`.
  have hRing : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) ℝ) (↑u⁻¹) (↑u⁻¹)) (Y τ) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [hus] at this
  -- Compose with `hY`.
  have hcomp := hRing.comp_hasDerivAt τ hY
  -- Rewrite `Ring.inverse ∘ Y` as `s ↦ (Y s)⁻¹`.
  have hfun : (Ring.inverse ∘ Y) = fun s => (Y s)⁻¹ := by
    funext s; exact (Matrix.nonsing_inv_eq_ringInverse (Y s)).symm
  rw [hfun] at hcomp
  -- Identify the derivative value.
  convert hcomp using 1
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui]
  noncomm_ring

/-- **Matrix Riccati equation.**
From the matrix Jacobi ODE `Y'' τ = −(A τ)(Y τ)` (with `Y τ` a unit), the expansion `Θ := Y' Y⁻¹`
satisfies `Θ' = −A − Θ²`, i.e.
`s ↦ Y' s (Y s)⁻¹` has derivative `−(A τ) − (Y' τ (Y τ)⁻¹)²` at `τ`. -/
theorem matrix_riccati (Y Y' Y'' A : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hY' : HasDerivAt Y' (Y'' τ) τ)
    (hjac : Y'' τ = -(A τ) * Y τ) (hu : IsUnit (Y τ)) :
    HasDerivAt (fun s => Y' s * (Y s)⁻¹)
      (-(A τ) - (Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)) τ := by
  have hinv := hasDerivAt_matrix_inv Y Y' hY hu
  have hmul : HasDerivAt (fun s => Y' s * (Y s)⁻¹)
      (Y'' τ * (Y τ)⁻¹ + Y' τ * (-(Y τ)⁻¹ * Y' τ * (Y τ)⁻¹)) τ := hY'.mul hinv
  -- Cancellation `Y τ * (Y τ)⁻¹ = 1` from invertibility.
  have hdet : IsUnit (Y τ).det := (Matrix.isUnit_iff_isUnit_det (Y τ)).mp hu
  have hc : Y τ * (Y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv (Y τ) hdet
  convert hmul using 1
  rw [hjac]
  have e1 : -(A τ) * Y τ * (Y τ)⁻¹ = -(A τ) := by
    rw [mul_assoc, hc, mul_one]
  have e2 : Y' τ * (-(Y τ)⁻¹ * Y' τ * (Y τ)⁻¹)
      = -((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)) := by
    noncomm_ring
  rw [e1, e2, sub_eq_add_neg]

/-- **Trace / scalar Raychaudhuri equation.**
Taking the trace of the matrix Riccati equation: `θ := tr Θ = tr (Y' Y⁻¹)` satisfies
`θ' = −tr A − tr(Θ²)`, i.e. `s ↦ (Y' s (Y s)⁻¹).trace` has derivative
`−(A τ).trace − ((Y' τ (Y τ)⁻¹)²).trace` at `τ`.

The trace is a continuous linear map (finite-dimensional), so it commutes with the derivative and
distributes over `−A − Θ²` by linearity. -/
theorem trace_raychaudhuri (Y Y' Y'' A : ℝ → Matrix (Fin n) (Fin n) ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hY' : HasDerivAt Y' (Y'' τ) τ)
    (hjac : Y'' τ = -(A τ) * Y τ) (hu : IsUnit (Y τ)) :
    HasDerivAt (fun s => (Y' s * (Y s)⁻¹).trace)
      (-(A τ).trace - ((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace) τ := by
  have hric := matrix_riccati Y Y' Y'' A hY hY' hjac hu
  -- Trace as a continuous linear map (finite-dimensional domain).
  set L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap with hL
  have hcomp := (L.hasFDerivAt.comp_hasDerivAt τ hric)
  -- `⇑L = Matrix.trace`.
  have hLcoe : ∀ x : Matrix (Fin n) (Fin n) ℝ, L x = x.trace := fun x => rfl
  -- Rewrite the composed function to the trace form.
  have hfun : (⇑L ∘ fun s => Y' s * (Y s)⁻¹) = fun s => (Y' s * (Y s)⁻¹).trace := by
    funext s; exact hLcoe _
  rw [hfun] at hcomp
  -- `L` applied to `−A − Θ²` is (definitionally) `(−A − Θ²).trace`, which distributes.
  have hLval : L (-(A τ) - (Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹))
      = -(A τ).trace - ((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace := by
    show (-(A τ) - (Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace = _
    rw [Matrix.trace_sub, Matrix.trace_neg]
  rw [show (-(A τ).trace - ((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace)
      = L (-(A τ) - (Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)) from hLval.symm]
  exact hcomp

end QIQTH.MatrixRaychaudhuri
