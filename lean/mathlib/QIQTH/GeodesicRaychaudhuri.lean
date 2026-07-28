/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# M4-full — the geodesic Raychaudhuri equation `θ' = −Ric(v,v) − tr(Θ²)` (off-center)

This file assembles the campaign's proven pieces into the **physics Raychaudhuri equation**
along the ray, OFF-CENTER (the whole point of the parallel-frame route past the wall M2b-3):
```
  θ' = −Ric(v,v) − tr(Θ²),      θ := tr Θ = tr (Y' Y⁻¹).
```

## What is assembled here

* `QIQTH.MatrixRaychaudhuri.trace_raychaudhuri` (**M4b**): the abstract trace / scalar Raychaudhuri
  equation `θ' = −tr A − tr(Θ²)` from the matrix Jacobi ODE `Y'' = −A Y`, with `A` abstract.
* `QIQTH.ExpMap.frame_jacobi_equation` (**M2b-5**): projecting the off-center covariant Jacobi
  equation onto a parallel orthonormal frame gives, per column, `Yt_k'' = −∑ j R̃_{kj} Yt_j`,
  i.e. the MATRIX Jacobi ODE `Y'' = −R̃ Y` where `R̃_{kj} = ∑_{a,b} g_{ab}(R(e_j,v)v)^a (e_k)^b`.
  (`frameJacobi_matrix_ode` below is the mechanical columnwise → matrix packaging that discharges
  the `hjac : Y'' = −R̃ Y` hypothesis of the milestone.)
* `QIQTH.FrameRicci.frame_ricci_trace` (**M2b-4**): the frame trace of `R̃` is the Ricci quadratic
  form, `tr R̃ = ∑_{σν} R_{σν} v^σ v^ν = Ric(v,v)`, at ANY point (hence along the whole ray).

Substituting `tr A = tr R̃ = Ric(v,v)` into M4b yields the geodesic Raychaudhuri equation.

## Honest scope

`Y` / `Rt` (the matrix Jacobi field + frame curvature) are carried with the ODE `hjac`
(`Y'' = −R̃ Y`) and the trace identity `htr` (`tr R̃ = Ric(v,v)`) as clearly-labeled hypotheses —
neither assumes the conclusion `θ' = −Ric − tr(Θ²)`.  Both are discharged elsewhere: `hjac`
columnwise by `frame_jacobi_equation` (M2b-5, packaged by `frameJacobi_matrix_ode` below), `htr`
by `frame_ricci_trace` (M2b-4).  The parallel orthonormal FRAME existence is still assumed
(that is the separate wall **M2b-2**).  This file does **NOT** relate `θ` to `r∂_r log J` /
the van-Vleck determinant (the M3 / K1 / K2 bridge, next), and is unrelated to the heat-kernel
coefficient `a₁ = R/6` (**M6**).

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.MatrixRaychaudhuri
import QIQTH.FrameJacobiEquation
import QIQTH.FrameRicci
import QIQTH.Curvature

namespace QIQTH.ExpMap

open QIQTH.Curvature Matrix

open scoped Matrix.Norms.Frobenius

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-- **Geodesic Raychaudhuri equation (M4-full milestone) — `θ' = −Ric(v,v) − tr(Θ²)`.**

Given the matrix Jacobi field `Y` (invertible at `τ`, `hu`) obeying the matrix Jacobi ODE
`Y'' τ = −(Rt τ)(Y τ)` (`hjac`), whose frame-curvature source has Ricci trace
`(Rt τ).trace = Ric(v,v) = ∑_{σν} R_{σν} v^σ v^ν` (`htr`), the expansion scalar
`θ := tr(Y' Y⁻¹)` satisfies the geodesic Raychaudhuri equation
```
  θ' = −Ric(v,v) − tr(Θ²),      Θ := Y' Y⁻¹.
```

This is `QIQTH.MatrixRaychaudhuri.trace_raychaudhuri` (M4b) with the abstract trace `(Rt τ).trace`
substituted by the Ricci quadratic form.  The two carried inputs are proven elsewhere and neither
assumes the conclusion: `hjac` (the matrix Jacobi ODE `Y'' = −R̃ Y`) is `QIQTH.ExpMap`'s
`frame_jacobi_equation` (M2b-5) packaged columnwise (see `frameJacobi_matrix_ode`), and `htr`
(`tr R̃ = Ric`) is `QIQTH.FrameRicci.frame_ricci_trace` (M2b-4). -/
theorem geodesic_raychaudhuri (Y Y' Y'' Rt : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (x v : Point n) (g gi : Point n → Fin n → Fin n → ℝ) {τ : ℝ}
    (hY : HasDerivAt Y (Y' τ) τ) (hY' : HasDerivAt Y' (Y'' τ) τ)
    (hjac : Y'' τ = -(Rt τ) * Y τ) (hu : IsUnit (Y τ))
    (htr : (Rt τ).trace = ∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν) :
    HasDerivAt (fun s => (Y' s * (Y s)⁻¹).trace)
      (-(∑ σ, ∑ ν, QIQTH.Curvature.ricci g gi σ ν x * v σ * v ν)
        - ((Y' τ * (Y τ)⁻¹) * (Y' τ * (Y τ)⁻¹)).trace) τ := by
  have h := QIQTH.MatrixRaychaudhuri.trace_raychaudhuri Y Y' Y'' Rt hY hY' hjac hu
  rwa [htr] at h

/-- **Columnwise packaging of the frame Jacobi ODE (discharges `hjac`).**

Assemble a family of frame Jacobi fields into a matrix and show it satisfies the matrix Jacobi
ODE `Y'' = −R̃ Y`.  Here `Yt j k` is the `k`-th frame component of the `j`-th Jacobi field, and
`Rmat τ k i := ∑_{a,b} g_{ab}(R(e_i,v)v)^a (e_k)^b` is the frame curvature matrix; the per-`(j,k)`
frame Jacobi equation `deriv² (Yt j k) τ = −∑ i, Rmat τ k i · Yt j i τ` is exactly
`QIQTH.ExpMap.frame_jacobi_equation` (M2b-5) applied to column `j`.  Packaging the columns into
`Y τ = of (k,j ↦ Yt j k τ)`, `Rt τ = of (k,i ↦ Rmat τ k i)`, `Y'' τ = of (k,j ↦ deriv² (Yt j k) τ)`
gives the matrix equation `Y'' τ = −(Rt τ)(Y τ)`, which is precisely the `hjac` hypothesis of
`geodesic_raychaudhuri`.  Pure `Matrix.ext` + `Matrix.mul_apply` bookkeeping. -/
theorem frameJacobi_matrix_ode
    (Yt : Fin n → Fin n → ℝ → ℝ) (Rmat : ℝ → Fin n → Fin n → ℝ) {τ : ℝ}
    (hjac : ∀ j k, deriv (deriv (Yt j k)) τ = - ∑ i, Rmat τ k i * Yt j i τ) :
    (Matrix.of (fun k j => deriv (deriv (Yt j k)) τ) : Matrix (Fin n) (Fin n) ℝ)
      = -(Matrix.of (fun k i => Rmat τ k i)) * (Matrix.of (fun k j => Yt j k τ)) := by
  ext k j
  rw [Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [hjac j k]

end QIQTH.ExpMap
