/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Frame-route CAPSTONE — the `−Ric` Raychaudhuri equation `θ' = −Ric − tr(Θ²)`
  for the exp-flow frame Jacobi field.

This file is the CAPSTONE of the frame-route sub-campaign: it assembles the four already-built
pieces into the geodesic Raychaudhuri equation

  `θ' = −Ric(γ',γ') − tr(Θ²)`,     `θ := tr Θ = tr (Y' Y⁻¹)`,     `Θ := Y' Y⁻¹`,

along the exp geodesic `γ`, evaluated at an interior parameter `t`, with the matrix Jacobi field
`Y s := of (k, j ↦ Yt j k s)` assembled from a family of frame Jacobi fields `Yt j` (the `j`-th
Jacobi field, `k`-th frame component, parameter `s`).

## What is assembled here

* `QIQTH.ExpMap.frame_jacobi_equation_nhds` (localized frame Jacobi ODE): projected onto the
  parallel orthonormal frame, each column `j` obeys `deriv² (Yt j k) t = −∑ i R̃_{ki} Yt j i t`.
* `QIQTH.ExpMap.frameJacobi_matrix_ode`: packages the per-column ODEs into the matrix ODE
  `Y'' t = −(R̃ t)(Y t)`.
* `QIQTH.FrameRicci.frame_ricci_trace`: the frame trace of the curvature matrix is Ricci,
  `(R̃ t).trace = ∑_{σν} R_{σν} v^σ v^ν = Ric(v,v)`.
* `QIQTH.ExpMap.geodesic_raychaudhuri`: the abstract trace/Jacobi Raychaudhuri identity, fed the
  matrix ODE (`hjac`) and the Ricci trace (`htr`), yields `θ' = −Ric − tr(Θ²)`.

## Honest scope

This is a pure ASSEMBLY.  The parallel orthonormal FRAME data — component regularity (`hY`, `hY2`),
frame regularity (`he`), parallelism (`hpar`), orthonormality (`hortho`) + completeness
(`hcomplete`, `hinv`), and the frame decomposition of the variation fields (`hexp`) — as well as the
matrix regularity (`hYmat`, `hY'mat`, which follow from `hY`/`hY2` via `hasDerivAt_pi` but are
carried honestly to keep this brick an assembly) and the no-conjugate invertibility (`hu`) are all
carried as clearly-labeled hypotheses.  Every carried hypothesis is a genuine mathematical statement
(a `HasDerivAt`, an orthonormality/completeness identity, an `IsUnit`), NONE is `True`/vacuous, and
none assumes the conclusion.

This file does **NOT** construct the parallel orthonormal frame (the M2b-2 ODE-existence wall, still
carried), does **NOT** relate `θ_Y` to the coordinate exp-differential `θ_B` / the real van-Vleck
determinant `J`, and is unrelated to the heat-kernel coefficient `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.FrameJacobiEquationNhds
import QIQTH.GeodesicRaychaudhuri
import QIQTH.FrameRicci

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic Finset Matrix

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **Frame-route capstone — the `−Ric` Raychaudhuri equation for the exp-flow frame Jacobi field.**

Along the exp geodesic `γ`, let `Yt j k` be the `k`-th parallel-frame component of the `j`-th
Jacobi field, assembled into the matrix Jacobi field `Y s := of (k,j ↦ Yt j k s)` with derivatives
`Y' s := of (k,j ↦ deriv (Yt j k) s)`.  Under the carried frame data (regularity `hY`, `hY2`, `he`;
parallelism `hpar`; orthonormality `hortho`; completeness `hcomplete`, `hinv`; frame decomposition
`hexp`), the matrix regularity `hYmat`, `hY'mat`, and the no-conjugate invertibility `hu`, the
expansion scalar `θ := tr(Y' Y⁻¹)` obeys the geodesic Raychaudhuri equation

  `θ'(t) = −Ric(γ'(t), γ'(t)) − tr(Θ(t)²)`,     `Θ := Y' Y⁻¹`.

Assembled from `frame_jacobi_equation_nhds` (per-column frame Jacobi ODE) packaged by
`frameJacobi_matrix_ode` into the matrix ODE `hjac`, `frame_ricci_trace` supplying the Ricci trace
`htr`, and `geodesic_raychaudhuri` combining them.  Conditional on the carried frame data; does not
construct the frame, connect `θ` to the van-Vleck determinant, or derive `a₁ = R/6`. -/
theorem frame_raychaudhuri_ricci_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ : ℝ → Point n × Point n} {t : ℝ}
    (V : Fin n → ℝ → Point n × Point n)
    (hγ : ∀ᶠ τ in nhds t, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ j, ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ (V j) τ)
    (e : Fin n → ℝ → Point n) (Yt : Fin n → Fin n → ℝ → ℝ)
    (hY : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (Yt j i) (deriv (Yt j i) τ) τ)
    (hY2 : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (deriv (Yt j i)) (deriv (deriv (Yt j i)) τ) τ)
    (he : ∀ i a, ∀ᶠ τ in nhds t, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds t, covariantDerivAlong g gi (fun τ => (γ τ).1) (e i) τ = 0)
    (hortho : ∀ i k, (∑ a, ∑ b, g (γ t).1 a b * e i t a * e k t b) = if i = k then (1:ℝ) else 0)
    (hcomplete : ∀ μ b, (∑ i, e i t μ * e i t b) = gi (γ t).1 μ b)
    (hinv : ∀ a μ, (∑ b, g (γ t).1 a b * gi (γ t).1 μ b) = if a = μ then (1:ℝ) else 0)
    (hexp : ∀ j, (fun s => fun a => ∑ i, Yt j i s * e i s a) =ᶠ[nhds t] (fun s => (V j s).1))
    (hYmat : HasDerivAt (fun s => (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (Yt j k) t)) t)
    (hY'mat : HasDerivAt
              (fun s => (Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (deriv (Yt j k)) t)) t)
    (hu : IsUnit (Matrix.of (fun k j => Yt j k t) : Matrix (Fin n) (Fin n) ℝ)) :
    HasDerivAt
      (fun s => ((Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ)
                  * (Matrix.of (fun k j => Yt j k s))⁻¹).trace)
      (-(∑ σ, ∑ ν, ricci g gi σ ν (γ t).1 * (γ t).2 σ * (γ t).2 ν)
        - (((Matrix.of (fun k j => deriv (Yt j k) t) : Matrix (Fin n) (Fin n) ℝ)
              * (Matrix.of (fun k j => Yt j k t))⁻¹)
            * ((Matrix.of (fun k j => deriv (Yt j k) t))
              * (Matrix.of (fun k j => Yt j k t))⁻¹)).trace)
      t := by
  -- per-column frame Jacobi ODE `deriv² (Yt j k) t = −∑ i R̃_{ki} Yt j i t`.
  have hjaccol : ∀ j k,
      deriv (deriv (Yt j k)) t
        = - ∑ i, (∑ a, ∑ b, g (γ t).1 a b
            * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e i t)) a * e k t b) * Yt j i t := by
    intro j k
    exact frame_jacobi_equation_nhds g gi hC hgsymm hγ (hVar j) e (Yt j)
      (hY j) (hY2 j) he hpar hortho (hexp j) k
  -- package the columns into the matrix Jacobi ODE `Y'' t = −(R̃ t)(Y t)`.
  have hjacmat := frameJacobi_matrix_ode Yt
    (fun τ k i => ∑ a, ∑ b, g (γ τ).1 a b
        * (riemannGeodesicDeviation g gi (γ τ).1 (γ τ).2 (e i τ)) a * e k τ b)
    (τ := t) hjaccol
  -- the frame trace of the curvature matrix is the Ricci quadratic form.
  have htr : (Matrix.of (fun k i => (∑ a, ∑ b, g (γ t).1 a b
        * (riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (e i t)) a * e k t b))
        : Matrix (Fin n) (Fin n) ℝ).trace
      = ∑ σ, ∑ ν, ricci g gi σ ν (γ t).1 * (γ t).2 σ * (γ t).2 ν := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    exact QIQTH.FrameRicci.frame_ricci_trace g gi (γ t).1 (γ t).2 (fun i => e i t) hcomplete hinv
  -- combine via the abstract Raychaudhuri identity.
  exact geodesic_raychaudhuri
    (fun s => (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ))
    (fun s => Matrix.of (fun k j => deriv (Yt j k) s))
    (fun s => Matrix.of (fun k j => deriv (deriv (Yt j k)) s))
    (fun s => Matrix.of (fun k i => (∑ a, ∑ b, g (γ s).1 a b
        * (riemannGeodesicDeviation g gi (γ s).1 (γ s).2 (e i s)) a * e k s b)))
    (γ t).1 (γ t).2 g gi (τ := t) hYmat hY'mat hjacmat hu htr

end QIQTH.ExpMap
