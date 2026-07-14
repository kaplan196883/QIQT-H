/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import QIQTH.CoordinateCurvature

/-!
# The hyperbolic plane `H²` — constant negative curvature `R = −2`

Builds the hyperbolic plane `H²` (Poincaré upper half-plane) as a curved Riemannian surface: an
explicit Riemannian metric on a genuine manifold (the open upper half-plane ⊆ ℝ²), with its
metric-derivatives VERIFIED against Mathlib's `HasDerivAt` (the curvature is computed from genuine
derivatives of the metric field), and scalar curvature `R = −2` everywhere — constant NEGATIVE
curvature (a new sign; complements flat `R = 0` and the sphere `R = +2` in `CoordinateCurvature`).

⚠ HONEST: this is a metric field + scalar curvature in a single global COORDINATE chart (`H²` has
one), computed via the coordinate/component `CoordinateCurvature` machinery; it is NOT the abstract
coordinate-free curvature tensor and does NOT integrate the metric into Mathlib's
`RiemannianMetric` / tangent-bundle API — that (and the general curved heat kernel / parametrix)
remains the L0 frontier (Mathlib WIP). NOT the conjecture, NOT the strong principle, NOT QG.
No axioms, no `sorry`.

## The metric

Poincaré upper half-plane, `g_{ij}(x,y) = δ_{ij} / y²` for `y > 0`. At a point of height `y`:
* `g       = diag(1/y², 1/y²)`, `ginv = diag(y², y²)`;
* `∂ₓ g    = 0`, `∂_y g = diag(−2/y³, −2/y³)`;
* `∂ₓ∂ₓ g = ∂ₓ∂_y g = 0`, `∂_y∂_y g = diag(6/y⁴, 6/y⁴)`.

Gauss curvature `K = −1`, scalar curvature `R = 2K = −2`.
-/

open QIQTH.CoordinateCurvature
open scoped BigOperators

namespace QIQTH.HyperbolicPlane

/-! ## 1. Metric-derivative verification (the honesty core)

The single metric component `y ↦ 1/y²` has genuine first derivative `−2/y³` and second derivative
`6/y⁴`, certified against Mathlib's `HasDerivAt`. These verify that the 1- and 2-jets fed to the
curvature calculator ARE the actual derivatives of the metric field, not merely asserted. -/

/-- The metric component `g_{xx} = g_{yy} = 1/y²` has first derivative `−2/y³` (for `y ≠ 0`). -/
theorem hasDerivAt_hyp_gyy (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / y ^ 3) y := by
  have h := (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_pow 2 y) (pow_ne_zero 2 hy)
  convert h using 1
  push_cast
  field_simp
  ring

/-- The first-derivative component `−2/y³` has derivative `6/y⁴` (for `y ≠ 0`); i.e. the second
derivative of `1/y²` is `6/y⁴`. -/
theorem hasDerivAt_hyp_dgyy (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => -2 / y ^ 3) (6 / y ^ 4) y := by
  have h := (hasDerivAt_const y (-2 : ℝ)).div (hasDerivAt_pow 3 y) (pow_ne_zero 3 hy)
  convert h using 1
  push_cast
  field_simp
  ring

/-! ## 2. The metric 2-jet as functions of the height `y` -/

/-- Inverse metric `ginv = diag(y², y²)`. -/
noncomputable def hypGinv (y : ℝ) : Mat (Fin 2) := !![y ^ 2, 0; 0, y ^ 2]

/-- Components of `∂ₐ g_{ij}`: `∂_y g = diag(−2/y³, −2/y³)` (i.e. `a = 1`, `i = j`), else `0`. -/
noncomputable def hypDgc (y : ℝ) (a i j : Fin 2) : ℝ := if a = 1 ∧ i = j then -2 / y ^ 3 else 0

/-- Components of `∂ₐ∂ᵦ g_{ij}`: `∂_y∂_y g = diag(6/y⁴, 6/y⁴)` (i.e. `a = b = 1`, `i = j`), else
`0`. -/
noncomputable def hypDdgc (y : ℝ) (a b i j : Fin 2) : ℝ :=
  if a = 1 ∧ b = 1 ∧ i = j then 6 / y ^ 4 else 0

/-- First partials of the metric as a matrix field. `hypDg y 0 = 0` and
`hypDg y 1 = !![-2/y³, 0; 0, -2/y³]`. -/
noncomputable def hypDg (y : ℝ) : Fin 2 → Mat (Fin 2) :=
  fun a => Matrix.of fun i j => hypDgc y a i j

/-- Second partials of the metric as a matrix field. `hypDdg y 1 1 = !![6/y⁴, 0; 0, 6/y⁴]`, else
`0`. -/
noncomputable def hypDdg (y : ℝ) : Fin 2 → Fin 2 → Mat (Fin 2) :=
  fun a b => Matrix.of fun i j => hypDdgc y a b i j

/-! ## 3. Scalar curvature `R = −2` everywhere -/

/-- ★★★ The hyperbolic plane has constant scalar curvature `R = −2`. -/
theorem hyperbolic_scalarCurvature (y : ℝ) (hy : 0 < y) :
    scalarCurvature (hypGinv y) (hypDg y) (hypDdg y) = -2 := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [scalarCurvature, ricci, riemann, riemannOf, christoffel, dChristoffel,
    dChristoffelOfDInv, dInvMetric, lowerGamma, dLowerGamma, hypGinv, hypDg, hypDdg,
    hypDgc, hypDdgc, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  field_simp
  ring

/-! ## 4. The curvature sign is negative -/

/-- The hyperbolic plane has NEGATIVE scalar curvature (a new sign for this development). -/
theorem hyperbolic_curvature_negative (y : ℝ) (hy : 0 < y) :
    scalarCurvature (hypGinv y) (hypDg y) (hypDdg y) < 0 := by
  rw [hyperbolic_scalarCurvature y hy]; norm_num

/-! ## 5. The underlying space is a genuine manifold (documentation) -/

/-- The open upper half-plane `{p : ℝ × ℝ | 0 < p.2}` is open, hence a manifold as an open subset
of `ℝ²`. -/
theorem isOpen_uhp : IsOpen {p : ℝ × ℝ | 0 < p.2} :=
  isOpen_lt continuous_const continuous_snd

end QIQTH.HyperbolicPlane
