/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import QIQTH.CoordinateCurvature

/-!
# A surface of revolution `ds² = dr² + (1+r²)² dθ²` — NONCONSTANT curvature `R(r) = −4/(1+r²)`

Builds a rotationally-symmetric surface of revolution (`ds² = dr² + (1+r²)² dθ²`, profile
`f(r) = 1+r²`) — the first INHOMOGENEOUS curved manifold in the repo, with NONCONSTANT scalar
curvature `R(r) = −4/(1+r²)` (varies from `−4` at `r = 0` toward `0` at infinity), metric-derivatives
VERIFIED via Mathlib `HasDerivAt`, computed via the component `CoordinateCurvature` machinery.
Complements the constant-curvature examples (flat `R = 0`, sphere `R = +2`, hyperbolic `R = −2`) by
demonstrating the curvature machine on a genuinely varying curvature field.

⚠ HONEST: metric field + scalar curvature in ONE global coordinate chart, coordinate/component
curvature — NOT the abstract coordinate-free curvature tensor, NOT integrated into Mathlib's
`RiemannianMetric` API — that (and the general curved heat kernel) is the L0/parametrix frontier
(Mathlib WIP). NOT the conjecture, NOT the strong principle, NOT QG. No axioms, no `sorry`.

## The metric

Surface of revolution `ds² = dr² + f(r)² dθ²` with profile `f(r) = 1 + r²`; index `0 = r`,
`1 = θ`. Write `h(r) := f(r)² = (1+r²)²`. At radius `r`:
* `g       = diag(1, h(r))`, `ginv = diag(1, 1/h(r))`;
* `∂_r g   = diag(0, h'(r))`, `∂_θ g = 0`, with `h'(r) = 4 r (1+r²)`;
* `∂_r∂_r g = diag(0, h''(r))`, other 2-jets `0`, with `h''(r) = 4 + 12 r²`.

Gauss curvature `K = −f''/f`, scalar `R = 2K = −2 f''/f`. With `f = 1+r²`, `f'' = 2`, so
`R = −4/(1+r²)`.
-/

open QIQTH.CoordinateCurvature
open scoped BigOperators

namespace QIQTH.RevolutionSurface

/-! ## 1. Metric-derivative verification (the honesty core)

The single nontrivial metric component `h(r) = (1+r²)²` has genuine first derivative
`h'(r) = 4 r (1+r²)` and second derivative `h''(r) = 4 + 12 r²`, certified against Mathlib's
`HasDerivAt`. These verify that the 1- and 2-jets fed to the curvature calculator ARE the actual
derivatives of the metric field `h = f²`, not merely asserted. -/

/-- The metric component `g_{θθ} = h(r) = (1+r²)²` has first derivative `h'(r) = 4 r (1+r²)`. -/
theorem hasDerivAt_revsurf_h (r : ℝ) :
    HasDerivAt (fun r : ℝ => (1 + r ^ 2) ^ 2) (4 * r * (1 + r ^ 2)) r := by
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hbase : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := hsq.const_add (1 : ℝ)
  have h := hbase.pow 2
  convert h using 1
  ring

/-- The first-derivative component `h'(r) = 4 r (1+r²)` has derivative `h''(r) = 4 + 12 r²`; i.e.
the second derivative of `h = (1+r²)²` is `4 + 12 r²`. -/
theorem hasDerivAt_revsurf_dh (r : ℝ) :
    HasDerivAt (fun r : ℝ => 4 * r * (1 + r ^ 2)) (4 + 12 * r ^ 2) r := by
  have hlin : HasDerivAt (fun r : ℝ => 4 * r) (4 : ℝ) r := by
    simpa using (hasDerivAt_id r).const_mul (4 : ℝ)
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hquad : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := hsq.const_add (1 : ℝ)
  have h := hlin.mul hquad
  convert h using 1
  ring

/-! ## 2. The metric 2-jet as functions of the radius `r` -/

/-- Inverse metric `ginv = diag(1, 1/(1+r²)²)`. -/
noncomputable def revGinv (r : ℝ) : Mat (Fin 2) := !![1, 0; 0, 1 / (1 + r ^ 2) ^ 2]

/-- Components of `∂ₐ g_{ij}`: `∂_r g_{θθ} = 4 r (1+r²)` (i.e. `a = 0`, `i = j = 1`), else `0`. -/
noncomputable def revDgc (r : ℝ) (a i j : Fin 2) : ℝ :=
  if a = 0 ∧ i = 1 ∧ j = 1 then 4 * r * (1 + r ^ 2) else 0

/-- Components of `∂ₐ∂ᵦ g_{ij}`: `∂_r∂_r g_{θθ} = 4 + 12 r²` (i.e. `a = b = 0`, `i = j = 1`),
else `0`. -/
noncomputable def revDdgc (r : ℝ) (a b i j : Fin 2) : ℝ :=
  if a = 0 ∧ b = 0 ∧ i = 1 ∧ j = 1 then 4 + 12 * r ^ 2 else 0

/-- First partials of the metric as a matrix field. `revDg r 0 = !![0,0; 0, 4 r (1+r²)]` and
`revDg r 1 = 0`. -/
noncomputable def revDg (r : ℝ) : Fin 2 → Mat (Fin 2) :=
  fun a => Matrix.of fun i j => revDgc r a i j

/-- Second partials of the metric as a matrix field. `revDdg r 0 0 = !![0,0; 0, 4 + 12 r²]`,
else `0`. -/
noncomputable def revDdg (r : ℝ) : Fin 2 → Fin 2 → Mat (Fin 2) :=
  fun a b => Matrix.of fun i j => revDdgc r a b i j

/-! ## 3. Scalar curvature `R(r) = −4/(1+r²)` (NONCONSTANT) -/

/-- ★★★ The surface of revolution `ds² = dr² + (1+r²)² dθ²` has NONCONSTANT scalar curvature
`R(r) = −4/(1+r²)`. -/
theorem revsurf_scalarCurvature (r : ℝ) :
    scalarCurvature (revGinv r) (revDg r) (revDdg r) = -4 / (1 + r ^ 2) := by
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hne : (1 + r ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [scalarCurvature, ricci, riemann, riemannOf, christoffel, dChristoffel,
    dChristoffelOfDInv, dInvMetric, lowerGamma, dLowerGamma, revGinv, revDg, revDdg,
    revDgc, revDdgc, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  field_simp
  ring

/-! ## 4. The curvature is genuinely nonconstant -/

/-- Scalar curvature at the origin `r = 0` is `−4`. -/
theorem revsurf_scalarCurvature_zero :
    scalarCurvature (revGinv 0) (revDg 0) (revDdg 0) = -4 := by
  rw [revsurf_scalarCurvature 0]; norm_num

/-- Scalar curvature at `r = 1` is `−2`. -/
theorem revsurf_scalarCurvature_one :
    scalarCurvature (revGinv 1) (revDg 1) (revDdg 1) = -2 := by
  rw [revsurf_scalarCurvature 1]; norm_num

/-- The scalar curvature is NONCONSTANT: it takes the value `−4` at `r = 0` and `−2` at `r = 1`,
so this is a genuinely inhomogeneous curved surface (unlike the sphere / `H²`). -/
theorem revsurf_curvature_nonconstant :
    scalarCurvature (revGinv 0) (revDg 0) (revDdg 0) ≠
      scalarCurvature (revGinv 1) (revDg 1) (revDdg 1) := by
  rw [revsurf_scalarCurvature_zero, revsurf_scalarCurvature_one]; norm_num

/-- The scalar curvature is NEGATIVE everywhere. -/
theorem revsurf_curvature_negative (r : ℝ) :
    scalarCurvature (revGinv r) (revDg r) (revDdg r) < 0 := by
  rw [revsurf_scalarCurvature r]
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  apply div_neg_of_neg_of_pos <;> [norm_num; exact hpos]

end QIQTH.RevolutionSurface
