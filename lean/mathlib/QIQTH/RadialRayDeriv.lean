/-
  RadialRayDeriv — the radial (Euler) operator equals the ray derivative.

  Part of the off-radial matrix-Jacobi campaign (docs/qg_roadmap/MATRIX_JACOBI_PLAN.md): the
  RADIAL ↔ RAY parametrization bridge.  The Euler / radial operator `radialDeriv f v = ∑ i vⁱ ∂ᵢ f`
  (which acts as `r ∂_r` in Riemann-normal-coordinate / tangent space) coincides with the derivative
  of `f` along the ray `s ↦ s • v`:

        radialDeriv f v = deriv (fun s => f (s • v)) 1 = fderiv ℝ f v v.

  This connects K2's van-Vleck `radialDeriv (log J)` (the Euler operator, in tangent / RNC space) to
  the RAY-parametrized geodesic Raychaudhuri expansion `θ = d/ds log det Y` — the parametrization
  prerequisite for the `Y = D exp` / van-Vleck-radial-ODE bridge.

  ⚠ HONEST SCOPE.  This file provides ONLY the parametrization identity (Euler operator = ray
  derivative = `fderiv f v v`).  It does NOT itself perform the `Y = D exp` identification, does NOT
  derive the van-Vleck radial ODE, and is NOT the `a₁ = R/6` heat-kernel coefficient.
-/
import Mathlib
import QIQTH.RadialDistance
import QIQTH.ExpMap

namespace QIQTH.RadialDistance

open QIQTH.Curvature
open QIQTH.ExpMap
open scoped BigOperators

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **Euler operator = directional Fréchet derivative.**  The radial (Euler) operator
    `radialDeriv f v = ∑ i vⁱ ∂ᵢ f` equals the Fréchet derivative of `f` at `v` applied to `v`
    itself, `fderiv ℝ f v v`.  Proof: expand `radialDeriv` and rewrite `fderiv ℝ f v v` in
    coordinate form via `fderiv_apply_eq_sum_pd`, reconciling `vⁱ · ∂ᵢf` with `∂ᵢf · vⁱ`. -/
theorem radialDeriv_eq_fderiv (f : Point n → ℝ) (v : Point n)
    (hf : DifferentiableAt ℝ f v) :
    radialDeriv f v = fderiv ℝ f v v := by
  rw [radialDeriv, fderiv_apply_eq_sum_pd f v v hf]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (v i) (pd f i v))

/-- **Derivative of `f` along a ray.**  For `f` differentiable at `s • v`, the scalar function
    `u ↦ f (u • v)` has derivative `fderiv ℝ f (s • v) v` at `s`.  Proof: the linear map
    `u ↦ u • v` has derivative `v` (`HasDerivAt.smul_const` on `id`), composed with the Fréchet
    derivative of `f` (`HasFDerivAt.comp_hasDerivAt`). -/
theorem hasDerivAt_ray (f : Point n → ℝ) (v : Point n) {s : ℝ}
    (hf : DifferentiableAt ℝ f (s • v)) :
    HasDerivAt (fun u : ℝ => f (u • v)) (fderiv ℝ f (s • v) v) s := by
  have hray : HasDerivAt (fun u : ℝ => u • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  exact hf.hasFDerivAt.comp_hasDerivAt s hray

/-- **The parametrization bridge:** the radial (Euler) operator equals the ray derivative,
    `radialDeriv f v = deriv (fun s => f (s • v)) 1`.  Proof: the ray derivative at `s = 1` is
    `fderiv ℝ f (1 • v) v = fderiv ℝ f v v` (`hasDerivAt_ray` + `one_smul`), and this equals
    `radialDeriv f v` by `radialDeriv_eq_fderiv`.  This is the Euler-operator = ray-derivative
    identity that lets the tangent-space van-Vleck `radialDeriv (log J)` be read as the RAY-parametrized
    Raychaudhuri expansion `θ = d/ds log det Y`. -/
theorem radialDeriv_eq_ray_deriv (f : Point n → ℝ) (v : Point n)
    (hf : DifferentiableAt ℝ f v) :
    radialDeriv f v = deriv (fun s : ℝ => f (s • v)) 1 := by
  have hf1 : DifferentiableAt ℝ f ((1 : ℝ) • v) := by rw [one_smul]; exact hf
  have hd : HasDerivAt (fun u : ℝ => f (u • v)) (fderiv ℝ f ((1 : ℝ) • v) v) 1 :=
    hasDerivAt_ray f v hf1
  rw [hd.deriv, one_smul, radialDeriv_eq_fderiv f v hf]

end QIQTH.RadialDistance
