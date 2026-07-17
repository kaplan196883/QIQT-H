/-
  CovariantJacobi — the COVARIANT Jacobi (geodesic-deviation) equation.

  ODE_VARIATIONAL_PLAN.md, Phase L2c.  L2 (`JacobiEquation`) proved the COORDINATE second-order ODE
  `ξ'' = −jacobiOperator` UNCONDITIONALLY, and found that the literal `jacobiOperator = R(ξ,v)v` is
  FALSE in coordinates: the genuine Jacobi equation is `D²ξ/dτ² = −R(ξ,γ')γ'` with the COVARIANT
  second derivative `D²/dτ²`.  This brick builds the along-the-curve covariant derivative and proves
  the covariant Jacobi equation from L2's coordinate ODE plus the covariant correction.

  WHAT LANDS HERE (all axiom-clean, no `sorry`) — the covariant-derivative MACHINERY (L2c #1/#2):

  #1  `covariantDerivAlong` — the covariant derivative of a vector field `ξ(τ)` along a curve `γ(τ)`,
      `(Dξ/dτ)^i = (ξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·ξ^k(τ)`, matching `christoffel`'s index
      convention.

  #2  `covariantSecondDeriv` — `D²ξ/dτ² := covariantDerivAlong g gi γ (covariantDerivAlong g gi γ ξ)`,
      with its definitional expansion `covariantSecondDeriv_apply`; plus `hasDerivAt_comp_curve` (the
      ray chain-rule helper).

  ⚠ NOT YET BUILT HERE (the L2c continuation): `covariant_jacobi_equation` — the deliverable
  `D²ξ/dτ² = −R(ξ,v)v` (`= −riemannGeodesicDeviation`) for a Jacobi field along a geodesic. This is the
  Finset identity matching L2's coordinate `ξ'' = −jacobiOperator` + the covariant correction against the
  antisymmetrized `riemann`; it is the next brick (continuation), NOT proved in this file.

  All regularity/gauge inputs (`hsymm`, `hC`: Γ is `C^∞`; geodesic ODE `hγ`; variational ODE `hVar`)
  are carried as genuine, clearly-labelled hypotheses.  Does NOT build the covariant Jacobi equation,
  Raychaudhuri (L3), or the heat-kernel coefficient `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.Curvature
import QIQTH.JacobiEquation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-! ### #1 — the covariant derivative along a curve -/

/-- **The covariant derivative of a vector field `ξ` along a curve `γ`.**
    `(Dξ/dτ)^i = (ξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·ξ^k(τ)`, with the Christoffel index
    convention `christoffel g gi i j k = Γ^i_{jk}`.  The ordinary coordinate derivative of `ξ^i`
    corrected by the connection term contracting the velocity `γ'` and the field `ξ`. -/
noncomputable def covariantDerivAlong (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) : Point n :=
  fun i => deriv (fun s => ξ s i) τ
    + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ * ξ τ k

/-- Componentwise form of `covariantDerivAlong` (definitional). -/
theorem covariantDerivAlong_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) (i : Fin n) :
    covariantDerivAlong g gi γ ξ τ i
      = deriv (fun s => ξ s i) τ
        + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ * ξ τ k := rfl

/-! ### #2 — the covariant second derivative -/

/-- **The covariant second derivative** `D²ξ/dτ²` — apply `covariantDerivAlong` twice (the inner
    covariant derivative is itself a vector field along `γ`). -/
noncomputable def covariantSecondDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) : Point n :=
  covariantDerivAlong g gi γ (covariantDerivAlong g gi γ ξ) τ

/-- **Expansion of the covariant second derivative** (definitional): the outer covariant derivative of
    the inner covariant-derivative field.  `(D²ξ)^i = (Dξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·(Dξ)^k(τ)`. -/
theorem covariantSecondDeriv_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) (i : Fin n) :
    covariantSecondDeriv g gi γ ξ τ i
      = deriv (fun s => covariantDerivAlong g gi γ ξ s i) τ
        + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ
            * covariantDerivAlong g gi γ ξ τ k := rfl

/-! ### Helpers for #3 (curve chain rule) -/

/-- **Chain rule along a curve** in Christoffel-partial form: for a smooth scalar field `f` and a curve
    `c` with `HasDerivAt c c' τ`, `d/ds f(c s) = ∑ l, ∂_l f(c τ)·c'_l` (via `fderiv_apply_eq_sum_pd`). -/
theorem hasDerivAt_comp_curve (f : Point n → ℝ) (c : ℝ → Point n) (c' : Point n) (τ : ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (hc : HasDerivAt c c' τ) :
    HasDerivAt (fun s => f (c s)) (∑ l, pd f l (c τ) * c' l) τ := by
  have hFD : HasFDerivAt f (fderiv ℝ f (c τ)) (c τ) :=
    (hf.differentiable (by simp) (c τ)).hasFDerivAt
  have h := hFD.comp_hasDerivAt τ hc
  rwa [fderiv_apply_eq_sum_pd f (c τ) c' (hf.differentiable (by simp) (c τ))] at h

end QIQTH.ExpMap
