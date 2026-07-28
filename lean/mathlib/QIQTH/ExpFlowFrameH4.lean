/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The van-Vleck `h4`: `d²(log det Y) t = −Ric − Sh` for the exp-flow frame Jacobi matrix.

This file CHAINS the two landed results

* `QIQTH.ExpMap.expFlow_frame_raychaudhuri` (ExpFlowRaychaudhuri.lean) — the frame `−Ric`
  Raychaudhuri equation for the actual exp geodesic `γ = expTube`, giving
  `HasDerivAt (θ_Y := s ↦ tr(Y'(s) (Y s)⁻¹)) (−Ric − Sh) t` where `Y = of(Yt)`, `Sh = tr(Θ²)`,
  `Θ = Y' Y⁻¹`; and
* `QIQTH.ExpMap.logdet_secondDeriv_eq_trace_deriv` (LogDetSecondDerivTrace.lean) — the calculus
  connector `d²/ds²(log det Y) t = d/ds(tr(Y'(s) (Y s)⁻¹)) t`,

into the van-Vleck `h4`:
```
  d²/ds² (log det Y) t = −Ric(γ',γ') − tr(Θ²).
```

The proof is a three-line chain: `logdet_secondDeriv_eq_trace_deriv` rewrites the second derivative
of the log-determinant potential as the derivative of the Raychaudhuri trace `θ_Y`, and
`expFlow_frame_raychaudhuri`'s `.deriv` evaluates that derivative to `−Ric − Sh`.  The matrix
fields `Y = fun s => of (fun k j => Yt j k s)` and `Y' = fun s => of (fun k j => deriv (Yt j k) s)`
are syntactically identical to those appearing in `expFlow_frame_raychaudhuri`'s conclusion, so the
atoms align.

## Honest scope

This is the `h4` hypothesis of `vanVleck_ray_secondDeriv_ricci_at`.  It is CONDITIONAL on the
carried frame data (the parallel orthonormal frame `e`, the exp-flow Jacobi matrix `Yt`, and all
the regularity / orthonormality / completeness / decomposition hypotheses of
`expFlow_frame_raychaudhuri`), plus the two genuine `∀ᶠ` facts (`hYmat_ev`, `hu_ev`) the log-det
connector needs.  It is NOT the full discharge of that frame data (the M2b-2 wall), NOT the
connection of `θ` to the coordinate van-Vleck determinant `J`, and NOT `a₁ = R/6`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ExpFlowRaychaudhuri
import QIQTH.LogDetSecondDerivTrace

namespace QIQTH.ExpMap

open QIQTH.Curvature Matrix

set_option maxHeartbeats 1200000

variable {n : ℕ}

/-- **The van-Vleck `h4`: `d²(log det Y) t = −Ric − Sh` for the exp-flow frame Jacobi matrix.**

Chains `expFlow_frame_raychaudhuri` (`θ_Y' = −Ric − Sh`, `Y = of(Yt)`, `Θ = Y' Y⁻¹`, `Sh = tr(Θ²)`)
with `logdet_secondDeriv_eq_trace_deriv` (`d²(log det Y) = d(θ_Y)`) to give
```
  d²/ds² (log det Y) t = −Ric(γ',γ') − tr(Θ²).
```

Carries the full frame-data hypothesis list of `expFlow_frame_raychaudhuri` verbatim, plus the two
genuine `∀ᶠ` facts (`hYmat_ev`, `hu_ev`) that the log-det connector needs (matrix differentiability
and invertibility on a neighbourhood of `t`).  This is the `h4` hypothesis of
`vanVleck_ray_secondDeriv_ricci_at`.  CONDITIONAL on the carried frame data (still to be constructed
from the parallel frame + exp-flow Jacobi fields); NOT the full discharge, NOT `a₁ = R/6`. -/
theorem expFlow_frame_h4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (V : Fin n → ℝ → Point n × Point n)
    (hVar : ∀ j, ∀ᶠ τ in nhds t,
      IsGeodesicVariationAt g gi (expTube g gi hC p v) (V j) τ)
    (e : Fin n → ℝ → Point n) (Yt : Fin n → Fin n → ℝ → ℝ)
    (hY : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (Yt j i) (deriv (Yt j i) τ) τ)
    (hY2 : ∀ j i, ∀ᶠ τ in nhds t, HasDerivAt (deriv (Yt j i)) (deriv (deriv (Yt j i)) τ) τ)
    (he : ∀ i a, ∀ᶠ τ in nhds t, HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds t,
      covariantDerivAlong g gi (fun τ => (expTube g gi hC p v τ).1) (e i) τ = 0)
    (hortho : ∀ i k,
      (∑ a, ∑ b, g (expTube g gi hC p v t).1 a b * e i t a * e k t b) = if i = k then (1:ℝ) else 0)
    (hcomplete : ∀ μ b, (∑ i, e i t μ * e i t b) = gi (expTube g gi hC p v t).1 μ b)
    (hinv : ∀ a μ,
      (∑ b, g (expTube g gi hC p v t).1 a b * gi (expTube g gi hC p v t).1 μ b)
        = if a = μ then (1:ℝ) else 0)
    (hexp : ∀ j,
      (fun s => fun a => ∑ i, Yt j i s * e i s a)
        =ᶠ[nhds t] (fun s => (V j s).1))
    (hYmat : HasDerivAt (fun s => (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (Yt j k) t)) t)
    (hY'mat : HasDerivAt
              (fun s => (Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ))
              (Matrix.of (fun k j => deriv (deriv (Yt j k)) t)) t)
    (hu : IsUnit (Matrix.of (fun k j => Yt j k t) : Matrix (Fin n) (Fin n) ℝ))
    (hYmat_ev : ∀ᶠ s in nhds t,
      HasDerivAt (fun u => (Matrix.of (fun k j => Yt j k u) : Matrix (Fin n) (Fin n) ℝ))
        (Matrix.of (fun k j => deriv (Yt j k) s)) s)
    (hu_ev : ∀ᶠ s in nhds t,
      IsUnit (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ)) :
    deriv (deriv (fun s => Real.log
        ((Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ).det))) t
      = -(∑ σ, ∑ ν, ricci g gi σ ν (expTube g gi hC p v t).1
              * (expTube g gi hC p v t).2 σ * (expTube g gi hC p v t).2 ν)
        - (((Matrix.of (fun k j => deriv (Yt j k) t) : Matrix (Fin n) (Fin n) ℝ)
              * (Matrix.of (fun k j => Yt j k t))⁻¹)
            * ((Matrix.of (fun k j => deriv (Yt j k) t))
              * (Matrix.of (fun k j => Yt j k t))⁻¹)).trace := by
  -- The frame `−Ric` Raychaudhuri equation for the exp geodesic: `θ_Y' = −Ric − Sh` at `t`.
  have hRay := expFlow_frame_raychaudhuri g gi hC hgsymm p v hv ht V hVar e Yt hY hY2 he hpar
    hortho hcomplete hinv hexp hYmat hY'mat hu
  -- The log-det connector: `d²(log det Y) t = d(θ_Y) t`.
  have hconn := logdet_secondDeriv_eq_trace_deriv
    (fun s => (Matrix.of (fun k j => Yt j k s) : Matrix (Fin n) (Fin n) ℝ))
    (fun s => (Matrix.of (fun k j => deriv (Yt j k) s) : Matrix (Fin n) (Fin n) ℝ))
    hYmat_ev hu_ev
  -- Chain: rewrite `d²(log det Y)` as `d(θ_Y)`, then evaluate `d(θ_Y) = −Ric − Sh`.
  rw [hconn, hRay.deriv]

end QIQTH.ExpMap
