/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The conditional van-Vleck bridge — `radialDeriv(log J) = θ` (the Raychaudhuri expansion)

This file identifies the van-Vleck radial log-derivative with the geodesic Raychaudhuri expansion
scalar, CONDITIONAL on the single labeled geometric input `Y = D exp_p` (the matrix Jacobi field
along the ray = the exp-Jacobian). Concretely:
```
  radialDeriv (log J) v  = (Y' 1 · (Y 1)⁻¹).trace = θ           (the Raychaudhuri expansion)
  radialDeriv (log det g̃) v = 2 θ + radialDeriv (log det (g∘exp)) v.
```
This is the physics identity `θ = r∂_r log J = congruence expansion`, connecting the geodesic
Raychaudhuri equation (`θ' = −Ric − tr Θ²`, from `raychaudhuri_logdet`) to the van-Vleck determinant
`det g̃` (through the K2 split `radialDeriv_log_det_split`).

## The single geometric input

The bridge is CONDITIONAL on
```
  hYexp : (fun s => Real.log ((Y s).det))
            =ᶠ[𝓝 1] (fun s => Real.log (expJacobianDet g gi hC p (s • v))),
```
i.e. the matrix-Jacobi determinant along the ray `s ↦ s • v` equals the exp-Jacobian `J(s•v)` near
`s = 1`. This is `Y = D exp_p` along the ray — a genuine geometric INPUT, NOT the conclusion.

## Assembly

* `QIQTH.RadialDistance.radialDeriv_eq_ray_deriv` : `radialDeriv f v = deriv (fun s => f (s•v)) 1`.
* `Filter.EventuallyEq.deriv_eq` : rewrites the ray `deriv` across `hYexp`.
* `QIQTH.ExpMap.raychaudhuri_logdet_firstderiv` : `d/ds log det Y = (Y' · Y⁻¹).trace = θ`.
* `QIQTH.JacobianRadial.radialDeriv_log_det_split` (K2) : the additive van-Vleck radial-log split.

## Honest scope

⚠ CONDITIONAL on `hYexp` (`Y = D exp_p`, dischargeable via the repo's EXP-JET3, currently
incomplete). This does NOT discharge `hYexp`, does NOT give the O(1/t) cancellation (M5), and is NOT
the heat-kernel coefficient `a₁ = R/6` (M6). `hYexp` and the regularity hypotheses are ordinary
inputs, not the conclusion.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.RadialRayDeriv
import QIQTH.RaychaudhuriLogDet
import QIQTH.JacobianDet
import QIQTH.JacobianRadial

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.JacobianDet QIQTH.JacobianRadial
  QIQTH.PullbackMetric Matrix

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **The Raychaudhuri expansion = the van-Vleck radial log-derivative (conditional on `Y = D exp`).**

For a matrix Jacobi field `Y` that is invertible and differentiable at `s = 1`, whose determinant
along the ray `s ↦ s • v` agrees (near `s = 1`) with the exp-Jacobian `J(s•v)` — this agreement is
the labeled geometric input `hYexp`, i.e. `Y = D exp_p` — the radial (Euler) log-derivative of the
exp-Jacobian equals the Raychaudhuri expansion scalar `θ := (Y' · Y⁻¹).trace`:
```
  radialDeriv (fun x => log J(x)) v = (Y' 1 · (Y 1)⁻¹).trace = θ.
```

Proof: `radialDeriv_eq_ray_deriv` turns the Euler operator into the ray derivative
`deriv (fun s => log J(s•v)) 1`; `hYexp.deriv_eq` rewrites this to `deriv (fun s => log det Y(s)) 1`;
and `raychaudhuri_logdet_firstderiv` evaluates the latter to `(Y' 1 · (Y 1)⁻¹).trace`.

⚠ CONDITIONAL: `hYexp` (`Y = D exp_p` along the ray) is a genuine geometric INPUT, not a conclusion. -/
theorem raychaudhuri_expansion_eq_radialDeriv_logJ
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hY1 : HasDerivAt Y (Y' 1) 1) (hu1 : IsUnit (Y 1))
    (hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v)
    (hYexp : (fun s => Real.log ((Y s).det))
      =ᶠ[nhds (1 : ℝ)]
      (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))) :
    radialDeriv (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v
      = (Y' 1 * (Y 1)⁻¹).trace := by
  rw [radialDeriv_eq_ray_deriv _ _ hJdiff, ← hYexp.deriv_eq]
  exact (raychaudhuri_logdet_firstderiv Y Y' hY1 hu1).deriv

/-- **The van-Vleck radial-log-det via the Raychaudhuri expansion (conditional on `Y = D exp`).**

Combining the K2 additive split `radialDeriv_log_det_split` with
`raychaudhuri_expansion_eq_radialDeriv_logJ`, the radial (Euler) log-derivative of the van-Vleck
determinant `det g̃` reads
```
  radialDeriv (log det g̃) v = 2 θ + radialDeriv (log det (g∘exp)) v,   θ := (Y' 1 · (Y 1)⁻¹).trace.
```

Proof: rewrite the LHS by the K2 split, then rewrite the `radialDeriv (log J)` summand by
`raychaudhuri_expansion_eq_radialDeriv_logJ`.

⚠ CONDITIONAL on the same geometric input `hYexp` (`Y = D exp_p`); the `hJ hD hJp hDp` are the K2
regularity hypotheses (positivity/coordinate-differentiability), all genuine inputs. -/
theorem vanVleck_radialDeriv_via_raychaudhuri
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hY1 : HasDerivAt Y (Y' 1) 1) (hu1 : IsUnit (Y 1))
    (hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v)
    (hYexp : (fun s => Real.log ((Y s).det))
      =ᶠ[nhds (1 : ℝ)]
      (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v))))
    (hJ : ∀ᶠ x in nhds v, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p x)
    (hD : ∀ᶠ x in nhds v,
      0 < Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))
    (hJp : ∀ i, PdiffAt (QIQTH.JacobianDet.expJacobianDet g gi hC p) i v)
    (hDp : ∀ i, PdiffAt
      (fun x => Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b)) i v) :
    radialDeriv
        (fun x => Real.log (Matrix.det
          (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))) v
      = 2 * (Y' 1 * (Y 1)⁻¹).trace
        + radialDeriv
            (fun x => Real.log (Matrix.det
              (Matrix.of fun a b => g (expMap g gi hC p x) a b))) v := by
  rw [QIQTH.JacobianRadial.radialDeriv_log_det_split g gi hC p v hJ hD hJp hDp,
    raychaudhuri_expansion_eq_radialDeriv_logJ g gi hC p v Y Y' hY1 hu1 hJdiff hYexp]

end QIQTH.ExpMap
