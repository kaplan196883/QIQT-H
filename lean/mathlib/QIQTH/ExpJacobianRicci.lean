/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# EXP-JET3-3b — the Ricci-carrying connection `radialDeriv(log J) = θ_B − n`

This is the step that puts the **Ricci content** into the van-Vleck radial ODE.  Writing
`J = expJacobianDet` for the exp-map Jacobian determinant and `B` for the *clean* matrix Jacobi
field (columns = Jacobi fields along the geodesic, `B(0) = 0`, `B'(0) = I`, `B'' = −R̃ B`), the
Raychaudhuri expansion of `B` is
```
  θ_B := tr(B'(1) · B(1)⁻¹).
```
We prove
```
  radialDeriv (fun x => log J(x)) v = θ_B − n.
```

## Why this is the Ricci-carrying step

The earlier `vanVleck_radialDeriv_via_raychaudhuri` gave only the *tautological* identification
`θ = radialDeriv(log J)` — the expansion of `J` itself, which by construction has no independent
dynamical content.  Here `θ_B` is the expansion of the **clean matrix Jacobi field `B`**, and `B`
satisfies the matrix Jacobi ODE `B'' = −R̃ B`.  Consequently `θ_B` genuinely obeys the geodesic
Raychaudhuri equation `θ_B' = −Ric(v,v) − tr(Θ²)` (see `geodesic_raychaudhuri` /
`raychaudhuri_logdet`).  So identifying `radialDeriv(log J)` with `θ_B − n` is exactly what wires
the `−Ric` source term into the van-Vleck radial ODE.

## The carried geometric input `hresc`

The bridge between `J` and `B` is the **standard Jacobi-field ↔ exp-differential rescaling**
```
  det B(s) = sⁿ · expJacobianDet(s • v),
```
equivalently (taking logs near `s = 1`, where `s > 0`, `det B(s) > 0`)
```
  log expJacobianDet(s • v) = log det B(s) − n · log s.
```
This is `hresc`.  It is **CARRIED here as a labeled geometric hypothesis**, NOT proved and NOT the
conclusion.  Its full proof (the Φ-rescaling / smooth-dependence-on-initial-conditions argument
identifying the columns of `B` with `s`-scaled exp differentials) is EXP-JET3-3a's checkpointed
deep target.  It is emphatically **not** the heat-kernel coefficient `a₁ = R/6` (M6), and it is not
the M5 continuum step.

## Proof

`radialDeriv_eq_ray_deriv` turns the Euler operator into the ray derivative
`deriv (fun s => log J(s • v)) 1`; `hresc.deriv_eq` rewrites this to
`deriv (fun s => log det B(s) − n·log s) 1`; the sub-derivative splits as
`(raychaudhuri_logdet_firstderiv …).deriv = θ_B` minus `deriv (fun s => n·log s) 1 = n·(1⁻¹) = n`.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.RadialRayDeriv
import QIQTH.RaychaudhuriLogDet
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.RadialDistance Matrix

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **EXP-JET3-3b — the Ricci-carrying radial-derivative identity.**

For the exp-map Jacobian determinant `J = expJacobianDet` and the clean matrix Jacobi field `B`
(with Raychaudhuri expansion `θ_B := tr(B'(1)·B(1)⁻¹)`), the radial (Euler) derivative of `log J`
at `v` is
```
  radialDeriv (fun x => log J(x)) v = θ_B − n.
```

The hypothesis `hresc` is the CARRIED geometric input — the standard Jacobi-field ↔ exp-differential
**rescaling** `det B(s) = sⁿ · J(s • v)` (in its log form near `s = 1`).  It is an assumed
input, not the conclusion; its proof is EXP-JET3-3a's deep target and is unrelated to `a₁ = R/6`.

Combined with `raychaudhuri_logdet` (`θ_B' = −Ric − tr(Θ²)`, from `B'' = −R̃ B`), this puts the
Ricci source term into the van-Vleck radial ODE. -/
theorem expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (B B' : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hB : HasDerivAt B (B' 1) 1) (hu : IsUnit (B 1))
    (hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v)
    (hresc : (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))
             =ᶠ[nhds (1:ℝ)] (fun s => Real.log ((B s).det) - (n : ℝ) * Real.log s)) :
    radialDeriv (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v
      = (B' 1 * (B 1)⁻¹).trace - (n : ℝ) := by
  -- `θ_B` is the derivative of `log det B` at `1` (Raychaudhuri log-det bridge).
  have hlog : HasDerivAt (fun s => Real.log ((B s).det)) ((B' 1 * (B 1)⁻¹).trace) 1 :=
    raychaudhuri_logdet_firstderiv B B' hB hu
  -- `d/ds (n·log s)` at `1` is `n·(1⁻¹)`.
  have hnlog : HasDerivAt (fun s => (n : ℝ) * Real.log s) ((n : ℝ) * (1 : ℝ)⁻¹) 1 :=
    (Real.hasDerivAt_log (one_ne_zero)).const_mul (n : ℝ)
  -- The difference `log det B − n·log` differentiates termwise (stated in `fun s => f s - g s`
  -- form so its `deriv` matches the goal after `hresc`).
  have hcomb : HasDerivAt (fun s => Real.log ((B s).det) - (n : ℝ) * Real.log s)
      ((B' 1 * (B 1)⁻¹).trace - (n : ℝ) * (1 : ℝ)⁻¹) 1 := hlog.sub hnlog
  -- The ray derivative of `log J(s • v)`, via the carried rescaling `hresc`.
  have key : deriv (fun s : ℝ => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v))) 1
      = (B' 1 * (B 1)⁻¹).trace - (n : ℝ) := by
    rw [hresc.deriv_eq, hcomb.deriv, inv_one, mul_one]
  rw [radialDeriv_eq_ray_deriv _ _ hJdiff]
  exact key

end QIQTH.ExpMap
