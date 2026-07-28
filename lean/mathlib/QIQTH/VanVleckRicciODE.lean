/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# EXP-JET3-3c — the van-Vleck radial ODE in Ricci-carrying form

This brick assembles the **corrected** van-Vleck radial ODE
```
  radialDeriv(log det g̃) = 2·(θ_B − n) + radialDeriv(log det(g∘exp)),
```
where `θ_B := tr(B'(1)·B(1)⁻¹)` is the Raychaudhuri expansion of the **clean matrix Jacobi
field** `B` (columns = Jacobi fields along the geodesic, `B(0) = 0`, `B'(0) = I`, `B'' = −R̃ B`).

## Why this is the corrected form

The two ingredients are:

  * **K2** (`QIQTH.JacobianRadial.radialDeriv_log_det_split`): the additive radial-log split
    `radialDeriv(log det g̃) = 2·radialDeriv(log J) + radialDeriv(log det(g∘exp))`, from the
    algebraic factorization `det g̃ = J²·det(g∘exp)`.

  * **EXP-JET3-3b** (`QIQTH.ExpMap.expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n`): the
    Ricci-carrying identification `radialDeriv(log J) = θ_B − n`, with `θ_B` the expansion of the
    clean matrix Jacobi field `B`.

Because `B` satisfies the matrix Jacobi ODE `B'' = −R̃ B`, its expansion genuinely obeys the
geodesic Raychaudhuri equation `θ_B' = −Ric(v,v) − tr(Θ²)` (via `geodesic_raychaudhuri` /
`raychaudhuri_logdet`).  So substituting `radialDeriv(log J) = θ_B − n` into the K2 split yields the
van-Vleck radial ODE that genuinely **carries `−Ric`** — the corrected replacement for the earlier
`vanVleck_radialDeriv_via_raychaudhuri`, which gave only the tautological identification
`θ = radialDeriv(log J)` (the expansion of `J` itself, no independent dynamical content).

## The carried geometric input `hresc`

This theorem is **CONDITIONAL** on `hresc` (an EXP-JET3-3b hypothesis): the standard
Jacobi-field ↔ exp-differential rescaling `det B(s) = sⁿ · expJacobianDet(s • v)`, carried as a
labeled geometric input.  Its proof is EXP-JET3-3a's checkpointed Φ-smooth-dependence deep target.

## Honest scope

This is a DIRECT two-rewrite assembly of the two lemmas above.  It is NOT unconditional (it carries
`hresc`, plus K2's genuine positivity/regularity inputs).  It is NOT the M5 continuum `O(1/t)`
cancellation, and it is NOT the heat-kernel coefficient `a₁ = R/6` (M6).

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.ExpJacobianRicci
import QIQTH.JacobianRadial
import QIQTH.JacobianDet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.JacobianDet QIQTH.JacobianRadial
open QIQTH.PullbackMetric Matrix
open scoped Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **EXP-JET3-3c — the van-Vleck radial ODE in Ricci-carrying form.**

Assembling K2 (the additive radial-log split) with EXP-JET3-3b (the Ricci-carrying
`radialDeriv(log J) = θ_B − n`) gives
```
  radialDeriv(log det g̃) = 2·(θ_B − n) + radialDeriv(log det(g∘exp)),
```
with `θ_B = tr(B'(1)·B(1)⁻¹)` the Raychaudhuri expansion of the clean matrix Jacobi field `B`.
Since `θ_B' = −Ric − tr(Θ²)` (via `B'' = −R̃ B`, `raychaudhuri_logdet` / `geodesic_raychaudhuri`),
this is the van-Vleck radial ODE that genuinely carries `−Ric`.

CONDITIONAL on `hresc` (the rescaling `det B = sⁿ·expJacobianDet`, EXP-JET3-3b's labeled input) and
on K2's positivity/regularity hypotheses.  NOT the M5 `O(1/t)` cancellation, NOT `a₁ = R/6`. -/
theorem vanVleck_radialDeriv_ricci_form
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (B B' : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hB : HasDerivAt B (B' 1) 1) (hu : IsUnit (B 1))
    (hJdiff : DifferentiableAt ℝ
      (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v)
    (hresc : (fun s => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v)))
             =ᶠ[nhds (1:ℝ)] (fun s => Real.log ((B s).det) - (n : ℝ) * Real.log s))
    (hJ : ∀ᶠ x in 𝓝 v, 0 < expJacobianDet g gi hC p x)
    (hD : ∀ᶠ x in 𝓝 v, 0 < Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))
    (hJp : ∀ i, PdiffAt (expJacobianDet g gi hC p) i v)
    (hDp : ∀ i, PdiffAt (fun x => Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b)) i v) :
    radialDeriv (fun x => Real.log (Matrix.det (Matrix.of fun i j =>
        expPullbackMetric g gi hC p x i j))) v
      = 2 * ((B' 1 * (B 1)⁻¹).trace - (n : ℝ))
        + radialDeriv (fun x => Real.log (Matrix.det (Matrix.of fun a b =>
            g (expMap g gi hC p x) a b))) v := by
  rw [QIQTH.JacobianRadial.radialDeriv_log_det_split g gi hC p v hJ hD hJp hDp,
    QIQTH.ExpMap.expJacobianDet_radialDeriv_eq_raychaudhuri_sub_n g gi hC p v B B' hB hu hJdiff hresc]

end QIQTH.ExpMap
