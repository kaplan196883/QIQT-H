/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Matrix Jacobi field: the regularized-invertibility payoff (phase M2)

A matrix curve `Y : ℝ → Matrix (Fin n) (Fin n) ℝ` that **vanishes at the centre** (`Y 0 = 0`) and has an
**invertible derivative at the centre** (`det (Y' 0) ≠ 0`) factors, by the phase-M1 Hadamard primitive
(`QIQTH.HadamardFactor.hadamardFactor_smul`), as
```
  Y τ = τ • W τ,      W τ = hadamardFactor Y' τ = ∫₀¹ Y'(t·τ) dt,
```
with `W` continuous and `W 0 = Y' 0`.  Since `det` is continuous and `det (W 0) = det (Y' 0) ≠ 0`, the
determinant of `W` stays nonzero on a neighbourhood of the centre, so **`W` is invertible near `τ = 0`**.
This is the payoff of the campaign at the abstract level: the polar inverse `Y⁻¹` is singular at the
centre (because `Y 0 = 0`), but the regularized factor `W⁻¹` is *regular* exactly there.

## Honest scope

This file provides **only** the abstract regularized structure `Y = τ • W` with `W` invertible near `0`.
It does **not**:
* identify `Y` with the geodesic exp-Jacobian `D exp_p` or prove the Jacobi equation `Y'' = −R(τ) Y`
  (the geometric M2b);
* build the van-Vleck / Raychaudhuri radial ODE (M4);
* establish the heat-kernel coefficient `a₁ = R/6` (M6).

The genuine Jacobi initial condition is `Y'(0) = I` (invertible); here it is carried abstractly as the
weaker `det (Y' 0) ≠ 0`, which is all the invertibility payoff needs.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.HadamardFactor

namespace QIQTH.MatrixJacobi

open QIQTH.HadamardFactor

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- **The Hadamard factor's determinant is nonzero near the centre.**
If `Y'` is continuous and `det (Y' 0) ≠ 0`, then `det (hadamardFactor Y' τ) ≠ 0` for all `τ` in a
neighbourhood of `0`.  Proof: `τ ↦ det (hadamardFactor Y' τ)` is continuous (`hadamardFactor_continuous`
composed with `Matrix.det` continuity), and at `τ = 0` it equals `det (Y' 0) ≠ 0` (by
`hadamardFactor_zero`); a continuous real function nonzero at a point is eventually nonzero. -/
theorem hadamardFactor_det_ne_zero_eventually
    (Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) (hY'c : Continuous Y') (h0 : (Y' 0).det ≠ 0) :
    ∀ᶠ τ in nhds (0 : ℝ), (hadamardFactor Y' τ).det ≠ 0 := by
  have hcont : Continuous (fun τ => (hadamardFactor Y' τ).det) :=
    (Continuous.matrix_det continuous_id).comp (hadamardFactor_continuous hY'c)
  have hne : (fun τ => (hadamardFactor Y' τ).det) 0 ≠ 0 := by
    simp only [hadamardFactor_zero]; exact h0
  exact hcont.continuousAt.eventually_ne hne

/-- **The Hadamard factor is a unit near the centre.**
Over the field `ℝ`, `det (hadamardFactor Y' τ) ≠ 0` gives `IsUnit (hadamardFactor Y' τ)` via
`Matrix.isUnit_iff_isUnit_det` and `isUnit_iff_ne_zero`.  Hence `W = hadamardFactor Y'` is invertible on
a neighbourhood of the centre. -/
theorem hadamardFactor_isUnit_eventually
    (Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) (hY'c : Continuous Y') (h0 : (Y' 0).det ≠ 0) :
    ∀ᶠ τ in nhds (0 : ℝ), IsUnit (hadamardFactor Y' τ) := by
  refine (hadamardFactor_det_ne_zero_eventually Y' hY'c h0).mono (fun τ hτ => ?_)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hτ)

/-- **Matrix Jacobi field: the regularized structure.**
A matrix curve `Y` with `Y 0 = 0` and `det (Y' 0) ≠ 0` factors as `Y τ = τ • W τ` (phase M1) with the
factor `W = hadamardFactor Y'` invertible on a neighbourhood of the centre.  Thus `W⁻¹` is regular
exactly where the polar `Y⁻¹` is singular (the centre `τ = 0`), removing the `Y⁻¹` singularity. -/
theorem matrixJacobi_regularized
    (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) (hY : ∀ τ, HasDerivAt Y (Y' τ) τ)
    (hY'c : Continuous Y') (hY0 : Y 0 = 0) (h0 : (Y' 0).det ≠ 0) :
    (∀ τ, Y τ = τ • hadamardFactor Y' τ) ∧
      (∀ᶠ τ in nhds (0 : ℝ), IsUnit (hadamardFactor Y' τ)) :=
  ⟨fun τ => hadamardFactor_smul hY hY'c hY0 τ,
    hadamardFactor_isUnit_eventually Y' hY'c h0⟩

end QIQTH.MatrixJacobi
