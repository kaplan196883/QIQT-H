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

/-! ### M3 — determinant / log split

The Hadamard factorization `Y τ = τ • W τ` (with `W = hadamardFactor Y'`) passes to the
**determinant**, giving `det (Y τ) = τ ^ n · det (W τ)`, and — taking logs where everything is
nonzero — to the additive **log split**
`log det (Y τ) = n · log τ + log det (W τ)`.

This isolates the **singular radial term** `n · log τ` (the flat/radial expansion of the full
Jacobian determinant, which diverges as `τ → 0`) from the **finite curvature part** `log det W`
(regular at the centre since `det (W 0) = det (Y' 0)`).  It is exactly the structural separation the
van-Vleck / Raychaudhuri radial ODE (phase M4) needs.

Honest scope: this is the **abstract** det/log split for a curve `Y` with `Y 0 = 0`.  It does **not**
supply the geometric identification `Y = D exp_p` (phase M2b), so it does **not** yet bridge to the
geodesic Jacobian identity `det g̃ = J² · det (g ∘ exp)` (K1/K2); nor does it build the van-Vleck
radial ODE (M4) or the heat-kernel coefficient `a₁ = R/6` (M6). -/

/-- **Determinant of the matrix Jacobi field.**  From the Hadamard factorization `Y τ = τ • W τ`
(`hadamardFactor_smul`) and `det (c • M) = c ^ (card) * det M` (`Matrix.det_smul`, with
`Fintype.card (Fin n) = n`), the determinant factors as
`det (Y τ) = τ ^ n * det (hadamardFactor Y' τ)`. -/
theorem det_matrixJacobi_eq
    (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) (hY : ∀ τ, HasDerivAt Y (Y' τ) τ)
    (hY'c : Continuous Y') (hY0 : Y 0 = 0) (τ : ℝ) :
    (Y τ).det = τ ^ n * (QIQTH.HadamardFactor.hadamardFactor Y' τ).det := by
  rw [hadamardFactor_smul hY hY'c hY0 τ, Matrix.det_smul, Fintype.card_fin]

/-- **Log split of the Jacobi determinant.**  Where `τ ≠ 0` and `det (hadamardFactor Y' τ) ≠ 0`,
taking logs of `det (Y τ) = τ ^ n * det W` (`det_matrixJacobi_eq`) via `Real.log_mul` and
`Real.log_pow` gives the additive split
`log det (Y τ) = n · log τ + log det (hadamardFactor Y' τ)`.
The first summand `n · log τ` is the **singular radial** part; the second is the **finite curvature**
part. -/
theorem log_det_matrixJacobi_split
    (Y Y' : ℝ → Matrix (Fin n) (Fin n) ℝ) (hY : ∀ τ, HasDerivAt Y (Y' τ) τ)
    (hY'c : Continuous Y') (hY0 : Y 0 = 0) {τ : ℝ} (hτ : τ ≠ 0)
    (hW : (QIQTH.HadamardFactor.hadamardFactor Y' τ).det ≠ 0) :
    Real.log ((Y τ).det)
      = (n : ℝ) * Real.log τ + Real.log ((QIQTH.HadamardFactor.hadamardFactor Y' τ).det) := by
  rw [det_matrixJacobi_eq Y Y' hY hY'c hY0 τ, Real.log_mul (pow_ne_zero n hτ) hW, Real.log_pow]

end QIQTH.MatrixJacobi
