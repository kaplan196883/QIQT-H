/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Hadamard smooth-factorization primitive

A `C¹` function `f : ℝ → F` (`F` a real Banach space) with `f 0 = 0` factors **smoothly** through its
argument:
```
  f τ = τ • g τ,   where   g τ = ∫ t in 0..1, f' (t • τ),
```
with `g` continuous and `g 0 = f' 0`.  Concretely, the singular quotient `f τ / τ` (which is only
formally defined at `τ = 0`) is realized as the *genuinely continuous* function `g`.  The factorization
is exact for **all** `τ`, including `τ = 0` (both sides are `0`).

Derivation: for fixed `τ`, `d/dt f(t·τ) = τ • f'(t·τ)` (chain rule), so by the fundamental theorem of
calculus `∫₀¹ τ • f'(t·τ) dt = f(τ) − f(0) = f(τ)`; pulling the scalar out, `τ • ∫₀¹ f'(t·τ) dt = f τ`.

## Role in the QIQT→GR programme

This is **phase M1** of the off-radial matrix-Jacobi campaign
(`docs/qg_roadmap/MATRIX_JACOBI_PLAN.md`): the regularization key that removes the `Y(τ)/τ` singularity
at the geodesic centre so that the inverse Jacobi/van-Vleck matrix `W⁻¹` stays regular near `τ = 0`.
Mathlib does not supply this primitive — its `Analysis/Complex/Hadamard.lean` is the unrelated
Hadamard three-lines theorem.

## Honest scope

This file provides **only** the scalar smooth-factorization lemma.  It does **not** build the matrix
Jacobi field (phase M2), the van-Vleck radial ODE, or the heat-kernel coefficient `a₁ = R/6` — those are
later phases of the campaign and are not touched here.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib

namespace QIQTH.HadamardFactor

open intervalIntegral MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Hadamard factor** of a `C¹` function with derivative `f'`:
`hadamardFactor f' τ = ∫₀¹ f'(t·τ) dt`.  When `f 0 = 0` this is the continuous realization of the
formal quotient `f τ / τ` (see `hadamardFactor_smul`). -/
noncomputable def hadamardFactor (f' : ℝ → F) (τ : ℝ) : F := ∫ t in (0:ℝ)..1, f' (t * τ)

omit [CompleteSpace F] in
/-- **Chain rule for `t ↦ f(t·τ)`.**  Its derivative at `t` is `τ • f'(t·τ)`. -/
theorem hasDerivAt_comp_mul {f f' : ℝ → F} (hf : ∀ τ, HasDerivAt f (f' τ) τ) (τ t : ℝ) :
    HasDerivAt (fun t => f (t * τ)) (τ • f' (t * τ)) t := by
  have hinner : HasDerivAt (fun t : ℝ => t * τ) τ t := by
    simpa using (hasDerivAt_id t).mul_const τ
  exact (hf (t * τ)).scomp t hinner

omit [CompleteSpace F] in
/-- **Continuity of the composed derivative** `t ↦ τ • f'(t·τ)` (for the interval-integrability step). -/
theorem continuous_comp_deriv {f' : ℝ → F} (hf'c : Continuous f') (τ : ℝ) :
    Continuous (fun t => τ • f' (t * τ)) :=
  continuous_const.smul (hf'c.comp (continuous_id.mul continuous_const))

/-- **Hadamard smooth factorization.**  If `f` is `C¹` with `f 0 = 0`, then `f τ = τ • hadamardFactor f' τ`
for every `τ` (including `τ = 0`, where both sides vanish). -/
theorem hadamardFactor_smul {f f' : ℝ → F} (hf : ∀ τ, HasDerivAt f (f' τ) τ)
    (hf'c : Continuous f') (hf0 : f 0 = 0) (τ : ℝ) :
    f τ = τ • hadamardFactor f' τ := by
  -- FTC applied to `t ↦ f (t·τ)` on `[0,1]`, with derivative `t ↦ τ • f'(t·τ)`.
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t => f (t * τ)) (τ • f' (t * τ)) t :=
    fun t _ => hasDerivAt_comp_mul hf τ t
  have hint : IntervalIntegrable (fun t => τ • f' (t * τ)) MeasureTheory.volume 0 1 :=
    (continuous_comp_deriv hf'c τ).intervalIntegrable 0 1
  have hFTC : (∫ t in (0:ℝ)..1, τ • f' (t * τ)) = f (1 * τ) - f (0 * τ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [one_mul, zero_mul, hf0, sub_zero] at hFTC
  -- Pull the scalar `τ` out of the integral.
  rw [intervalIntegral.integral_smul] at hFTC
  rw [hadamardFactor, hFTC]

/-- **Value at the centre.**  `hadamardFactor f' 0 = f' 0`. -/
theorem hadamardFactor_zero {f' : ℝ → F} : hadamardFactor f' 0 = f' 0 := by
  unfold hadamardFactor
  simp

omit [CompleteSpace F] in
/-- **Continuity of the Hadamard factor.**  If `f'` is continuous, so is `τ ↦ hadamardFactor f' τ`. -/
theorem hadamardFactor_continuous {f' : ℝ → F} (hf'c : Continuous f') :
    Continuous (hadamardFactor f') := by
  have hcont : Continuous (Function.uncurry (fun τ t : ℝ => f' (t * τ))) :=
    hf'c.comp (continuous_snd.mul continuous_fst)
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun τ t : ℝ => f' (t * τ)) hcont 0 1
  simpa [hadamardFactor] using this

end QIQTH.HadamardFactor
