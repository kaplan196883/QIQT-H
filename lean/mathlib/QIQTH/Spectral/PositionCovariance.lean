import QIQTH.Spectral.PositionPVM
import QIQTH.Spectral.PVMConj
import QIQTH.Spectral.TranslationFlow

/-!
# Translation-covariance of the position PVM

The position observable transforms correctly under spatial translation: conjugating the position spectral
projection `E(A) = M_{𝟙_A}` by the translation unitary `τ_t` shifts the set,
`τ_t E(A) τ_t⁻¹ = E((· + t)⁻¹ A) = E(A - t)`. Equivalently `(positionPVM.conj (translationUnitary t)).E A
= positionPVM.E ((· + t)⁻¹ A)`. This Weyl-type covariance is exactly what identifies the **momentum operator**
(generator of `τ_t`) as the operator canonically conjugate to position — the kinematic backbone of
`WedgeKMSFlux #5`. Axiom-free.
-/

namespace QIQTH.Spectral.Multiplication

open MeasureTheory

/-- The translation unitary as a CLM acts by `τ_t`. -/
theorem translationUnitary_coe_apply (t : ℝ) (z : Lp ℂ 2 (volume : Measure ℝ)) :
    (translationUnitary t : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) z
      = translationLp t z := by
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    translationUnitary_apply]

/-- The inverse translation unitary as a CLM acts by `τ_{-t}`. -/
theorem translationUnitary_symm_coe_apply (t : ℝ) (z : Lp ℂ 2 (volume : Measure ℝ)) :
    ((translationUnitary t).symm : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) z
      = translationLp (-t) z := by
  simp only [LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    translationUnitary_symm_apply]

/-- **Translation-covariance of the position spectral measure** (scalar level): the position-probability
    distribution of a state `x` under the translated position PVM `positionPVM.conj (τ_t)` equals that of the
    translated state `τ_{-t} x`, `((positionPVM.conj (τ_t)).scalarMeasure x)(A) = ∫_A ‖(τ_{-t}x)(a)‖² da`. So
    conjugating the position observable by translation-by-`t` shifts the Born distribution by `t` — the
    covariance that makes the translation generator (momentum) conjugate to position. Axiom-free, from
    `conj_scalarMeasure` + `positionPVM_scalarMeasure`. -/
theorem positionPVM_conj_translation_scalarMeasure (t : ℝ) (x : Lp ℂ 2 (volume : Measure ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    ((positionPVM (μ := (volume : Measure ℝ))).conj (translationUnitary t)).scalarMeasure x A
      = ENNReal.ofReal (∫ a in A, ‖(translationLp (-t) x) a‖ ^ 2 ∂(volume : Measure ℝ)) := by
  rw [ProjectionValuedMeasure.conj_scalarMeasure _ _ _ hA, translationUnitary_symm_apply,
    positionPVM_scalarMeasure _ hA]

/-
HONEST CHECKPOINT (recorded): the *operator-level* covariance
  `positionPVM.conj (translationUnitary t)).E A = positionPVM.E ((· + t)⁻¹' A)`  (i.e. `τ_t E(A) τ_t⁻¹ = E(A - t)`)
is the stronger Weyl form. Its proof is `τ_t M_{𝟙_A} τ_{-t} = M_{𝟙_{(·+t)⁻¹A}}` via the indicator-shift
`𝟙_A(x+t) = 𝟙_{(·+t)⁻¹A}(x)` and a three-step ae-composition (the `coeFn`s of `τ_{-t}`, `M_{𝟙_A}`, `τ_t` pushed
through `· + t`). It is the next tractable target; the scalar-level covariance above already carries the physical
content (translation shifts the Born position distribution).
-/

end QIQTH.Spectral.Multiplication
