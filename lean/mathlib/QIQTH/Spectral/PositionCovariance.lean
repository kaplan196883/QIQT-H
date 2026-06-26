import QIQTH.Spectral.PositionPVM
import QIQTH.Spectral.PVMConj
import QIQTH.Spectral.TranslationFlow
import QIQTH.Spectral.ModulationFlow

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

/-- **Translation-covariance of the position PVM (operator form):** `τ_t E(A) τ_t⁻¹ = E((· + t)⁻¹ A)`
    (`= E(A - t)`). The position spectral projection on `A`, conjugated by translation-by-`t`, is the projection
    on the shifted set — the Weyl covariance that makes the translation generator (momentum) conjugate to
    position. Proof: `τ_t M_{𝟙_A} τ_{-t} = M_{𝟙_{(·+t)⁻¹A}}` via the indicator-shift `𝟙_A(x+t)=𝟙_{(·+t)⁻¹A}(x)`
    and the three `coeFn`s of `τ_{-t}, M_{𝟙_A}, τ_t` composed through the measure-preserving shift `· + t`. -/
theorem positionPVM_conj_translationUnitary (t : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ((positionPVM (μ := (volume : Measure ℝ))).conj (translationUnitary t)).E A
      = (positionPVM (μ := (volume : Measure ℝ))).E ((fun x => x + t) ⁻¹' A) := by
  have hpre : MeasurableSet ((fun x => x + t) ⁻¹' A) := hA.preimage (measurable_add_const t)
  rw [ProjectionValuedMeasure.conj_E,
    show (positionPVM (μ := (volume : Measure ℝ))).E A = indMul hA from posPVM_E_eq hA,
    show (positionPVM (μ := (volume : Measure ℝ))).E ((fun x => x + t) ⁻¹' A) = indMul hpre
      from posPVM_E_eq hpre]
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    translationUnitary_symm_coe_apply, translationUnitary_coe_apply]
  show translationLp t (indMul hA (translationLp (-t) f))
      = mulOp (indSymbol_measurable hpre) zero_le_one (indSymbol_norm_le ((fun x => x + t) ⁻¹' A)) f
  refine Lp.ext ?_
  have hqm := (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving
  have e_mul_s : (fun x => (indMul hA (translationLp (-t) f) : ℝ → ℂ) (x + t))
      =ᵐ[volume] fun x => indSymbol A (x + t) * (translationLp (-t) f : ℝ → ℂ) (x + t) :=
    hqm.tendsto_ae.eventually
      (mulOp_coeFn (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A) (translationLp (-t) f))
  have e_in_s : (fun x => (translationLp (-t) f : ℝ → ℂ) (x + t))
      =ᵐ[volume] fun x => (f : ℝ → ℂ) (x + t + -t) :=
    hqm.tendsto_ae.eventually (coeFn_translationLp (-t) f)
  filter_upwards [coeFn_translationLp t (indMul hA (translationLp (-t) f)), e_mul_s, e_in_s,
    mulOp_coeFn (indSymbol_measurable hpre) zero_le_one (indSymbol_norm_le _) f]
    with x h_out h_mul h_in h_rhs
  rw [h_out, h_mul, h_in, h_rhs, add_neg_cancel_right]
  congr 1

/-- The modulation unitary as a CLM acts by `e^{isX}`. -/
theorem modulationUnitary_coe (s : ℝ) :
    (modulationUnitary s : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      = modulationLp s := by
  ext f; rfl

/-- The inverse modulation unitary as a CLM acts by `e^{-isX}`. -/
theorem modulationUnitary_symm_coe (s : ℝ) :
    ((modulationUnitary s).symm : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      = modulationLp (-s) := by
  ext f; rfl

/-- **Invariance of the position observable under modulation (the trivial leg of Weyl covariance):**
    `e^{isX} E(A) e^{-isX} = E(A)`. Modulation by `e^{isx}` commutes with the position spectral projection
    `E(A) = M_{𝟙_A}` (both are multiplication operators), so it leaves the position observable invariant —
    `[e^{isX}, E(A)] = 0`, i.e. `e^{isX}` is a function of `X` and commutes with all functions of `X`. (Contrast
    the translation covariance, where `τ_t` genuinely *moves* `E(A)`.) Proof: `M_{e^{isx}} M_{𝟙_A} M_{e^{-isx}}
    = M_{e^{isx} 𝟙_A e^{-isx}} = M_{𝟙_A}` since `e^{isx} e^{-isx} = 1`. -/
theorem positionPVM_conj_modulationUnitary (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ((positionPVM (μ := (volume : Measure ℝ))).conj (modulationUnitary s)).E A
      = (positionPVM (μ := (volume : Measure ℝ))).E A := by
  rw [ProjectionValuedMeasure.conj_E,
    show (positionPVM (μ := (volume : Measure ℝ))).E A = indMul hA from posPVM_E_eq hA,
    modulationUnitary_coe, modulationUnitary_symm_coe]
  simp only [modulationLp, indMul]
  rw [mulOp_mul (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
      (modSymbol_measurable (-s)) zero_le_one (modSymbol_le_one (-s)),
    mulOp_mul (modSymbol_measurable s) zero_le_one (modSymbol_le_one s) _ _ _]
  exact mulOp_congr _ _ _ (indSymbol_measurable hA) zero_le_one (indSymbol_norm_le A)
    (funext fun x => by
      show modSymbol s x * (indSymbol A x * modSymbol (-s) x) = indSymbol A x
      have h1 : modSymbol s x * modSymbol (-s) x = 1 := by
        simp only [modSymbol]; rw [← Complex.exp_add]
        rw [show (↑(s * x) * Complex.I + ↑(-s * x) * Complex.I) = 0 by push_cast; ring,
          Complex.exp_zero]
      calc modSymbol s x * (indSymbol A x * modSymbol (-s) x)
          = indSymbol A x * (modSymbol s x * modSymbol (-s) x) := by ring
        _ = indSymbol A x := by rw [h1, mul_one])

end QIQTH.Spectral.Multiplication
