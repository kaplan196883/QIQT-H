import QIQTH.Spectral.PVM

/-!
# Unitary conjugation of a projection-valued measure

If `E` is a `ProjectionValuedMeasure` on a Hilbert space `H` and `U : H ≃ₗᵢ[ℂ] H` is a unitary, then
`A ↦ U ∘ E(A) ∘ U⁻¹` is again a projection-valued measure — the spectral measure of the conjugated operator
`U T U⁻¹`. This is the **general mechanism by which the Fourier–Plancherel transform carries the position PVM
to the momentum PVM** (and, downstream, the boost/translation generator — `WedgeKMSFlux #5`). The construction
is unitary-generic and axiom-free; instantiating `U` with the `L²` Fourier transform is the (Mathlib-Fourier-gated)
next step. All fields transport through conjugation: `U E U⁻¹` is self-adjoint (`U† = U⁻¹`, `E† = E`), idempotent
(`U⁻¹U = 1`), sends `∅↦0`, `univ↦UU⁻¹=1`, multiplicative, and σ-additive (`U` is continuous linear, so `HasSum`
is preserved).
-/

namespace QIQTH.Spectral
namespace ProjectionValuedMeasure

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Unitary conjugation of a PVM**: `(P.conj U).E A = U ∘ P.E A ∘ U⁻¹`. -/
noncomputable def conj (P : ProjectionValuedMeasure Ω H) (U : H ≃ₗᵢ[ℂ] H) :
    ProjectionValuedMeasure Ω H where
  E A := (U : H →L[ℂ] H) ∘L P.E A ∘L (U.symm : H →L[ℂ] H)
  isSA := fun s hs => by
    show star ((U : H →L[ℂ] H) ∘L P.E s ∘L (U.symm : H →L[ℂ] H)) = _
    rw [ContinuousLinearMap.star_eq_adjoint]
    simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
      LinearIsometryEquiv.symm_symm, P.adjoint_eq hs, ContinuousLinearMap.comp_assoc]
  isIdem := fun s hs => by
    show _ * _ = _
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply, P.E_apply_idem hs]
  E_empty := by
    simp only [P.E_empty, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  E_univ := by
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, P.E_univ, ContinuousLinearMap.one_apply,
      LinearIsometryEquiv.apply_symm_apply]
  E_inter := fun s t hs ht => by
    ext x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply, P.E_inter hs ht]
  hasSum_iUnion := fun {A} hAmeas hd x => by
    exact (P.hasSum_iUnion hAmeas hd ((U.symm : H →L[ℂ] H) x)).mapL (U : H →L[ℂ] H)

/-- The conjugated PVM's projection unfolds as `U ∘ P.E A ∘ U⁻¹`. -/
@[simp] theorem conj_E (P : ProjectionValuedMeasure Ω H) (U : H ≃ₗᵢ[ℂ] H) (A : Set Ω) :
    (P.conj U).E A = (U : H →L[ℂ] H) ∘L P.E A ∘L (U.symm : H →L[ℂ] H) := rfl

end ProjectionValuedMeasure
end QIQTH.Spectral
