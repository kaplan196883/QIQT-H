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

/-- The conjugated projection has the same `L²` mass as the original projection applied to `U⁻¹ x`
    (`U` is an isometry): `‖(P.conj U).E A x‖ = ‖P.E A (U⁻¹ x)‖`. -/
theorem norm_conj_E (P : ProjectionValuedMeasure Ω H) (U : H ≃ₗᵢ[ℂ] H) (A : Set Ω) (x : H) :
    ‖(P.conj U).E A x‖ = ‖P.E A (U.symm x)‖ := by
  rw [conj_E]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]

/-- **Spectral measures transform covariantly under unitary conjugation:** the scalar spectral measure of the
    conjugated PVM `P.conj U` at the state `x` equals that of `P` at `U⁻¹ x`,
    `(P.conj U).scalarMeasure x A = P.scalarMeasure (U⁻¹ x) A`. (For the Fourier case: the momentum-space
    probability distribution of `x` is the position distribution of `ℱ⁻¹ x`.) -/
theorem conj_scalarMeasure (P : ProjectionValuedMeasure Ω H) (U : H ≃ₗᵢ[ℂ] H) (x : H)
    {A : Set Ω} (hA : MeasurableSet A) :
    (P.conj U).scalarMeasure x A = P.scalarMeasure (U.symm x) A := by
  rw [(P.conj U).scalarMeasure_apply x hA, P.scalarMeasure_apply (U.symm x) hA, norm_conj_E]

/-- **Matrix elements transform covariantly under unitary conjugation:** the off-diagonal matrix element of the
    conjugated spectral projection equals that of the original projection between `U⁻¹`-rotated states,
    `⟪g, (P.conj U).E A f⟫ = ⟪U⁻¹ g, P.E A (U⁻¹ f)⟫` (`U` is a unitary, so it moves to the other slot as `U⁻¹`).
    The off-diagonal companion of `conj_scalarMeasure`; for the Fourier case it gives the momentum-space
    transition amplitude as the position amplitude of the inverse-transformed states. -/
theorem conj_E_inner (P : ProjectionValuedMeasure Ω H) (U : H ≃ₗᵢ[ℂ] H) (A : Set Ω) (g f : H) :
    inner ℂ g ((P.conj U).E A f) = inner ℂ (U.symm g) (P.E A (U.symm f)) := by
  rw [conj_E]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  rw [← LinearIsometryEquiv.inner_map_map U (U.symm g) (P.E A (U.symm f)),
    LinearIsometryEquiv.apply_symm_apply]

end ProjectionValuedMeasure
end QIQTH.Spectral
