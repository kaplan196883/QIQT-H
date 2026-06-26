import QIQTH.Spectral.PositionPVM
import QIQTH.Spectral.PVMConj
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The momentum projection-valued measure on `L²(ℝ)`

The **momentum PVM** is the Fourier–Plancherel conjugate of the position PVM: `Ê(A) = ℱ E(A) ℱ⁻¹`, where
`ℱ = MeasureTheory.Lp.fourierTransformₗᵢ` is the (unitary) `L²` Fourier transform and `E` is the position PVM
(`positionPVM`, bricks 1–16). Because conjugation of a `ProjectionValuedMeasure` by a unitary is again a
`ProjectionValuedMeasure` (`ProjectionValuedMeasure.conj`, axiom-free), the momentum PVM is a genuine
projection-valued measure with no further work — it inherits all the structure fields.

This is the spectral measure of the **momentum operator** `P = ℱ X ℱ⁻¹` on `L²(ℝ)`, and the route to the
translation/boost generator (`WedgeKMSFlux #5`): the one-parameter unitary group `e^{itP}` is spatial
translation. Built here for `E = ℝ` (the canonical 1D free-particle case); the construction generalizes
verbatim to any finite-dimensional real inner product space carried by `fourierTransformₗᵢ`.

**Honest scope:** this delivers the momentum PVM as an axiom-free object. Extracting the unbounded generator
`P = ∫ k dÊ(k)` (Stone) and feeding it to `#5` remains the unbounded-FC / Stone frontier; and the GR chain
beyond `#5` stays gated on the physical wedge inputs `#1/#3/#4`.
-/

namespace QIQTH.Spectral.Multiplication

open MeasureTheory

/-- **The momentum projection-valued measure on `L²(ℝ)`**: `Ê(A) = ℱ E(A) ℱ⁻¹`, the Fourier-conjugate of the
    position PVM. A genuine `ProjectionValuedMeasure`, axiom-free, inherited through `conj`. -/
noncomputable def momentumPVM :
    ProjectionValuedMeasure ℝ (Lp (α := ℝ) ℂ 2) :=
  (positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)

/-- The momentum PVM's projection is the Fourier-conjugate of the position projection:
    `Ê(A) = ℱ ∘ E(A) ∘ ℱ⁻¹`. -/
theorem momentumPVM_E (A : Set ℝ) :
    momentumPVM.E A
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2)
        ∘L (positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).E A
        ∘L ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2) :=
  rfl

/-- **The momentum PVM's scalar measure is the Born momentum distribution:** for a state `x`, the
    momentum-space probability mass on `A` equals the *position* mass of its inverse Fourier transform
    `ℱ⁻¹ x`, `(scalarMeasure x)(A) = ENNReal.ofReal (∫_A ‖(ℱ⁻¹ x)(a)‖² da)`. This is the standard fact that
    `|x̂(k)|²` is the momentum-probability density — here read off the Fourier-conjugated PVM via the covariance
    of spectral measures under unitary conjugation (`conj_scalarMeasure`). -/
theorem momentumPVM_scalarMeasure (x : Lp (α := ℝ) ℂ 2) {A : Set ℝ} (hA : MeasurableSet A) :
    momentumPVM.scalarMeasure x A
      = ENNReal.ofReal
          (∫ a in A, ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm x) a‖ ^ 2 ∂(volume : Measure ℝ)) := by
  rw [show momentumPVM.scalarMeasure x A
        = ((positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)).scalarMeasure x A from rfl,
    ProjectionValuedMeasure.conj_scalarMeasure _ _ _ hA, positionPVM_scalarMeasure _ hA]

/-- **The momentum-space transition amplitude:** the off-diagonal matrix element of the momentum spectral
    projection equals the *position* transition amplitude of the inverse-Fourier-transformed states,
    `⟪g, Ê(B) f⟫ = ∫_B conj((ℱ⁻¹ g)(a))·(ℱ⁻¹ f)(a) da`. So the momentum matrix elements `⟪g, Ê(B) f⟫` are the
    position integrals of `ℱ⁻¹ g, ℱ⁻¹ f` over `B` — the momentum-space Born amplitudes. -/
theorem momentumPVM_inner (g f : Lp (α := ℝ) ℂ 2) {B : Set ℝ} (hB : MeasurableSet B) :
    inner ℂ g (momentumPVM.E B f)
      = ∫ a in B, (starRingEnd ℂ) ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm g a)
          * ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm f) a ∂(volume : Measure ℝ) := by
  rw [show momentumPVM.E B = ((positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)).E B from rfl,
    ProjectionValuedMeasure.conj_E_inner,
    show (positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).E B = indMul hB from posPVM_E_eq hB,
    indMul_inner]

end QIQTH.Spectral.Multiplication
