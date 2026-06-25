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

end QIQTH.Spectral.Multiplication
