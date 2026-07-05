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

/-- **The momentum Born expectation value:** the expectation of any bounded function `f` of the momentum
    observable `P` in the state `x` is the *position* expectation of its inverse Fourier transform,
    `⟪f(P)⟫_x = ∫ f(a)·‖(ℱ⁻¹ x)(a)‖² da` — the Born expectation rule for momentum, the Fourier image of the
    position one. Via the covariance of the diagonal functional under the Fourier conjugation. -/
theorem momentumPVM_diagInt (f : ℝ → ℂ) (x : Lp (α := ℝ) ℂ 2) :
    momentumPVM.diagInt f x
      = ∫ a, f a * (‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm x) a‖ ^ 2 : ℂ)
          ∂(volume : Measure ℝ) := by
  rw [show momentumPVM.diagInt f x
        = ((positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)).diagInt f x from rfl,
    ProjectionValuedMeasure.conj_diagInt, positionPVM_diagInt]

/-- **The momentum scalar spectral measure is the Born `|ℱ⁻¹x|²` density measure:**
    `scalarMeasure x = volume.withDensity (a ↦ ‖(ℱ⁻¹ x)(a)‖²)` — the momentum-probability distribution of `x`
    is the measure with Radon–Nikodym density `|ℱ⁻¹x|²` (the momentum-space `|x̂|²`). The measure-level Born
    rule for momentum, the Fourier image of the position density. -/
theorem momentumPVM_scalarMeasure_eq_withDensity (x : Lp (α := ℝ) ℂ 2) :
    momentumPVM.scalarMeasure x
      = (volume : Measure ℝ).withDensity
          (fun a => ENNReal.ofReal (‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm x) a‖ ^ 2)) := by
  rw [show momentumPVM.scalarMeasure x
        = ((positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)).scalarMeasure x from rfl,
    ProjectionValuedMeasure.conj_scalarMeasure_eq, positionPVM_scalarMeasure_eq_withDensity]

/-- **Plancherel / conservation of total probability:** the total momentum probability equals the total
    position probability, `∫ ‖(ℱ⁻¹ x)(a)‖² da = ‖x‖²`. The Fourier transform is an `L²` isometry, so the
    momentum-space density `|ℱ⁻¹x|²` integrates to the same total mass `‖x‖²` as the position density `|x|²` —
    the Born total-probability is conserved between position and momentum representations. -/
theorem fourier_integral_norm_sq (x : Lp (α := ℝ) ℂ 2) :
    ∫ a, ‖((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm x) a‖ ^ 2 ∂(volume : Measure ℝ) = ‖x‖ ^ 2 := by
  rw [← norm_sq_eq_integral, LinearIsometryEquiv.norm_map]

/-- **The momentum bounded-Borel functional calculus is the Fourier-conjugated multiplication operator:**
    `f(P) = ℱ ∘ M_f ∘ ℱ⁻¹` for every bounded measurable symbol `f : ℝ → ℂ`. Concretely, the abstract Borel
    functional calculus of the momentum observable `P` (built spectrally from the momentum PVM `Ê = ∫ dÊ`) is
    the honest Fourier transform of multiplication by `f` in momentum space. This is the exact algebraic
    combination of the two covariance results: `momentumPVM = positionPVM.conj ℱ`, so
    `Φ_momentum(f) = ℱ ∘ Φ_position(f) ∘ ℱ⁻¹` (`conj_boundedFC`) and `Φ_position(f) = M_f`
    (`boundedFC_positionPVM_eq_mulOp`). It realizes `f(P) = ℱ M_f ℱ⁻¹` at the level of bounded operators on
    `L²(ℝ)`, axiom-free. -/
theorem boundedFC_momentumPVM_eq_fourier_conj_mulOp {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ s, ‖φ s‖ ≤ C) :
    momentumPVM.boundedFC hφ hC0 hC
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2)
        ∘L mulOp hφ hC0 hC
        ∘L ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2) := by
  rw [show momentumPVM = (positionPVM (α := ℝ) (μ := (volume : Measure ℝ))).conj
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) from rfl,
    ProjectionValuedMeasure.conj_boundedFC, boundedFC_positionPVM_eq_mulOp]

/- **CHECKPOINT — the final Weyl-pair capstone `τ_t = e^{itP} = Φ_momentum(fun k => exp (t*k*I))`.**

   By `boundedFC_momentumPVM_eq_fourier_conj_mulOp` (above) the remaining goal
     `momentumPVM.boundedFC (fun k => Complex.exp (t * k * Complex.I)) = translationLp t`
   is EXACTLY the operator identity
     `ℱ ∘ M_{e^{i t k}} ∘ ℱ⁻¹ = τ_t`   (`(τ_t f)(x) = f (x + t)`),
   i.e. "the Fourier transform conjugates modulation by the character `e^{i t k}` into translation by `t`".

   This is a genuine `L²` OPERATOR identity, NOT a Mathlib gap — the function-level content is
   `Fourier.fourierIntegral_comp_add_right` (Fourier turns a right-translation into multiplication by a phase,
   `Mathlib/Analysis/Fourier/FourierTransform.lean`). The residual is pure LABOR (consult-confirmed, no missing
   Mathlib theorem): `MeasureTheory.Lp.fourierTransformₗᵢ` is defined by extension-by-continuity from the
   Schwartz maps (`fourierEquiv … |>.extendOfIsometry`, `LpSpace.lean`), so transferring the pointwise
   modulation↔translation duality to the `L²` isometry needs a density argument:
     (1) prove `ℱ (M_{e^{itk}} f) = τ_t (ℱ f)` on a dense set (`SchwartzMap.toLp`, via
         `SchwartzMap.toLp_fourier_eq` + the pointwise `fourierIntegral_comp_add_right`, matching the exact
         `e^{-2πi x·ξ}` normalization/sign of Mathlib's `fourierIntegral` — the delicate step), then
     (2) extend to all of `L²` by continuity (both sides bounded operators, `DenseRange.induction_on`).
   There is currently NO Mathlib lemma relating `fourierTransformₗᵢ` to translation/modulation, so both
   halves must be built here. Increments 1–2 and the algebraic capstone above are the reusable
   infrastructure this step consumes; landed green and axiom-free. The `τ_t = e^{itP}` identification is the
   carried (labor-only) frontier. NB: this capstone is COSMETIC for the QG program — the GR-chain momentum
   datum is already derived/wired via the self-adjoint `momentumOp` (`MomentumGenerator.lean`); this only
   names the generator spectrally, completing the Weyl pair `X = ∫ x dE`, `P = ∫ k dÊ`. -/

end QIQTH.Spectral.Multiplication
