import QIQTH.Spectral.PositionPVM
import QIQTH.Spectral.PVMConj
import QIQTH.Spectral.TranslationFlow
import QIQTH.Spectral.ModulationFlow
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

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
open scoped Real FourierTransform

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

/-! ### The Weyl-pair capstone `τ_{-t/2π} = e^{itP} = Φ_momentum(e^{itk})`

The remaining step identifies the momentum bounded functional calculus at the character symbol
`k ↦ e^{itk}` with the **translation group** `τ`. By `boundedFC_momentumPVM_eq_fourier_conj_mulOp` this is
the pure `L²` operator identity `ℱ ∘ M_{e^{itk}} ∘ ℱ⁻¹ = τ_{-t/(2π)}` ("Fourier conjugates modulation by the
character `e^{itk}` into a translation"). The honest constant carries the `2π` normalization of Mathlib's
`fourierIntegral` kernel `e^{-2πi x·ξ}`, so `e^{itP} = τ_{-t/(2π)}`. Built here by a density argument off the
Schwartz maps, since `Lp.fourierTransformₗᵢ` is an extension-by-continuity from `𝓢`. Axiom-free.

NB: this capstone is COSMETIC for the QG program — the GR-chain momentum datum is already derived/wired via the
self-adjoint `momentumOp` (`MomentumGenerator.lean`); this only names the generator spectrally, completing the
canonical Weyl pair `X = ∫ x dE`, `P = ∫ k dÊ`. -/

/-- The derivative of the modulation symbol: `d/dx e^{isx} = (is)·e^{isx}`. -/
theorem modSymbol_hasDerivAt (s x : ℝ) :
    HasDerivAt (modSymbol s) ((↑s * Complex.I) * modSymbol s x) x := by
  have h1 : HasDerivAt (fun y : ℝ => s * y) s x := by simpa using (hasDerivAt_id x).const_mul s
  have h3 : HasDerivAt (fun y : ℝ => (↑(s * y) : ℂ) * Complex.I) ((↑s : ℂ) * Complex.I) x :=
    (h1.ofReal_comp).mul_const Complex.I
  rw [mul_comm]
  exact h3.cexp

/-- The `n`-th derivative of the modulation symbol: `dⁿ/dxⁿ e^{isx} = (is)ⁿ·e^{isx}`. -/
theorem modSymbol_iteratedDeriv (s : ℝ) (n : ℕ) :
    iteratedDeriv n (modSymbol s) = fun x => (↑s * Complex.I) ^ n * modSymbol s x := by
  induction n with
  | zero => ext x; simp
  | succ n IH =>
    rw [iteratedDeriv_succ, IH]
    ext x
    rw [deriv_const_mul _ (modSymbol_hasDerivAt s x).differentiableAt,
      (modSymbol_hasDerivAt s x).deriv]
    ring

/-- **The modulation symbol `e^{isx}` has temperate growth.** Smooth with all iterated derivatives bounded
    (the `n`-th derivative has constant norm `|s|ⁿ`), so it is an admissible Schwartz multiplier — the fact
    that lets us realize `M_{e^{isx}}` on Schwartz functions and transfer the Fourier duality to `L²`. -/
theorem modSymbol_hasTemperateGrowth (s : ℝ) : Function.HasTemperateGrowth (modSymbol s) := by
  refine ⟨?_, fun n => ⟨0, |s| ^ n, fun x => ?_⟩⟩
  · unfold modSymbol
    exact (((Complex.ofRealCLM.contDiff).comp (contDiff_const.mul contDiff_id)).mul
      contDiff_const).cexp
  have hval : ‖iteratedFDeriv ℝ n (modSymbol s) x‖ = |s| ^ n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, congrFun (modSymbol_iteratedDeriv s n) x,
      norm_mul, norm_pow, norm_modSymbol, mul_one, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs]
  rw [hval]; simp

/-- **Modulation ↦ translation under the Fourier integral** (function level): with Mathlib's normalization
    `𝓕 f(ξ) = ∫ e^{-2πi vξ} f(v) dv`, multiplying by the character `e^{itv}` before transforming shifts the
    argument, `𝓕 (e^{itv} f)(x) = 𝓕 f (x − t/(2π))`. Proved by pointwise equality of the exp-kernel
    integrands (no integrability hypothesis needed). -/
theorem fourier_modSymbol_smul (t : ℝ) (φ : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun v => modSymbol t v * φ v) x = 𝓕 φ (x - t / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with v
  simp only [modSymbol, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
  have hexp : -2 * π * v * x + t * v = -2 * π * v * (x - t / (2 * π)) := by
    have hpi : (2 * π) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp]

/-- **Fourier conjugates modulation into translation on `L²(ℝ)`** (state level): for every `g ∈ L²`,
    `ℱ (e^{itX} g) = τ_{-t/(2π)} (ℱ g)`. Proved by density off the Schwartz maps (`SchwartzMap.toLp`), where
    both sides reduce to the function-level `fourier_modSymbol_smul`; extended to all of `L²` because both
    sides are continuous. -/
theorem fourier_modulationLp_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (modulationLp t g)
      = translationLp (-(t / (2 * π))) (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ g) := by
  refine DenseRange.induction_on
    (p := fun z => MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (modulationLp t z)
      = translationLp (-(t / (2 * π))) (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ z))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top)
    g ?_ ?_
  · exact isClosed_eq
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (modulationLp t).continuous)
      ((translationLp (-(t / (2 * π)))).continuous.comp
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    set ψ := SchwartzMap.smulLeftCLM ℂ (modSymbol t) φ with hψ
    -- `M_{e^{itx}}` on `φ.toLp` is the `toLp` of the Schwartz function `ψ = e^{itx}·φ`
    have hmod : modulationLp t (φ.toLp 2) = ψ.toLp 2 := by
      refine Lp.ext ?_
      filter_upwards [coeFn_modulationLp t (φ.toLp 2), SchwartzMap.coeFn_toLp φ 2,
        SchwartzMap.coeFn_toLp ψ 2] with x h1 h2 h3
      rw [h1, h2, h3, hψ, SchwartzMap.smulLeftCLM_apply_apply (modSymbol_hasTemperateGrowth t),
        smul_eq_mul]
    -- coeFn of `ψ`
    have hψeq : (⇑ψ) = fun v => modSymbol t v * φ v := by
      rw [hψ, SchwartzMap.smulLeftCLM_apply (modSymbol_hasTemperateGrowth t)]
      funext v; rw [smul_eq_mul]
    have hFψ : MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (ψ.toLp 2) = (𝓕 ψ).toLp 2 :=
      SchwartzMap.toLp_fourier_eq ψ
    have hFφ : MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (φ.toLp 2) = (𝓕 φ).toLp 2 :=
      SchwartzMap.toLp_fourier_eq φ
    rw [hmod, hFψ, hFφ]
    -- both sides are now `toLp`s of Schwartz functions; compare a.e.
    refine Lp.ext ?_
    have hqm := (measurePreserving_add_right (volume : Measure ℝ)
      (-(t / (2 * π)))).quasiMeasurePreserving
    have hshift := hqm.tendsto_ae.eventually (SchwartzMap.coeFn_toLp (𝓕 φ) 2 (volume : Measure ℝ))
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 ψ) 2,
      coeFn_translationLp (-(t / (2 * π))) ((𝓕 φ).toLp 2), hshift] with x hxψ hxtr hxsh
    rw [hxψ, hxtr, hxsh]
    simp only [SchwartzMap.fourier_coe]
    rw [hψeq, show (x + -(t / (2 * π))) = x - t / (2 * π) by ring, fourier_modSymbol_smul]

/-- **The Weyl-pair capstone: `τ_{-t/(2π)} = e^{itP}`.** The momentum bounded functional calculus at the
    character symbol `k ↦ e^{itk}` is the translation operator `τ_{-t/(2π)}`. Combined with the modulation
    group `e^{isX}` (the position side) this completes the canonical Weyl pair at the spectral level:
    `X = ∫ x dE`, `P = ∫ k dÊ`, with `e^{itP}` the translation group and `e^{isX}` the modulation group. The
    `2π` in the constant is the honest normalization of Mathlib's Fourier kernel `e^{-2πi x·ξ}`. Axiom-free. -/
theorem translationLp_eq_boundedFC_momentumPVM (t : ℝ) :
    momentumPVM.boundedFC (modSymbol_measurable t) zero_le_one (modSymbol_le_one t)
      = (translationLp (-(t / (2 * π)))).toContinuousLinearMap := by
  ext f
  rw [boundedFC_momentumPVM_eq_fourier_conj_mulOp]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    LinearIsometryEquiv.toContinuousLinearEquiv_symm]
  rw [show mulOp (modSymbol_measurable t) zero_le_one (modSymbol_le_one t)
        ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm f)
      = modulationLp t ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm f) from rfl,
    fourier_modulationLp_apply, LinearIsometryEquiv.apply_symm_apply]

end QIQTH.Spectral.Multiplication
