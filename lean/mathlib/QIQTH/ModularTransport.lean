/-
  G2 (GROUNDING_PLAN.md) — the projection/operator transport under unitary conjugacy.

  The first rung of the modular-transport derivation (toward deleting J3's `hmodVac`, Gate 3's
  trace-transport hinge, and the ball-Clausius modular input). Per the binding corrections: ONE `conjU`
  wrapper; the projection transport by the UNIQUENESS characterization of the real orthogonal projection
  under the ℝ-isometry (a ℂ-unitary preserves the real inner product); carrier hypotheses in MEMBERSHIP
  form (`CarrierMap` — no `Submodule.map` plumbing at payoff sites).

  • `conjU U A = U ∘ A ∘ U⁻¹` with the apply lemmas;
  • `starProj_transport` — the core: real orthogonal projections transport along membership-level
    carrier conjugacy (uniqueness route);
  • `carrierMap_mulI` — the `i𝒦` carrier transports automatically (U is ℂ-linear, so it commutes with
    the `I`-scaling defining `mulI`);
  • `projK_transport` / `projIK_transport` / `rvdR_transport` / **`rvdRC_transport`** — the RvD operator
    `R = P + Q` transports: `rvdRC S' = U ∘ rvdRC S ∘ U⁻¹`. G3 (Borel-FC covariance) then transports
    `modUnitary` itself. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.StandardSubspaceModular
import QIQTH.Spectral.SpectralTheorem
import QIQTH.StandardSubspaceModularFlow
import QIQTH.CHMTransport

namespace QIQTH.ModularTransport

open QIQTH.StandardSubspaceModular ClosedSubmodule Complex
open scoped CompactlySupported

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitary conjugation `A ↦ U A U⁻¹` on complex operators. -/
noncomputable def conjU (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (U.toLinearIsometry.toContinuousLinearMap.comp A).comp
    U.symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem conjU_apply (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) (x : H) :
    conjU U A x = U (A (U.symm x)) := rfl

theorem conjU_apply_U (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) (x : H) :
    conjU U A (U x) = U (A x) := by
  rw [conjU_apply, U.symm_apply_apply]

/-- A ℂ-unitary preserves the REAL inner product (real part of the complex one). -/
theorem real_inner_map_map (U : H ≃ₗᵢ[ℂ] H) (a b : H) :
    (inner ℝ (U a) (U b) : ℝ) = inner ℝ a b := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), real_inner_eq_re_inner (𝕜 := ℂ), U.inner_map_map]

/-- The membership-level carrier conjugacy for closed real subspaces. -/
def CarrierMapC (p p' : ClosedSubmodule ℝ H) (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ x : H, x ∈ p' ↔ ∃ y ∈ p, U y = x

/-- **The core transport**: real orthogonal projections transport along carrier conjugacy —
    by the uniqueness characterization (image membership + orthogonality, both preserved by the
    ℝ-isometry). -/
theorem starProj_transport {p p' : ClosedSubmodule ℝ H} {U : H ≃ₗᵢ[ℂ] H}
    (h : CarrierMapC p p' U) (x : H) :
    p'.toSubmodule.starProjection x = U (p.toSubmodule.starProjection (U.symm x)) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((h _).mpr ⟨p.toSubmodule.starProjection (U.symm x),
      Submodule.starProjection_apply_mem _ _, rfl⟩) fun w hw => ?_
  obtain ⟨w', hw', rfl⟩ := (h w).mp hw
  have hx : x - U (p.toSubmodule.starProjection (U.symm x))
      = U (U.symm x - p.toSubmodule.starProjection (U.symm x)) := by
    rw [map_sub, U.apply_symm_apply]
  rw [hx, real_inner_map_map]
  exact Submodule.starProjection_inner_eq_zero (U.symm x) w' hw'

/-- The carrier conjugacy of a `StandardSubspace` pair. -/
def CarrierMap (S S' : StandardSubspace H) (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  CarrierMapC S.toClosedSubmodule S'.toClosedSubmodule U

/-- **`i𝒦` transports automatically**: a ℂ-linear unitary commutes with the `I`-scaling defining
    `mulI`, so the carrier conjugacy passes to the `i𝒦` subspaces. -/
theorem carrierMap_mulI {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) :
    CarrierMapC S.toClosedSubmodule.mulI S'.toClosedSubmodule.mulI U := by
  intro x
  constructor
  · intro hx
    have h1 : (scalarSMulCLE H Complex.UnitI).symm x ∈ S'.toClosedSubmodule :=
      (mem_mapEquiv_iff _ _ _).mp hx
    obtain ⟨y, hy, hUy⟩ := (hK _).mp h1
    refine ⟨(Complex.UnitI : ℂˣ) • y, ?_, ?_⟩
    · refine (mem_mapEquiv_iff _ _ _).mpr ?_
      rw [scalarSMulCLE_symm_apply, inv_smul_smul]
      exact hy
    · rw [Units.smul_def, map_smul, hUy, scalarSMulCLE_symm_apply, ← Units.smul_def,
        smul_inv_smul]
  · rintro ⟨y, hy, rfl⟩
    have h1 : (scalarSMulCLE H Complex.UnitI).symm y ∈ S.toClosedSubmodule :=
      (mem_mapEquiv_iff _ _ _).mp hy
    refine (mem_mapEquiv_iff _ _ _).mpr ?_
    rw [scalarSMulCLE_symm_apply]
    have hcomm : (Complex.UnitI : ℂˣ)⁻¹ • U y = U ((Complex.UnitI : ℂˣ)⁻¹ • y) := by
      rw [Units.smul_def, Units.smul_def, map_smul]
    rw [hcomm]
    exact (hK _).mpr ⟨(Complex.UnitI : ℂˣ)⁻¹ • y, by
      rw [← scalarSMulCLE_symm_apply]
      exact h1, rfl⟩

/-- `P` transports. -/
theorem projK_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (x : H) :
    projK S' x = U (projK S (U.symm x)) :=
  starProj_transport hK x

/-- `Q` transports. -/
theorem projIK_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (x : H) :
    projIK S' x = U (projIK S (U.symm x)) :=
  starProj_transport (carrierMap_mulI hK) x

/-- `R = P + Q` transports (real form). -/
theorem rvdR_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (x : H) :
    rvdR S' x = U (rvdR S (U.symm x)) := by
  simp only [rvdR, ContinuousLinearMap.add_apply, projK_transport hK, projIK_transport hK,
    map_add]

/-- **G2 CAPSTONE — the RvD operator transports under unitary conjugacy:**
    `R_{S′} = U R_S U⁻¹` as ℂ-linear operators. G3's Borel-FC covariance then carries this to the
    modular unitaries themselves. -/
theorem rvdRC_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) :
    rvdRC S' = conjU U (rvdRC S) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [conjU_apply, rvdRC_apply, rvdRC_apply, rvdR_transport hK]

/-! ### G3a — the conjugation star-algebra homomorphism, spectrum transport, CFC covariance

The first half of the Borel-FC covariance crux: `conjU U` bundled as a CONTINUOUS star-algebra
homomorphism on `H →L[ℂ] H`, self-adjointness and spectrum transport, and the CONTINUOUS functional
calculus covariance `cfc f (U T U⁻¹) = U (cfc f T) U⁻¹` (via Mathlib's `StarAlgHomClass.map_cfc` —
ambient real symbols, no dependent spectrum rewrites, per the binding correction). G3b lifts this to
the bounded BOREL calculus through the scalar-measure/RMK chain. -/

/-- The CLM of `U` as a unit of the operator algebra. -/
noncomputable def unitOfLIE (U : H ≃ₗᵢ[ℂ] H) : (H →L[ℂ] H)ˣ where
  val := U.toLinearIsometry.toContinuousLinearMap
  inv := U.symm.toLinearIsometry.toContinuousLinearMap
  val_inv := by
    ext x
    simp
  inv_val := by
    ext x
    simp

theorem conjU_eq_units_conj (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    conjU U A = (unitOfLIE U : H →L[ℂ] H) * A * ((unitOfLIE U)⁻¹ : (H →L[ℂ] H)ˣ) := rfl

/-- Conjugation preserves the ℝ-spectrum. -/
theorem spectrum_conjU (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    spectrum ℝ (conjU U T) = spectrum ℝ T := by
  rw [conjU_eq_units_conj]
  exact spectrum.units_conjugate

/-- Conjugation is continuous on the operator algebra. -/
theorem conjU_continuous (U : H ≃ₗᵢ[ℂ] H) : Continuous (conjU U) := by
  have h1 : Continuous fun A : H →L[ℂ] H =>
      U.toLinearIsometry.toContinuousLinearMap.comp A :=
    (ContinuousLinearMap.compL ℂ H H H U.toLinearIsometry.toContinuousLinearMap).continuous
  have h2 : Continuous fun B : H →L[ℂ] H =>
      B.comp U.symm.toLinearIsometry.toContinuousLinearMap := by
    exact ((ContinuousLinearMap.compL ℂ H H H).flip
      U.symm.toLinearIsometry.toContinuousLinearMap).continuous
  exact h2.comp h1

/-- **The conjugation star-algebra homomorphism** `A ↦ U A U⁻¹`. -/
noncomputable def conjUStarAlgHom (U : H ≃ₗᵢ[ℂ] H) : (H →L[ℂ] H) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := conjU U
  map_one' := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [conjU_apply]
  map_mul' A B := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [conjU_apply, U.symm_apply_apply]
  map_zero' := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [conjU_apply]
  map_add' A B := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [conjU_apply]
  commutes' c := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp [conjU_apply, Algebra.algebraMap_eq_smul_one, map_smul]
  map_star' A := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [conjU_apply, conjU_apply]
    calc inner ℂ (U (ContinuousLinearMap.adjoint A (U.symm x))) y
        = inner ℂ (U (ContinuousLinearMap.adjoint A (U.symm x))) (U (U.symm y)) := by
          rw [U.apply_symm_apply]
      _ = inner ℂ (ContinuousLinearMap.adjoint A (U.symm x)) (U.symm y) :=
          U.inner_map_map _ _
      _ = inner ℂ (U.symm x) (A (U.symm y)) :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℂ (U (U.symm x)) (U (A (U.symm y))) := (U.inner_map_map _ _).symm
      _ = inner ℂ x (U (A (U.symm y))) := by rw [U.apply_symm_apply]

@[simp] theorem conjUStarAlgHom_apply (U : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    conjUStarAlgHom U A = conjU U A := rfl

/-- Conjugation preserves self-adjointness. -/
theorem conjU_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (U : H ≃ₗᵢ[ℂ] H) :
    IsSelfAdjoint (conjU U T) := by
  have h := map_star (conjUStarAlgHom U) T
  rw [conjUStarAlgHom_apply, conjUStarAlgHom_apply, hT.star_eq] at h
  exact h.symm

/-- **G3a CAPSTONE — CONTINUOUS functional calculus covariance under conjugation:**
    `cfc f (U T U⁻¹) = U (cfc f T) U⁻¹` for ambient real symbols (Mathlib functoriality riding the
    conjugation star-hom). G3b lifts this to the bounded Borel calculus. -/
theorem cfc_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T)) :
    cfc f (conjU U T) = conjU U (cfc f T) := by
  have hφ : Continuous (conjUStarAlgHom U) := conjU_continuous U
  have hφa : IsSelfAdjoint (conjUStarAlgHom U T) := conjU_isSelfAdjoint hT U
  have h := StarAlgHomClass.map_cfc (R := ℝ) (conjUStarAlgHom U) f T hf hφ hT hφa
  rw [conjUStarAlgHom_apply] at h
  exact h.symm

/-! ### G3b(i) — the scalar spectral measure transports

The Riesz–Markov scalar measure of the conjugated operator at the transported vector is the pushforward
of the original along the (value-preserving) spectrum homeomorphism — proved by testing against C_c
functions, Tietze-extended to ambient symbols so G3a's `cfc_conjU` applies (the binding correction:
ambient symbols, no dependent spectrum rewrites). -/

/-- The value-preserving spectrum homeomorphism induced by conjugation. -/
noncomputable def specHomeo (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    spectrum ℝ T ≃ₜ spectrum ℝ (conjU U T) :=
  Homeomorph.setCongr (spectrum_conjU U T).symm

@[simp] theorem specHomeo_val (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (ω : spectrum ℝ T) :
    ((specHomeo U T ω : spectrum ℝ (conjU U T)) : ℝ) = (ω : ℝ) := rfl

open QIQTH.SpectralTheorem MeasureTheory RCLike CompactlySupportedContinuousMap in
/-- **G3b(i) — the scalar spectral measure transports:** `μ^{UTU⁻¹}_{Ux} = (specHomeo)_* μ^T_x`. -/
theorem specMeasure_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x : H) :
    specMeasure (conjU U T) (conjU_isSelfAdjoint hT U) (U x)
      = Measure.map (specHomeo U T) (specMeasure T hT x) := by
  have hT' := conjU_isSelfAdjoint hT U
  haveI : CompactSpace (spectrum ℝ T) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact T)
  haveI : CompactSpace (spectrum ℝ (conjU U T)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact (conjU U T))
  haveI : IsFiniteMeasure (Measure.map (specHomeo U T) (specMeasure T hT x)) :=
    Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq
    (spectrum.isClosed (𝕜 := ℝ) (conjU U T)) f.toContinuousMap
  have hgOn : ContinuousOn (⇑g) (spectrum ℝ T) := g.continuous.continuousOn
  have hgOn' : ContinuousOn (⇑g) (spectrum ℝ (conjU U T)) := g.continuous.continuousOn
  set fT : C_c(spectrum ℝ T, ℝ) :=
    continuousMapEquiv (f.toContinuousMap.comp
      ⟨⇑(specHomeo U T), (specHomeo U T).continuous⟩) with hfT
  have hf_cfc : cfcHom (R := ℝ) hT' f.toContinuousMap = cfc (⇑g) (conjU U T) := by
    rw [cfc_apply (⇑g) (conjU U T) hT' hgOn']
    congr 1
    ext ω
    rw [← hg]
    rfl
  have hfT_cfc : cfcHom (R := ℝ) hT fT.toContinuousMap = cfc (⇑g) T := by
    rw [cfc_apply (⇑g) T hT hgOn]
    congr 1
    ext ω
    show f.toContinuousMap (specHomeo U T ω) = ((spectrum ℝ T).restrict ⇑g) ω
    rw [← hg]
    rfl
  calc ∫ ω, f ω ∂(specMeasure (conjU U T) hT' (U x))
      = RCLike.re (inner ℂ (U x) (cfcHom hT' f.toContinuousMap (U x))) :=
        integral_specMeasure (conjU U T) hT' (U x) f
    _ = RCLike.re (inner ℂ (U x) (cfc (⇑g) (conjU U T) (U x))) := by rw [hf_cfc]
    _ = RCLike.re (inner ℂ (U x) (conjU U (cfc (⇑g) T) (U x))) := by
        rw [cfc_conjU U hT (⇑g) hgOn]
    _ = RCLike.re (inner ℂ (U x) (U (cfc (⇑g) T x))) := by rw [conjU_apply_U]
    _ = RCLike.re (inner ℂ x (cfc (⇑g) T x)) := by rw [U.inner_map_map]
    _ = RCLike.re (inner ℂ x (cfcHom hT fT.toContinuousMap x)) := by rw [hfT_cfc]
    _ = ∫ ω, fT ω ∂(specMeasure T hT x) := (integral_specMeasure T hT x fT).symm
    _ = ∫ ω, f (specHomeo U T ω) ∂(specMeasure T hT x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        rfl
    _ = ∫ ω, f ω ∂(Measure.map (specHomeo U T) (specMeasure T hT x)) :=
        (integral_map (specHomeo U T).continuous.aemeasurable
          f.continuous.aestronglyMeasurable).symm

/-! ### G3b(ii) — the Borel functional calculus transports (THE CRUX CAPSTONE)

Everything above the scalar measures is defined from them, so the transport lifts by unfolding:
`qForm` → `cForm` (polarization; U is ℂ-linear) → `specProj` (inner ext) → the PVM's scalar measure
(pushforward) → `diagInt` (integral_map) → `bilinDiag` (polarization again) → **`borelFC_conjU`**
(the `inner_borelFC` calc chain). -/

open QIQTH.SpectralTheorem MeasureTheory in
theorem qForm_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {s' : Set (spectrum ℝ (conjU U T))} (hs' : MeasurableSet s') (z : H) :
    qForm (conjU U T) (conjU_isSelfAdjoint hT U) s' (U z)
      = qForm T hT (specHomeo U T ⁻¹' s') z := by
  rw [qForm, qForm, specMeasure_conjU U hT z, measureReal_def, measureReal_def,
    Measure.map_apply (specHomeo U T).continuous.measurable hs']

open QIQTH.SpectralTheorem in
theorem cForm_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {s' : Set (spectrum ℝ (conjU U T))} (hs' : MeasurableSet s') (x y : H) :
    cForm (conjU U T) (conjU_isSelfAdjoint hT U) s' (U x) (U y)
      = cForm T hT (specHomeo U T ⁻¹' s') x y := by
  rw [cForm, cForm, bForm, bForm, bForm, bForm]
  rw [show U x + U y = U (x + y) from (map_add U x y).symm,
    show U x - U y = U (x - y) from (map_sub U x y).symm,
    show Complex.I • U y = U (Complex.I • y) from (map_smul U Complex.I y).symm,
    show U x + U (Complex.I • y) = U (x + Complex.I • y) from (map_add U x _).symm,
    show U x - U (Complex.I • y) = U (x - Complex.I • y) from (map_sub U x _).symm,
    qForm_conjU U hT hs', qForm_conjU U hT hs', qForm_conjU U hT hs', qForm_conjU U hT hs']

open QIQTH.SpectralTheorem in
/-- The spectral projections transport: `E'(s') = U E(e⁻¹ s') U⁻¹`. -/
theorem specProj_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {s' : Set (spectrum ℝ (conjU U T))} (hs' : MeasurableSet s') :
    specProj (conjU U T) (conjU_isSelfAdjoint hT U) s'
      = conjU U (specProj T hT (specHomeo U T ⁻¹' s')) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine ext_inner_right ℂ fun y => ?_
  rw [inner_specProj]
  conv_lhs => rw [show z = U (U.symm z) from (U.apply_symm_apply z).symm,
    show y = U (U.symm y) from (U.apply_symm_apply y).symm]
  rw [cForm_conjU U hT hs', ← inner_specProj, conjU_apply, ← U.inner_map_map
    (specProj T hT (specHomeo U T ⁻¹' s') (U.symm z)) (U.symm y), U.apply_symm_apply]

open QIQTH.Spectral QIQTH.SpectralTheorem MeasureTheory in
/-- The PVM's scalar measure transports as a pushforward. -/
theorem pvmScalarMeasure_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x : H) :
    (PVM_of_selfAdjoint (conjU U T) (conjU_isSelfAdjoint hT U)).scalarMeasure (U x)
      = Measure.map (specHomeo U T) ((PVM_of_selfAdjoint T hT).scalarMeasure x) := by
  refine Measure.ext fun s' hs' => ?_
  rw [(PVM_of_selfAdjoint (conjU U T) (conjU_isSelfAdjoint hT U)).scalarMeasure_apply (U x) hs',
    Measure.map_apply (specHomeo U T).continuous.measurable hs',
    (PVM_of_selfAdjoint T hT).scalarMeasure_apply x
      (hs'.preimage (specHomeo U T).continuous.measurable)]
  congr 2
  rw [show (PVM_of_selfAdjoint (conjU U T) (conjU_isSelfAdjoint hT U)).E s'
      = specProj (conjU U T) (conjU_isSelfAdjoint hT U) s' from rfl,
    specProj_conjU U hT hs', conjU_apply_U, U.norm_map]
  rfl

open QIQTH.Spectral QIQTH.SpectralTheorem MeasureTheory in
theorem diagInt_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {f' : spectrum ℝ (conjU U T) → ℂ} (hf' : Measurable f') (x : H) :
    (PVM_of_selfAdjoint (conjU U T) (conjU_isSelfAdjoint hT U)).diagInt f' (U x)
      = (PVM_of_selfAdjoint T hT).diagInt (f' ∘ (specHomeo U T)) x := by
  rw [QIQTH.Spectral.ProjectionValuedMeasure.diagInt,
    QIQTH.Spectral.ProjectionValuedMeasure.diagInt, pvmScalarMeasure_conjU U hT,
    integral_map (specHomeo U T).continuous.aemeasurable hf'.aestronglyMeasurable]
  rfl

open QIQTH.Spectral QIQTH.SpectralTheorem in
theorem bilinDiag_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {f' : spectrum ℝ (conjU U T) → ℂ} (hf' : Measurable f') (x y : H) :
    (PVM_of_selfAdjoint (conjU U T) (conjU_isSelfAdjoint hT U)).bilinDiag f' (U x) (U y)
      = (PVM_of_selfAdjoint T hT).bilinDiag (f' ∘ (specHomeo U T)) x y := by
  rw [QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag,
    QIQTH.Spectral.ProjectionValuedMeasure.bilinDiag]
  rw [show U x + U y = U (x + y) from (map_add U x y).symm,
    show U x - U y = U (x - y) from (map_sub U x y).symm,
    show Complex.I • U x + U y = U (Complex.I • x + y) from by
      rw [map_add, map_smul],
    show Complex.I • U x - U y = U (Complex.I • x - y) from by
      rw [map_sub, map_smul],
    diagInt_conjU U hT hf', diagInt_conjU U hT hf', diagInt_conjU U hT hf',
    diagInt_conjU U hT hf']

open QIQTH.SpectralTheorem in
/-- **G3 CAPSTONE — the bounded BOREL functional calculus transports under conjugation:**
    `f(UTU⁻¹) = U · (f∘e)(T) · U⁻¹` for bounded measurable symbols. The generator-uniqueness shortcut
    was rejected (binding); this is the honest scalar-measure route, completed. -/
theorem borelFC_conjU (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {f' : spectrum ℝ (conjU U T) → ℂ} (hf' : Measurable f')
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f' ω‖ ≤ C) :
    borelFC (conjU U T) (conjU_isSelfAdjoint hT U) hf' hC0 hC
      = conjU U (borelFC T hT (hf'.comp (specHomeo U T).continuous.measurable) hC0
          (fun ω => hC _)) := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left ℂ fun x => ?_
  conv_lhs => rw [show x = U (U.symm x) from (U.apply_symm_apply x).symm,
    show y = U (U.symm y) from (U.apply_symm_apply y).symm]
  rw [inner_borelFC, bilinDiag_conjU U hT hf', ← inner_borelFC, conjU_apply,
    ← U.inner_map_map (U.symm x), U.apply_symm_apply]

/-! ### G4 — the modular unitaries transport; the payoffs

`modUnitary S t = u_t(rvdRC S)` with an AMBIENT symbol (`modChar t`), so the transport is one
operator-congruence (G2) + the crux (G3). Payoffs: J3's `hmodVac` carried field is DELETED (a
`CHMTransportData` now needs NO modular input — carrier conjugacy suffices); Gate 3's covariance hinge
is fed by the derived correlator covariance; the ball family rides the same theorem. The residue
everywhere is the GEOMETRIC carrier-conjugacy data itself — geometry, not modular theory. -/

/-- `borelFC` congruence along an operator equality, for AMBIENT symbols (dependent-type-safe:
    `subst` + proof irrelevance). -/
theorem borelFC_congr_op {T T' : H →L[ℂ] H} (h : T = T') (hT : IsSelfAdjoint T)
    (hT' : IsSelfAdjoint T') (g : ℝ → ℂ)
    (hg : Measurable fun ω : spectrum ℝ T => g ω.val)
    (hg' : Measurable fun ω : spectrum ℝ T' => g ω.val)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω : spectrum ℝ T, ‖g ω.val‖ ≤ C)
    (hC' : ∀ ω : spectrum ℝ T', ‖g ω.val‖ ≤ C) :
    QIQTH.SpectralTheorem.borelFC T' hT' hg' hC0 hC'
      = QIQTH.SpectralTheorem.borelFC T hT hg hC0 hC := by
  subst h
  rfl

open QIQTH.SpectralTheorem in
/-- **G4 CAPSTONE — the modular unitaries transport under carrier conjugacy:**
    `Δ^{it}_{S′} = U Δ^{it}_S U⁻¹`. One congruence (G2's `rvdRC_transport`) + the crux (G3's
    `borelFC_conjU`); the symbol is ambient. -/
theorem modUnitary_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (t : ℝ) :
    modUnitary S' t = conjU U (modUnitary S t) := by
  have hR : conjU U (rvdRC S) = rvdRC S' := (rvdRC_transport hK).symm
  have hT : IsSelfAdjoint (conjU U (rvdRC S)) :=
    conjU_isSelfAdjoint (rvdRC_isSelfAdjoint S) U
  have hg : Measurable fun ω : spectrum ℝ (conjU U (rvdRC S)) => modChar t ω.val :=
    (modChar_measurable t).comp measurable_subtype_coe
  have hC : ∀ ω : spectrum ℝ (conjU U (rvdRC S)), ‖modChar t ω.val‖ ≤ 1 :=
    fun ω => le_of_eq (modChar_norm t ω.val)
  have e1 : QIQTH.SpectralTheorem.borelFC (rvdRC S') (rvdRC_isSelfAdjoint S')
      (modSpecFun_measurable S' t) zero_le_one (modSpecFun_norm_le S' t)
      = QIQTH.SpectralTheorem.borelFC (conjU U (rvdRC S)) hT hg zero_le_one hC :=
    borelFC_congr_op hR hT (rvdRC_isSelfAdjoint S') (modChar t) hg
      (modSpecFun_measurable S' t) zero_le_one hC (modSpecFun_norm_le S' t)
  rw [modUnitary, modUnitary]
  refine e1.trans ?_
  refine (borelFC_conjU U (rvdRC_isSelfAdjoint S) hg zero_le_one hC).trans ?_
  rfl

/-- The pointwise (caller-friendly) form. -/
theorem modUnitary_apply_transport {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (t : ℝ) (x : H) :
    modUnitary S' t (U x) = U (modUnitary S t x) := by
  rw [modUnitary_transport hK, conjU_apply_U]

open QIQTH.BallModular in
/-- **J3 PAYOFF — the `hmodVac` carried field is DELETED.** A `CHMTransportData` can now be built from
    the GEOMETRIC data alone: carrier conjugacy per ball supplies the modular transport as a theorem
    (`modUnitary_apply_transport`). The residue is the carrier-conjugacy data itself — geometry. -/
noncomputable def CHMTransportDataOfCarrierMap {Ball : Type*}
    (W : StandardSubspace H) (vac : H) (boost : ℝ → H → H)
    (hBW : ∀ t, boost t vac = modUnitary W t vac)
    (U : Ball → (H ≃ₗᵢ[ℂ] H)) (S : Ball → StandardSubspace H)
    (flow : Ball → ℝ → H → H)
    (hflow : ∀ B t x, flow B t x = U B (boost t ((U B).symm x)))
    (hK : ∀ B, CarrierMap W (S B) (U B)) :
    CHMTransportData Ball H where
  W := W
  vac := vac
  boost := boost
  hBW := hBW
  U := U
  S := S
  flow := flow
  hflow := hflow
  hmodVac := fun B t => modUnitary_apply_transport (hK B) t vac

/-- **Gate-3 PAYOFF — the modular correlators are carrier-covariant** — the derived covariance datum
    the state-level gate's `Sren_cov`/`CovariantExpectation` hinge consumes. -/
theorem modUnitary_inner_cov {S S' : StandardSubspace H} {U : H ≃ₗᵢ[ℂ] H}
    (hK : CarrierMap S S' U) (t : ℝ) (x y : H) :
    inner ℂ (U x) (modUnitary S' t (U y)) = inner ℂ x (modUnitary S t y) := by
  rw [modUnitary_apply_transport hK, U.inner_map_map]

/-- **Ball-family PAYOFF** — per-ball modular covariance from per-ball geometric carrier conjugacy
    (the ball-Clausius modular input, replaced by geometry). -/
theorem ball_modUnitary_cov {Ball : Type*} {W : StandardSubspace H}
    {U : Ball → (H ≃ₗᵢ[ℂ] H)} {S : Ball → StandardSubspace H}
    (hK : ∀ B, CarrierMap W (S B) (U B)) (B : Ball) (t : ℝ) (x : H) :
    modUnitary (S B) t (U B x) = U B (modUnitary W t x) :=
  modUnitary_apply_transport (hK B) t x

end QIQTH.ModularTransport
