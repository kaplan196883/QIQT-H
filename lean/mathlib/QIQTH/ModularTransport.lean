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

namespace QIQTH.ModularTransport

open QIQTH.StandardSubspaceModular ClosedSubmodule Complex

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

end QIQTH.ModularTransport
