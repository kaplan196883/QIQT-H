/-
  THE MODULAR CONJUGATION J3 (THE_MODULAR_CONJUGATION_PLAN.md) — the σ-semilinear
  completion: `jRaw → jPre → towerJ`, with NO ℝ-reduction and NO unbounded operator.

  Deliverables:
  • `jRaw` — the stage conjugations glued on the raw direct sum, bundled as a genuinely
    SEMILINEAR map `⨁ →ₛₗ[starRingEnd ℂ] ⨁` (`DirectSum.toAddMonoid` on the additive
    skeleton `jStage_add`, the conjugate-scalar law by `DirectSum.induction_on` from
    `jStage_smul`); `jRaw_of` — the componentwise action.
  • `rawInner_jRaw` ★ — THE RAW ANTI-ISOMETRY `⟪Jx, Jy⟫ = ⟪y, x⟫`: double induction
    reduces to pure components, J2's cross-stage law `cornerEmbed_jStage` pushes the
    conjugation through the embeddings into the common stage `C ⊔ C'`, and J1's
    single-stage anti-isometry `gnsInner_jStage` flips the slots.
  • `jPre : TowerPre →SL[starRingEnd ℂ] TowerPre` — the continuous conjugate-linear
    pre-operator (`LinearMap.mkContinuous` with constant `1`; the seminorm is preserved
    because the anti-isometry at `x = y` gives `⟪Jx, Jx⟫ = ⟪x, x⟫`).
  • `towerJ : TowerGNS →SL[starRingEnd ℂ] TowerGNS := jPre.completion` — Mathlib's
    `ContinuousLinearMap.completion` is SEMILINEAR-GENERIC, so the star-twisted extension
    is the SAME one-liner as `towerFlow`; `towerJ_coe` — the dense-subspace action.

  HONEST SCOPE: plumbing only — the global conjugate-linear operator exists and acts
  componentwise on the dense core. NO anti-unitary pack yet (⟪Jξ,Jη⟫ = ⟪η,ξ⟫ on the
  completion, J² = 1, JΩ = Ω are J4), no polar decomposition (J5), no Tomita II claim.

  LEAN ARCHITECTURE (the R3 lesson, binding): the working lemmas (`jRaw`, `jRaw_of`,
  `rawInner_jRaw`) live at the RAW `⨁` type; the `TowerPre`-typed items (`jPreₗ`, the norm
  bound, `jPre`) are final wrappers accepted by application-position definitional equality.
  Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.JEmbed

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The raw layer — the glued conjugation on `⨁` (the R3 lesson: no synonym here) -/

/-- The stage conjugation bundled additively (`jStage_add`). -/
noncomputable def jStageₐ (C : Finset M) : DiamondAlg L C →+ DiamondAlg L C :=
  AddMonoidHom.mk' (jStage L ω β C) (jStage_add L ω β C)

/-- The additive skeleton of the raw conjugation: the component at stage `C` is conjugated
    IN PLACE by `jStage C` — same stage, no stage shift (exactly the `flowRaw` shape). -/
noncomputable def jRawₐ :
    (⨁ C : Finset M, DiamondAlg L C) →+ (⨁ C : Finset M, DiamondAlg L C) :=
  DirectSum.toAddMonoid fun C =>
    (DirectSum.of (fun C : Finset M => DiamondAlg L C) C).comp (jStageₐ L ω β C)

@[simp] theorem jRawₐ_of (C : Finset M) (a : DiamondAlg L C) :
    jRawₐ L ω β (DirectSum.of _ C a)
      = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (jStage L ω β C a) := by
  rw [jRawₐ, DirectSum.toAddMonoid_of]
  rfl

/-- **The raw conjugation pre-operator** — the stage conjugations glued on the raw direct
    sum, as a genuinely SEMILINEAR map over `starRingEnd ℂ` (no ℝ-reduction: the
    conjugate-scalar law `J(c • x) = conj c • J x` is carried in the TYPE). -/
noncomputable def jRaw :
    (⨁ C : Finset M, DiamondAlg L C) →ₛₗ[starRingEnd ℂ] (⨁ C : Finset M, DiamondAlg L C) where
  toFun x := jRawₐ L ω β x
  map_add' x y := (jRawₐ L ω β).map_add x y
  map_smul' c x := by
    induction x using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero (jRawₐ L ω β), smul_zero]
    | of C a =>
      have hsm : c • DirectSum.of (fun C : Finset M => DiamondAlg L C) C a
          = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (c • a) := by
        rw [← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, map_smul]
      have hsm' : starRingEnd ℂ c
            • DirectSum.of (fun C : Finset M => DiamondAlg L C) C (jStage L ω β C a)
          = DirectSum.of (fun C : Finset M => DiamondAlg L C) C
              (starRingEnd ℂ c • jStage L ω β C a) := by
        rw [← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, map_smul]
      show jRawₐ L ω β (c • DirectSum.of _ C a)
          = starRingEnd ℂ c • jRawₐ L ω β (DirectSum.of _ C a)
      rw [hsm, jRawₐ_of, jRawₐ_of, jStage_smul, hsm']
    | add x₁ x₂ h₁ h₂ =>
      show jRawₐ L ω β (c • (x₁ + x₂)) = starRingEnd ℂ c • jRawₐ L ω β (x₁ + x₂)
      rw [smul_add, map_add (jRawₐ L ω β), h₁, h₂, map_add (jRawₐ L ω β), smul_add]

@[simp] theorem jRaw_of (C : Finset M) (a : DiamondAlg L C) :
    jRaw L ω β (DirectSum.of _ C a)
      = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (jStage L ω β C a) :=
  jRawₐ_of L ω β C a

/-! ### ★ The raw anti-isometry -/

/-- **★ THE RAW ANTI-ISOMETRY**: `⟪Jx, Jy⟫ = ⟪y, x⟫` on the raw direct sum — double
    induction reduces to pure components, where J2's cross-stage law `cornerEmbed_jStage`
    pushes the conjugation through the embeddings into the common stage `C ⊔ C'` and J1's
    single-stage anti-isometry `gnsInner_jStage` flips the slots (`pairInner_embed`
    re-expresses the flipped pairing at the SAME common stage). -/
theorem rawInner_jRaw (x y : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β (jRaw L ω β x) (jRaw L ω β y) = rawInner L ω β y x := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (jRaw L ω β), map_zero (rawInner L ω β), AddMonoidHom.zero_apply,
      map_zero (rawInner L ω β y)]
  | of C a =>
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (jRaw L ω β),
        map_zero (rawInner L ω β (jRaw L ω β (DirectSum.of _ C a))),
        map_zero (rawInner L ω β), AddMonoidHom.zero_apply]
    | of C' b =>
      rw [jRaw_of, jRaw_of, rawInner_of_of, rawInner_of_of, pairInner,
        cornerEmbed_jStage, cornerEmbed_jStage, gnsInner_jStage,
        pairInner_embed L ω β C' C (C ⊔ C') Finset.subset_union_right
          Finset.subset_union_left b a]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (jRaw L ω β),
        map_add (rawInner L ω β (jRaw L ω β (DirectSum.of _ C a))), h₁, h₂,
        map_add (rawInner L ω β), AddMonoidHom.add_apply]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (jRaw L ω β),
      map_add (rawInner L ω β) (jRaw L ω β x₁) (jRaw L ω β x₂),
      AddMonoidHom.add_apply, h₁, h₂, map_add (rawInner L ω β y)]

/-! ### The synonym wrappers (application-position defeq only — the R3 lesson) -/

/-- The conjugation at the synonym, as a plain semilinear map (fields delegate to the raw
    map by definitional equality). -/
noncomputable def jPreₗ : TowerPre L ω β →ₛₗ[starRingEnd ℂ] TowerPre L ω β where
  toFun x := jRaw L ω β x
  map_add' x y := (jRaw L ω β).map_add x y
  map_smul' c x := map_smulₛₗ (jRaw L ω β) c x

@[simp] theorem jPreₗ_apply (x : TowerPre L ω β) :
    jPreₗ L ω β x = jRaw L ω β x := rfl

/-- The conjugation preserves the tower seminorm (raw anti-isometry at `x = y` — the
    flipped slots agree there — + `√(‖·‖²)`). -/
theorem jPreₗ_norm_eq (x : TowerPre L ω β) :
    ‖jPreₗ L ω β x‖ = ‖x‖ := by
  have hinner : ⟪jPreₗ L ω β x, jPreₗ L ω β x⟫_ℂ = ⟪x, x⟫_ℂ :=
    rawInner_jRaw L ω β x x
  have h2 : ‖jPreₗ L ω β x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (jPreₗ L ω β x),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) x, hinner]
  calc ‖jPreₗ L ω β x‖
      = Real.sqrt (‖jPreₗ L ω β x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [h2]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `mkContinuous`-shaped bound with constant `1` (the conjugation is norm-preserving,
    hence trivially bounded). -/
theorem jPreₗ_norm_le (x : TowerPre L ω β) :
    ‖jPreₗ L ω β x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  exact le_of_eq (jPreₗ_norm_eq L ω β x)

/-- **The continuous conjugation pre-operator**: the glued stage conjugations as a
    CONTINUOUS conjugate-linear map on the tower pre-space (constant `1`), ready for
    extension to the completion — `LinearMap.mkContinuous` is σ-generic. -/
noncomputable def jPre : TowerPre L ω β →SL[starRingEnd ℂ] TowerPre L ω β :=
  LinearMap.mkContinuous (jPreₗ L ω β) 1 fun x => jPreₗ_norm_le L ω β x

@[simp] theorem jPre_apply (x : TowerPre L ω β) :
    jPre L ω β x = jRaw L ω β x := rfl

/-- The continuous conjugation pre-operator preserves the tower seminorm. -/
theorem jPre_norm_eq (x : TowerPre L ω β) :
    ‖jPre L ω β x‖ = ‖x‖ :=
  jPreₗ_norm_eq L ω β x

/-! ### J3 CAPSTONE — the conjugation on the completion -/

/-- **THE GLOBAL CONJUGATION PRE-OPERATOR ON THE TOWER HILBERT SPACE** — the stage
    conjugations `jStage a = √ρ·aᴴ·√ρ⁻¹`, glued by the tower and extended to the
    completion by the SEMILINEAR-generic `ContinuousLinearMap.completion` (no ℝ-reduction
    anywhere: `towerJ` is conjugate-linear BY TYPE). Plumbing only — the anti-unitary
    pack (inner-flip on the completion, J² = 1, JΩ = Ω) is J4. -/
noncomputable def towerJ : TowerGNS L ω β →SL[starRingEnd ℂ] TowerGNS L ω β :=
  (jPre L ω β).completion

@[simp] theorem towerJ_coe (x : TowerPre L ω β) :
    towerJ L ω β (x : TowerGNS L ω β)
      = ((jPre L ω β x : TowerPre L ω β) : TowerGNS L ω β) :=
  (jPre L ω β).completion_apply_coe x

end QIQTH.TowerGNS
