/-
  Tensor powers: `(A ⊗ B)^t = A^t ⊗ B^t`, connecting the abstract weighted-mean concavity
  (`wgSuperadd_mem_Icc`) to the tensor form `A^{1-t} ⊗ B^t` that Lieb's concavity uses (Carlen §6.1).

  The map `A ↦ A ⊗ₖ 1` is a continuous unital `*`-algebra homomorphism `kroneckerRightHom`, and the
  continuous functional calculus commutes with it (`StarAlgHomClass.map_cfc`), giving
  `(A ⊗ₖ 1)^t = A^t ⊗ₖ 1`; symmetrically `(1 ⊗ₖ B)^t = 1 ⊗ₖ B^t`.
-/
import QIQTH.Entropy.WeightedMean
import QIQTH.Entropy.CommuteRpow
import QIQTH.Entropy.TensorMean

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder Kronecker NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A ↦ A ⊗ₖ 1` as a unital `*`-algebra homomorphism `Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n×n) (n×n) ℂ`. -/
@[simps]
noncomputable def kroneckerRightHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := zero_kronecker 1
  map_add' A B := add_kronecker A B 1
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- `kroneckerRightHom` is continuous (entrywise: each entry of `A ⊗ₖ 1` is `Aᵢₖ · δ`). -/
lemma continuous_kroneckerRightHom :
    Continuous (kroneckerRightHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kroneckerRightHom_apply, Matrix.kroneckerMap_apply]
  exact (continuous_id.matrix_elem i₁ j₁).mul continuous_const

/-- **Tensor power, right factor identity**: `(A ⊗ₖ 1)^t = A^t ⊗ₖ 1` for `0 ≤ A`, `0 ≤ t`. -/
lemma rpow_kronecker_one {A : Matrix n n ℂ} (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    (A ⊗ₖ (1 : Matrix n n ℂ)) ^ t = (A ^ t) ⊗ₖ (1 : Matrix n n ℂ) := by
  have hφA : (0 : Matrix (n × n) (n × n) ℂ) ≤ kroneckerRightHom A :=
    nonneg_iff_posSemidef.mpr ((nonneg_iff_posSemidef.mp hA).kronecker Matrix.PosSemidef.one)
  have := StarAlgHomClass.map_cfc kroneckerRightHom (fun x : ℝ≥0 => x ^ t) A
    (NNReal.continuousOn_rpow_const (Or.inr ht)) continuous_kroneckerRightHom hA hφA
  simpa only [CFC.rpow_def, kroneckerRightHom_apply] using this.symm

/-- `B ↦ 1 ⊗ₖ B` as a unital `*`-algebra homomorphism. -/
@[simps]
noncomputable def kroneckerLeftHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun B := (1 : Matrix n n ℂ) ⊗ₖ B
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, Matrix.one_mul]
  map_zero' := kronecker_zero 1
  map_add' A B := kronecker_add 1 A B
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, kronecker_smul, one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma continuous_kroneckerLeftHom :
    Continuous (kroneckerLeftHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kroneckerLeftHom_apply, Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i₂ j₂)

/-- **Tensor power, left factor identity**: `(1 ⊗ₖ B)^t = 1 ⊗ₖ B^t` for `0 ≤ B`, `0 ≤ t`. -/
lemma rpow_one_kronecker {B : Matrix n n ℂ} (hB : 0 ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ((1 : Matrix n n ℂ) ⊗ₖ B) ^ t = (1 : Matrix n n ℂ) ⊗ₖ (B ^ t) := by
  have hφB : (0 : Matrix (n × n) (n × n) ℂ) ≤ kroneckerLeftHom B :=
    nonneg_iff_posSemidef.mpr (Matrix.PosSemidef.one.kronecker (nonneg_iff_posSemidef.mp hB))
  have := StarAlgHomClass.map_cfc kroneckerLeftHom (fun x : ℝ≥0 => x ^ t) B
    (NNReal.continuousOn_rpow_const (Or.inr ht)) continuous_kroneckerLeftHom hB hφB
  simpa only [CFC.rpow_def, kroneckerLeftHom_apply] using this.symm

/-- **The tensor power identity** `(A ⊗ₖ B)^t = A^t ⊗ₖ B^t` for positive-definite `A, B` and `0 ≤ t`.
    Via `A ⊗ B = (A ⊗ I)(I ⊗ B)` (commuting), commuting-product rpow, and the factor identities. -/
theorem rpow_kronecker {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (A ⊗ₖ B) ^ t = (A ^ t) ⊗ₖ (B ^ t) := by
  have hAB : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hcomm : Commute (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ B) :=
    show _ * _ = _ * _ by rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hAB, commute_rpow_mul (hA.kronecker Matrix.PosDef.one) (Matrix.PosDef.one.kronecker hB) hcomm ht,
    rpow_kronecker_one hA.posSemidef.nonneg ht, rpow_one_kronecker hB.posSemidef.nonneg ht,
    ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-! ### The tensor form `A^{1-t} ⊗ B^t` of Lieb's concavity -/

/-- `(A⁻¹)^t = A^{-t}` for positive-definite `A`, `0 ≤ t` (both equal `(A^t)⁻¹`). -/
lemma rpow_inv_eq {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (A⁻¹) ^ t = A ^ (-t) := by
  have hU : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hcomm : Commute A⁻¹ A := show A⁻¹ * A = A * A⁻¹ by
    rw [Matrix.nonsing_inv_mul _ hU, Matrix.mul_nonsing_inv _ hU]
  have key : (A⁻¹) ^ t * A ^ t = 1 := by
    rw [← commute_rpow_mul hA.inv hA hcomm ht, Matrix.nonsing_inv_mul _ hU, CFC.one_rpow]
  have key2 : A ^ (-t) * A ^ t = 1 := by
    rw [← CFC.rpow_add hA.isUnit, neg_add_cancel, CFC.rpow_zero _ hA.posSemidef.nonneg]
  rw [← Matrix.inv_eq_left_inv key, Matrix.inv_eq_left_inv key2]

/-- `√A · (A⁻¹)^t · √A = A^{1-t}` for positive-definite `A`, `0 ≤ t` (rpow algebra on the single `A`). -/
lemma sqrt_mul_rpow_inv_mul_sqrt {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt A * (A⁻¹) ^ t * CFC.sqrt A = A ^ (1 - t) := by
  rw [rpow_inv_eq hA ht, CFC.sqrt_eq_rpow, ← CFC.rpow_add hA.isUnit, ← CFC.rpow_add hA.isUnit]
  congr 1
  ring

/-- **The tensor weighted mean**: `A #ₜ B` of the commuting `A ⊗ I`, `I ⊗ B` equals `A^{1-t} ⊗ B^t`. -/
lemma wgmean_kronecker {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    wgmean t (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ B) = (A ^ (1 - t)) ⊗ₖ (B ^ t) := by
  have hsqA : CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)) = CFC.sqrt A ⊗ₖ 1 := by
    rw [sqrt_kronecker hA.posSemidef.nonneg Matrix.PosSemidef.one.nonneg, CFC.sqrt_one]
  have hinv : (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ = (CFC.sqrt A)⁻¹ ⊗ₖ 1 := by
    rw [hsqA, inv_kronecker (sqrt_isUnit_det hA) (by simp), inv_one]
  have hinner : (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ * ((1 : Matrix n n ℂ) ⊗ₖ B)
      * (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ = A⁻¹ ⊗ₖ B := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [sqrt_inv_mul_sqrt_inv hA]
  unfold wgmean
  rw [hinner, rpow_kronecker hA.inv hB ht, hsqA, ← mul_kronecker_mul, ← mul_kronecker_mul,
    sqrt_mul_rpow_inv_mul_sqrt hA ht]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- **Joint concavity of `(A,B) ↦ A^{1-t} ⊗ B^t`** (the tensor form Lieb's concavity uses), for
    `t ∈ [0,1]` — Ando's `wgSuperadd_mem_Icc` transported through `wgmean_kronecker`. -/
theorem tensor_rpow_superadditive {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (A₀ ^ (1 - t)) ⊗ₖ (B₀ ^ t) + (A₁ ^ (1 - t)) ⊗ₖ (B₁ ^ t)
      ≤ ((A₀ + A₁) ^ (1 - t)) ⊗ₖ ((B₀ + B₁) ^ t) := by
  have h := wgSuperadd_mem_Icc ht0 ht1 (A₀ ⊗ₖ (1 : Matrix n n ℂ)) (A₁ ⊗ₖ (1 : Matrix n n ℂ))
    ((1 : Matrix n n ℂ) ⊗ₖ B₀) ((1 : Matrix n n ℂ) ⊗ₖ B₁)
    (hA₀.kronecker Matrix.PosDef.one) (hA₁.kronecker Matrix.PosDef.one)
    (Matrix.PosDef.one.kronecker hB₀) (Matrix.PosDef.one.kronecker hB₁)
  rwa [wgmean_kronecker hA₀ hB₀ ht0, wgmean_kronecker hA₁ hB₁ ht0, ← add_kronecker, ← kronecker_add,
    wgmean_kronecker (hA₀.add hA₁) (hB₀.add hB₁) ht0] at h

end QIQTH.Entropy
