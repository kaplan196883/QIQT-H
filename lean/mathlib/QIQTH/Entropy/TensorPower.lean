/-
  Tensor powers: `(A ⊗ B)^t = A^t ⊗ B^t`, connecting the abstract weighted-mean concavity
  (`wgSuperadd_mem_Icc`) to the tensor form `A^{1-t} ⊗ B^t` that Lieb's concavity uses (Carlen §6.1).

  The map `A ↦ A ⊗ₖ 1` is a continuous unital `*`-algebra homomorphism `kroneckerRightHom`, and the
  continuous functional calculus commutes with it (`StarAlgHomClass.map_cfc`), giving
  `(A ⊗ₖ 1)^t = A^t ⊗ₖ 1`; symmetrically `(1 ⊗ₖ B)^t = 1 ⊗ₖ B^t`.
-/
import QIQTH.Entropy.WeightedMean

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

end QIQTH.Entropy
