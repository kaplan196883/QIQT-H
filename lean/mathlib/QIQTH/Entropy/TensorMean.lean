/-
  The tensor lift of the operator geometric mean — first step of Ando's tensor argument toward
  Lieb's concavity theorem (Carlen §6.1).

  The geometric mean of the *commuting* operators `A ⊗ I` and `I ⊗ B` is `√A ⊗ √B`
  (`gmean_kronecker`).  Feeding this through `gmean_superadditive` gives the **joint concavity of
  `(A,B) ↦ √A ⊗ √B`** (`tensor_sqrt_superadditive`) — the `p = q = 1/2` case of the joint concavity of
  `A^p ⊗ B^q` that, with the vec/trace identity, yields Lieb's concavity.
-/
import QIQTH.Entropy.GeometricMean
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The square root distributes over the Kronecker product of positive-semidefinite matrices:
    `√(A ⊗ B) = √A ⊗ √B`. -/
lemma sqrt_kronecker {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  refine CFC.sqrt_unique ?_ ?_
  · rw [← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]
  · exact ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg

/-- The inverse distributes over the Kronecker product of invertible matrices:
    `(A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹`. -/
lemma inv_kronecker {A B : Matrix n n ℂ} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← mul_kronecker_mul, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hB,
    one_kronecker_one]

/-- **Tensor geometric mean of commuting operators**: `(A ⊗ I) # (I ⊗ B) = √A ⊗ √B`. -/
lemma gmean_kronecker {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B) :
    gmean (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  have hsqA : CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)) = CFC.sqrt A ⊗ₖ 1 := by
    rw [sqrt_kronecker hA.posSemidef.nonneg Matrix.PosSemidef.one.nonneg, CFC.sqrt_one]
  have hsqAdet : IsUnit (CFC.sqrt A).det := sqrt_isUnit_det hA
  have hinv : (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ = (CFC.sqrt A)⁻¹ ⊗ₖ 1 := by
    rw [hsqA, inv_kronecker hsqAdet (by simp), inv_one]
  -- inner argument: (√A)⁻¹⊗1 · 1⊗B · (√A)⁻¹⊗1 = A⁻¹ ⊗ B
  have hinner : (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ * ((1 : Matrix n n ℂ) ⊗ₖ B)
      * (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ = A⁻¹ ⊗ₖ B := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [sqrt_inv_mul_sqrt_inv hA]
  -- √ of inner = (√A)⁻¹ ⊗ √B
  have hsqinner : CFC.sqrt ((CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹ * ((1 : Matrix n n ℂ) ⊗ₖ B)
      * (CFC.sqrt (A ⊗ₖ (1 : Matrix n n ℂ)))⁻¹) = (CFC.sqrt A)⁻¹ ⊗ₖ CFC.sqrt B := by
    rw [hinner, sqrt_kronecker hA.inv.posSemidef.nonneg hB, ← Matrix.PosSemidef.inv_sqrt hA.posSemidef]
  -- assemble gmean
  unfold gmean
  rw [hsqinner, hsqA, ← mul_kronecker_mul, ← mul_kronecker_mul, sqrt_mul_inv hA]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- **Joint concavity (superadditivity) of `(A,B) ↦ √A ⊗ √B`** — the `p=q=1/2` tensor case, the heart
    of Ando's route to Lieb's concavity.  Follows from `gmean_superadditive` for the commuting tensor
    pairs `Aᵢ ⊗ I`, `I ⊗ Bᵢ` via `gmean_kronecker`. -/
theorem tensor_sqrt_superadditive {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) :
    CFC.sqrt A₀ ⊗ₖ CFC.sqrt B₀ + CFC.sqrt A₁ ⊗ₖ CFC.sqrt B₁
      ≤ CFC.sqrt (A₀ + A₁) ⊗ₖ CFC.sqrt (B₀ + B₁) := by
  have h := gmean_superadditive (hA₀.kronecker Matrix.PosDef.one)
    (hA₁.kronecker Matrix.PosDef.one)
    ((Matrix.PosSemidef.one.kronecker (nonneg_iff_posSemidef.mp hB₀)).nonneg)
    ((Matrix.PosSemidef.one.kronecker (nonneg_iff_posSemidef.mp hB₁)).nonneg)
  rw [gmean_kronecker hA₀ hB₀, gmean_kronecker hA₁ hB₁, ← add_kronecker, ← kronecker_add,
    gmean_kronecker (hA₀.add hA₁) (add_nonneg hB₀ hB₁)] at h
  exact h

end QIQTH.Entropy
