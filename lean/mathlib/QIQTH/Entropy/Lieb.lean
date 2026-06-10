/-
  **Lieb's concavity theorem** (Carlen Thm 6.1, the `q+r=1` case): for fixed `K`, the map
  `(A,B) ↦ Tr(Kᴴ · A^{1-t} · K · (Bᵗ)ᵀ)` is jointly concave on positive-definite matrices, `t ∈ [0,1]`.

  This is the joint concavity of `A^{1-t} ⊗ Bᵗ` (`tensor_rpow_superadditive`) read through the
  vec/trace identity `Tr(Kᴴ · A · K · Bᵀ) = ⟨vec K, (B ⊗ₖ A) · vec K⟩` (Mathlib's `kronecker_mulVec_vec`
  and `star_vec_dotProduct_vec`): a positive-semidefinite operator inequality becomes a scalar one
  because `M ↦ ⟨v, M v⟩` is linear and monotone in the Loewner order.
-/
import QIQTH.Entropy.TensorPower
import Mathlib.LinearAlgebra.Matrix.Vec

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lieb's concavity** (superadditive form), the `q+r=1` case: for positive-definite `Aᵢ, Bᵢ`,
    `t ∈ [0,1]`, and any `K`,
    `Tr(Kᴴ A₀^{1-t} K (B₀ᵗ)ᵀ) + Tr(Kᴴ A₁^{1-t} K (B₁ᵗ)ᵀ) ≤ Tr(Kᴴ (A₀+A₁)^{1-t} K ((B₀+B₁)ᵗ)ᵀ)`. -/
theorem lieb_superadditive {A₀ A₁ B₀ B₁ : Matrix n n ℂ} (K : Matrix n n ℂ)
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Kᴴ * A₀ ^ (1 - t) * K * (B₀ ^ t)ᵀ).trace + (Kᴴ * A₁ ^ (1 - t) * K * (B₁ ^ t)ᵀ).trace
      ≤ (Kᴴ * (A₀ + A₁) ^ (1 - t) * K * ((B₀ + B₁) ^ t)ᵀ).trace := by
  -- vec/trace identity: Tr(Kᴴ A K Bᵀ) = ⟨vec K, (B ⊗ₖ A) vec K⟩
  have key : ∀ A B : Matrix n n ℂ,
      (Kᴴ * A * K * Bᵀ).trace = star (vec K) ⬝ᵥ ((B ⊗ₖ A) *ᵥ vec K) := by
    intro A B
    rw [kronecker_mulVec_vec, star_vec_dotProduct_vec]
    simp only [Matrix.mul_assoc]
  rw [key, key, key, ← dotProduct_add, ← Matrix.add_mulVec]
  -- the operator inequality B₀ᵗ⊗A₀^{1-t} + B₁ᵗ⊗A₁^{1-t} ≤ (B₀+B₁)ᵗ⊗(A₀+A₁)^{1-t}
  have hsuper := tensor_rpow_superadditive hB₀ hB₁ hA₀ hA₁
    (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : (1 : ℝ) - t ≤ 1)
  rw [show (1 : ℝ) - (1 - t) = t by ring] at hsuper
  -- the difference is PSD, so its quadratic form at `vec K` is nonnegative
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (Matrix.le_iff.mp hsuper)).2 (vec K)
  rw [Matrix.sub_mulVec, dotProduct_sub] at hq
  exact sub_nonneg.mp hq

end QIQTH.Entropy
