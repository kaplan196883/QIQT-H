/-
  Commuting-product rpow: `(P * Q)^t = P^t * Q^t` for commuting positive-definite `P, Q`.

  This is the matrix fact Mathlib lacks (no simultaneous diagonalization of commuting Hermitians).
  Strategy: commuting `√` (`sqrt_mul_of_commute`, via `sqrt_unique`) iterates to the dyadic powers
  `1/2ⁿ`, hence all dyadics `k/2ⁿ`; continuity in the exponent (`continuous_matrix_rpow`) + density of
  dyadics then gives all `t`.  Feeds the tensor power `(A ⊗ B)^t = A^t ⊗ B^t` (TensorPower) and thence
  the `A^{1-t} ⊗ B^t` form of Lieb's concavity.
-/
import QIQTH.Entropy.WeightedMean

namespace QIQTH.Entropy

open Matrix CStarMatrix Filter
open scoped MatrixOrder ComplexOrder NNReal Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of two commuting positive-semidefinite matrices is positive semidefinite:
    `X * Y = √X · Y · √X` (a congruence of `Y`). -/
lemma posSemidef_mul_of_commute {X Y : Matrix n n ℂ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : Commute X Y) :
    (0 : Matrix n n ℂ) ≤ X * Y := by
  have hcomm : Commute (CFC.sqrt X) Y := h.cfcₙ_nnreal NNReal.sqrt
  have heq : X * Y = CFC.sqrt X * Y * CFC.sqrt X := by
    rw [Matrix.mul_assoc, hcomm.symm.eq, ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self X hX]
  rw [heq]
  have hpsd := (nonneg_iff_posSemidef.mp hY).mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [(sqrt_isHermitian X).eq] at hpsd
  exact nonneg_iff_posSemidef.mpr hpsd

/-- **Commuting square root**: `√(P * Q) = √P * √Q` for commuting positive-semidefinite `P, Q`. -/
lemma sqrt_mul_of_commute {P Q : Matrix n n ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : Commute P Q) :
    CFC.sqrt (P * Q) = CFC.sqrt P * CFC.sqrt Q := by
  have hcomm : Commute (CFC.sqrt P) (CFC.sqrt Q) :=
    ((h.cfcₙ_nnreal NNReal.sqrt).symm.cfcₙ_nnreal NNReal.sqrt).symm
  refine CFC.sqrt_unique ?_
    (posSemidef_mul_of_commute (CFC.sqrt_nonneg P) (CFC.sqrt_nonneg Q) hcomm)
  calc CFC.sqrt P * CFC.sqrt Q * (CFC.sqrt P * CFC.sqrt Q)
      = CFC.sqrt P * CFC.sqrt P * (CFC.sqrt Q * CFC.sqrt Q) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt Q), hcomm.symm.eq, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = P * Q := by rw [CFC.sqrt_mul_sqrt_self P hP, CFC.sqrt_mul_sqrt_self Q hQ]

end QIQTH.Entropy
