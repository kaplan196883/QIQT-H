/-
  **Joint convexity of the quantum relative entropy** (Carlen Thm 6.3), the `t → 0` limit of
  Lieb's concavity.  Step 1: the derivative of `t ↦ B^t` at `t = 0` is `log B`.

  We fix one normed structure on matrices (`Matrix.Norms.Frobenius`, a genuine normed *ring* and
  *algebra*) so that matrix-valued differentiation has consistent instances, and differentiate the
  eigendecomposition `B^t = U·diag(μᵢ^t)·Uᴴ` (the eigenvectors `U` are constant in `t`), reducing to
  the scalar derivative `d/dt μ^t = μ^t·log μ`.
-/
import QIQTH.Entropy.RpowConj
import QIQTH.QuantumRelativeEntropy

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The derivative of `t ↦ B^t` at `t = 0` is the matrix logarithm `log B`, for positive-definite
    `B`.  Differentiate the eigendecomposition `B^t = U·diag(μᵢ^t)·Uᴴ`. -/
lemma hasDerivAt_rpow_zero {B : Matrix n n ℂ} (hB : B.PosDef) :
    HasDerivAt (fun t : ℝ => B ^ t) (QIQTH.QuantumEntropy.matLog hB.1) 0 := by
  set U : Matrix n n ℂ := (hB.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  set μ : n → ℝ := hB.1.eigenvalues with hμ
  -- `B^t = U · diag(μᵢ^t) · Uᴴ` and `log B = U · diag(log μᵢ) · Uᴴ`
  have hkey : (fun t : ℝ => B ^ t)
      = fun t => U * diagonal (fun i => (↑(μ i ^ t) : ℂ)) * Uᴴ := by
    funext t
    rw [CFC.rpow_eq_cfc_real hB.posSemidef.nonneg, Matrix.IsHermitian.cfc_eq hB.1,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  have hlog : QIQTH.QuantumEntropy.matLog hB.1
      = U * diagonal (fun i => (↑(Real.log (μ i)) : ℂ)) * Uᴴ := by
    rw [QIQTH.QuantumEntropy.matLog, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose]
    rfl
  rw [hkey, hlog]
  -- entrywise derivative of the diagonal vector `t ↦ (μᵢ^t)ᵢ`
  have hvec : HasDerivAt (fun t : ℝ => (fun i => (↑(μ i ^ t) : ℂ)))
      (fun i => (↑(Real.log (μ i)) : ℂ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have hs : HasDerivAt (fun t : ℝ => μ i ^ t) (μ i ^ (0 : ℝ) * Real.log (μ i)) 0 :=
      (Real.hasStrictDerivAt_const_rpow (hB.eigenvalues_pos i) 0).hasDerivAt
    simpa [Real.rpow_zero] using hs.ofReal_comp
  -- lift through `diagonal` (a continuous linear map)
  have hdiag : HasDerivAt (fun t : ℝ => diagonal (fun i => (↑(μ i ^ t) : ℂ)))
      (diagonal (fun i => (↑(Real.log (μ i)) : ℂ))) 0 :=
    (Matrix.diagonalLinearMap n ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt_of_eq 0 hvec rfl
  -- conjugate by the constant matrices `U`, `Uᴴ` (Frobenius is a normed algebra)
  exact (hdiag.const_mul U).mul_const Uᴴ

end QIQTH.Entropy
