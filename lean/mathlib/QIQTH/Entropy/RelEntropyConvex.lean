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

/-- `A · log A = U · diag(λᵢ·log λᵢ) · Uᴴ` for positive-definite `A` (eigendecomposition product). -/
lemma mul_matLog_eq {A : Matrix n n ℂ} (hA : A.PosDef) :
    A * QIQTH.QuantumEntropy.matLog hA.1
      = (hA.1.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => (↑(hA.1.eigenvalues i * Real.log (hA.1.eigenvalues i)) : ℂ))
        * (hA.1.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  set μ : n → ℝ := hA.1.eigenvalues with hμ
  -- both `A` and `log A` are `conjStarAlgAut U (diagonal …)`; conjugation is multiplicative
  have hAeq : A = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.1.eigenvectorUnitary
      (diagonal (fun i => (↑(μ i) : ℂ))) := hA.1.spectral_theorem
  have hlog : QIQTH.QuantumEntropy.matLog hA.1
      = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.1.eigenvectorUnitary
        (diagonal (fun i => (↑(Real.log (μ i)) : ℂ))) := rfl
  rw [show A * QIQTH.QuantumEntropy.matLog hA.1
        = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.1.eigenvectorUnitary
            (diagonal (fun i => (↑(μ i) : ℂ)))
          * Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.1.eigenvectorUnitary
            (diagonal (fun i => (↑(Real.log (μ i)) : ℂ))) from by rw [← hAeq, ← hlog],
    ← map_mul, Matrix.diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose]
  congr 2
  ext i
  push_cast
  ring

/-- The derivative of `t ↦ A^{1-t}` at `t = 0` is `-(A · log A)`, for positive-definite `A`. -/
lemma hasDerivAt_rpow_one_sub_zero {A : Matrix n n ℂ} (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ => A ^ (1 - t)) (-(A * QIQTH.QuantumEntropy.matLog hA.1)) 0 := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  set μ : n → ℝ := hA.1.eigenvalues with hμ
  have hkey : (fun t : ℝ => A ^ (1 - t))
      = fun t => U * diagonal (fun i => (↑(μ i ^ (1 - t)) : ℂ)) * Uᴴ := by
    funext t
    rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, Matrix.IsHermitian.cfc_eq hA.1,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  rw [hkey, mul_matLog_eq hA]
  -- entrywise scalar derivative `d/dt λᵢ^{1-t}|₀ = -(λᵢ log λᵢ)`
  have hvec : HasDerivAt (fun t : ℝ => (fun i => (↑(μ i ^ (1 - t)) : ℂ)))
      (fun i => (↑(-(μ i * Real.log (μ i))) : ℂ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have hconst : HasDerivAt (fun s : ℝ => μ i ^ s) (μ i ^ ((1 : ℝ) - 0) * Real.log (μ i)) (1 - 0) :=
      (Real.hasStrictDerivAt_const_rpow (hA.eigenvalues_pos i) ((1 : ℝ) - 0)).hasDerivAt
    have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).const_sub 1
    have hreal : HasDerivAt (fun t : ℝ => μ i ^ (1 - t)) (-(μ i * Real.log (μ i))) 0 := by
      simpa [Real.rpow_one, mul_comm] using hconst.comp 0 hinner
    exact hreal.ofReal_comp
  have hdiag : HasDerivAt (fun t : ℝ => diagonal (fun i => (↑(μ i ^ (1 - t)) : ℂ)))
      (diagonal (fun i => (↑(-(μ i * Real.log (μ i))) : ℂ))) 0 :=
    (Matrix.diagonalLinearMap n ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt_of_eq 0 hvec rfl
  have hconj := (hdiag.const_mul U).mul_const Uᴴ
  have heq : U * diagonal (fun i => (↑(-(μ i * Real.log (μ i))) : ℂ)) * Uᴴ
      = -(U * diagonal (fun i => (↑(μ i * Real.log (μ i)) : ℂ)) * Uᴴ) := by
    have hd : (fun i => (↑(-(μ i * Real.log (μ i))) : ℂ))
        = fun i => -(↑(μ i * Real.log (μ i)) : ℂ) := by
      ext i; push_cast; ring
    rw [hd, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
  rw [heq] at hconj
  exact hconj

/-- The derivative of `t ↦ Tr(A^{1-t}·B^t)` at `t = 0` is `Tr(-(A·log A) + A·log B) = -D(A‖B)`.
    Product rule (matrices are a normed ring under the Frobenius norm) on the two factor derivatives,
    composed with the (continuous, linear) trace. -/
lemma hasDerivAt_trace_rpow_mul {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    HasDerivAt (fun t : ℝ => (A ^ (1 - t) * B ^ t).trace)
      ((-(A * QIQTH.QuantumEntropy.matLog hA.1) + A * QIQTH.QuantumEntropy.matLog hB.1).trace) 0 := by
  have hmul : HasDerivAt (fun t : ℝ => A ^ (1 - t) * B ^ t)
      (-(A * QIQTH.QuantumEntropy.matLog hA.1) + A * QIQTH.QuantumEntropy.matLog hB.1) 0 := by
    have h := (hasDerivAt_rpow_one_sub_zero hA).mul (hasDerivAt_rpow_zero hB)
    rw [CFC.rpow_zero B hB.posSemidef.nonneg, Matrix.mul_one, show (1 : ℝ) - 0 = 1 by ring,
      CFC.rpow_one A hA.posSemidef.nonneg] at h
    exact h
  exact (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt_of_eq
    0 hmul rfl

end QIQTH.Entropy
