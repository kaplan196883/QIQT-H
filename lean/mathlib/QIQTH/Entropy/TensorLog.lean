import QIQTH.Entropy.PartialTraceDPI

/-!
# Toward subadditivity: the general tensor logarithm `log(A ⊗ B) = log A ⊗ I + I ⊗ log B`

With partial-trace data processing in hand (`partial_trace_dpi`), the next headline results are the
**subadditivity** `S(ρ) ≤ S(ρ₁) + S(ρ₂)` (Carlen §6.5) and **strong subadditivity**
`S(ρ₁₃)+S(ρ₂₃) ≥ S(ρ₁₂₃)+S(ρ₃)` (§6.6) of the von Neumann entropy. Both rest on the **tensor logarithm**
identity `log(ρ₁ ⊗ ρ₂) = log ρ₁ ⊗ I + I ⊗ log ρ₂`.

`matLog_kron_one` (in `PartialTraceDPI.lean`) already gives the right-factor half `log(A ⊗ 1) = (log A)⊗1`.
This file supplies the **left-factor half** `log(1 ⊗ B) = 1 ⊗ (log B)`, via the two-type left Kronecker
homomorphism `kronLeftHom` and CFC naturality — the exact mirror of `kronRightHom`/`matLog_kron_one`.
The remaining ingredient for the full identity (the commuting-product log rule
`log(PQ) = log P + log Q` for commuting positive `P, Q`, applied to `P = A⊗1`, `Q = 1⊗B`) is the cited
next brick. Axiom-free.
-/

namespace QIQTH.Entropy

open Matrix
open scoped Kronecker ComplexOrder

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `B ↦ 1_n ⊗ₖ B` as a unital ⋆-algebra homomorphism `Matrix p p ℂ →⋆ₐ Matrix (n×p)(n×p) ℂ` (the
left-factor, two-type generalization of `TensorPower.kroneckerLeftHom`). -/
@[simps]
noncomputable def kronLeftHom (n p : Type*) [Fintype n] [DecidableEq n] [Fintype p]
    [DecidableEq p] : Matrix p p ℂ →⋆ₐ[ℂ] Matrix (n × p) (n × p) ℂ where
  toFun B := (1 : Matrix n n ℂ) ⊗ₖ B
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := kronecker_zero 1
  map_add' A B := kronecker_add 1 A B
  commutes' r := by simp only [Algebra.algebraMap_eq_smul_one, kronecker_smul, one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma continuous_kronLeftHom :
    Continuous (kronLeftHom n m : Matrix m m ℂ → Matrix (n × m) (n × m) ℂ) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kronLeftHom_apply, Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i₂ j₂)

/-- **The matrix logarithm of `1 ⊗ B` factors**: `log(1_n ⊗ B) = 1_n ⊗ (log B)`. CFC naturality
(`map_cfc`) under `kronLeftHom` — the left-factor mirror of `matLog_kron_one`. -/
lemma matLog_one_kron {B : Matrix m m ℂ} (hB : B.PosDef)
    (h : ((1 : Matrix n n ℂ) ⊗ₖ B).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h = (1 : Matrix n n ℂ) ⊗ₖ (QIQTH.QuantumEntropy.matLog hB.1) := by
  unfold QIQTH.QuantumEntropy.matLog
  have hf : ContinuousOn Real.log (spectrum ℝ B) :=
    QIQTH.QuantumEntropy.continuousOn_log_spectrum hB
  rw [← h.cfc_eq Real.log, show ((1 : Matrix n n ℂ) ⊗ₖ B) = kronLeftHom n m B from rfl,
    ← StarAlgHomClass.map_cfc (kronLeftHom n m) Real.log B hf continuous_kronLeftHom (ha := hB.1),
    kronLeftHom_apply]
  exact congrArg ((1 : Matrix n n ℂ) ⊗ₖ ·) (hB.1.cfc_eq Real.log)

end QIQTH.Entropy
