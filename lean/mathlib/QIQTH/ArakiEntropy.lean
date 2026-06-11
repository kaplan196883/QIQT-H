/-
  Araki relative entropy via the relative modular operator — Phase A (foundation).

  Per the GPT-5.5 consultation: the genuine Araki object is built from the RELATIVE
  MODULAR OPERATOR `Δ = L_σ R_ρ⁻¹` on Hilbert–Schmidt space (no unbounded operators),
  via the operator functional calculus `log Δ`; the convention-locking theorem will be
  that it reduces to the finite-dim Umegaki relative entropy `tr(ρ(log ρ − log σ))`
  (σ in the numerator, ρ in the denominator).

  This file establishes the Hilbert–Schmidt space foundation: `HSMat n` = the matrices
  with the Frobenius inner product `⟪A,B⟫ = tr(AᴴB)`, realized via Mathlib's
  `Matrix.toMatrixInnerProductSpace 1`.  (A NON-reducible synonym is mandatory: a
  reducible one would install the Frobenius norm globally on `Matrix n n ℂ`, clobbering
  the operator-norm `CStarAlgebra`/CFC that `matLog` needs.)

  NEXT (focused continuation): the operator layer `Lmul`/`Rmul : HSMat →L[ℂ] HSMat`
  (with the Module-diamond handled), the relative modular operator, the CFC identity
  `log(L_σ R_ρ⁻¹) = L_{log σ} − R_{log ρ}`, and the trace reduction to Umegaki.
-/

import QIQTH.QuantumRelativeEntropy
import Mathlib.Analysis.Matrix.Order

namespace QIQTH.Araki

open scoped Matrix ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Hilbert–Schmidt space** of `n×n` complex matrices: the Frobenius inner product
    `⟪A, B⟫ = tr(B Aᴴ)`, realized via `Matrix.toMatrixInnerProductSpace 1`.  Non-reducible
    so the Frobenius structure stays OFF the global `Matrix n n ℂ` (which keeps its
    operator-norm C⋆-algebra + functional calculus, needed for `matLog`). -/
def HSMat (n : Type) [Fintype n] [DecidableEq n] : Type := Matrix n n ℂ

noncomputable instance : NormedAddCommGroup (HSMat n) :=
  Matrix.toMatrixNormedAddCommGroup (1 : Matrix n n ℂ) Matrix.PosDef.one

noncomputable instance : InnerProductSpace ℂ (HSMat n) :=
  Matrix.toMatrixInnerProductSpace (1 : Matrix n n ℂ) Matrix.PosDef.one.posSemidef

/-- The identification of `HSMat n` with `Matrix n n ℂ` (definitional). -/
def toMat (X : HSMat n) : Matrix n n ℂ := X

/-- The identification of `Matrix n n ℂ` with `HSMat n` (definitional). -/
def ofMat (X : Matrix n n ℂ) : HSMat n := X

@[simp] theorem toMat_ofMat (X : Matrix n n ℂ) : toMat (ofMat X) = X := rfl
@[simp] theorem ofMat_toMat (X : HSMat n) : ofMat (toMat X) = X := rfl

/-- The inner product on `HSMat` is the Frobenius/HS one: `⟪x, y⟫ = tr(y · xᴴ)`. -/
theorem hsInner_eq (x y : HSMat n) :
    (inner ℂ x y : ℂ) = (toMat y * (toMat x)ᴴ).trace := by
  show (toMat y * (1 : Matrix n n ℂ) * (toMat x)ᴴ).trace = _
  rw [Matrix.mul_one]

end QIQTH.Araki
