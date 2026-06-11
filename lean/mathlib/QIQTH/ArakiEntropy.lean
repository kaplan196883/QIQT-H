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

instance : FiniteDimensional ℂ (HSMat n) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix n n ℂ))

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

/-- The linear identification `HSMat n ≃ₗ[ℂ] Matrix n n ℂ` (definitional; the modules coincide). -/
def hsEquiv : HSMat n ≃ₗ[ℂ] Matrix n n ℂ where
  toFun := toMat
  invFun := ofMat
  left_inv := ofMat_toMat
  right_inv := toMat_ofMat
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### The relative-modular building blocks: left/right multiplication on HS -/

/-- Left multiplication `X ↦ A · X` as a continuous ℂ-linear map on `HSMat`. -/
noncomputable def Lmul (A : Matrix n n ℂ) : HSMat n →L[ℂ] HSMat n :=
  (hsEquiv.symm.toLinearMap ∘ₗ LinearMap.mulLeft ℂ A ∘ₗ hsEquiv.toLinearMap).toContinuousLinearMap

/-- Right multiplication `X ↦ X · A` as a continuous ℂ-linear map on `HSMat`. -/
noncomputable def Rmul (A : Matrix n n ℂ) : HSMat n →L[ℂ] HSMat n :=
  (hsEquiv.symm.toLinearMap ∘ₗ LinearMap.mulRight ℂ A ∘ₗ hsEquiv.toLinearMap).toContinuousLinearMap

@[simp] theorem Lmul_apply (A : Matrix n n ℂ) (X : HSMat n) :
    toMat (Lmul A X) = A * toMat X := by
  simp only [Lmul, LinearMap.coe_toContinuousLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.mulLeft_apply]
  rfl

@[simp] theorem Rmul_apply (A : Matrix n n ℂ) (X : HSMat n) :
    toMat (Rmul A X) = toMat X * A := by
  simp only [Rmul, LinearMap.coe_toContinuousLinearMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.mulRight_apply]
  rfl

theorem toMat_injective : Function.Injective (toMat : HSMat n → Matrix n n ℂ) := fun _ _ h => h

/-- `L` is multiplicative: `Lmul (A·B) = Lmul A · Lmul B`. -/
theorem Lmul_mul (A B : Matrix n n ℂ) : Lmul (A * B) = Lmul A * Lmul B := by
  ext X; apply toMat_injective
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc]

/-- `R` is anti-multiplicative: `Rmul (A·B) = Rmul B · Rmul A`. -/
theorem Rmul_mul (A B : Matrix n n ℂ) : Rmul (A * B) = Rmul B * Rmul A := by
  ext X; apply toMat_injective
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc]

/-- Left and right multiplications commute. -/
theorem Lmul_commute_Rmul (A B : Matrix n n ℂ) : Commute (Lmul A) (Rmul B) := by
  ext X; apply toMat_injective
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc]

/-- `Lmul` is unital. -/
@[simp] theorem Lmul_one : (Lmul (1 : Matrix n n ℂ) : HSMat n →L[ℂ] HSMat n) = 1 := by
  ext X; apply toMat_injective
  simp [ContinuousLinearMap.one_apply]

/-- `Rmul` is unital. -/
@[simp] theorem Rmul_one : (Rmul (1 : Matrix n n ℂ) : HSMat n →L[ℂ] HSMat n) = 1 := by
  ext X; apply toMat_injective
  simp [ContinuousLinearMap.one_apply]

end QIQTH.Araki
