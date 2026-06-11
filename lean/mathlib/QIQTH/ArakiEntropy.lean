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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace QIQTH.Araki

open QIQTH.QuantumEntropy Unitary
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

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

instance : CompleteSpace (HSMat n) := FiniteDimensional.complete ℂ (HSMat n)

/-- The identification of `HSMat n` with `Matrix n n ℂ` (definitional). -/
def toMat (X : HSMat n) : Matrix n n ℂ := X

/-- The identification of `Matrix n n ℂ` with `HSMat n` (definitional). -/
def ofMat (X : Matrix n n ℂ) : HSMat n := X

@[simp] theorem toMat_ofMat (X : Matrix n n ℂ) : toMat (ofMat X) = X := rfl
@[simp] theorem ofMat_toMat (X : HSMat n) : ofMat (toMat X) = X := rfl
@[simp] theorem toMat_zero : toMat (0 : HSMat n) = 0 := rfl
@[simp] theorem toMat_neg (x : HSMat n) : toMat (-x) = -toMat x := rfl

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

/-- **Adjoint of `Lmul`:** `(Lmul A)⋆ = Lmul Aᴴ` (w.r.t. the HS inner product). -/
theorem Lmul_adjoint (A : Matrix n n ℂ) :
    ContinuousLinearMap.adjoint (Lmul A) = Lmul Aᴴ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [hsInner_eq, hsInner_eq, Lmul_apply, Lmul_apply, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]

/-- **Adjoint of `Rmul`:** `(Rmul A)⋆ = Rmul Aᴴ`. -/
theorem Rmul_adjoint (A : Matrix n n ℂ) :
    ContinuousLinearMap.adjoint (Rmul A) = Rmul Aᴴ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [hsInner_eq, hsInner_eq, Rmul_apply, Rmul_apply, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-! ### `L`/`R` as algebra homomorphisms, and exponential naturality

  To compute `log(L_σ R_ρ⁻¹)` we need `exp` to commute with `Lmul`/`Rmul`.  `Lmul` is a unital
  algebra hom; `Rmul` is *anti*-multiplicative, so it is a hom out of the opposite algebra.  Both
  are continuous (finite dimension), so `map_exp` gives the naturality. -/

@[simp] theorem toMat_add (x y : HSMat n) : toMat (x + y) = toMat x + toMat y := rfl
@[simp] theorem toMat_smul (c : ℂ) (x : HSMat n) : toMat (c • x) = c • toMat x := rfl

theorem Lmul_add (A B : Matrix n n ℂ) : Lmul (A + B) = Lmul A + Lmul B := by
  ext X; apply toMat_injective; simp [ContinuousLinearMap.add_apply, Matrix.add_mul]

theorem Lmul_smul (c : ℂ) (A : Matrix n n ℂ) : Lmul (c • A) = c • Lmul A := by
  ext X; apply toMat_injective; simp [ContinuousLinearMap.smul_apply, smul_mul_assoc]

theorem Rmul_add (A B : Matrix n n ℂ) : Rmul (A + B) = Rmul A + Rmul B := by
  ext X; apply toMat_injective; simp [ContinuousLinearMap.add_apply, Matrix.mul_add]

theorem Rmul_neg (A : Matrix n n ℂ) : Rmul (-A) = -Rmul A := by
  ext X; apply toMat_injective; simp [ContinuousLinearMap.neg_apply, Matrix.mul_neg]

theorem Rmul_smul (c : ℂ) (A : Matrix n n ℂ) : Rmul (c • A) = c • Rmul A := by
  ext X; apply toMat_injective; simp [ContinuousLinearMap.smul_apply, mul_smul_comm]

/-- `Lmul` bundled as a unital ℂ-algebra homomorphism `Matrix → 𝓛(HS)`. -/
noncomputable def Lmulₐ : Matrix n n ℂ →ₐ[ℂ] (HSMat n →L[ℂ] HSMat n) where
  toFun := Lmul
  map_one' := Lmul_one
  map_mul' := Lmul_mul
  map_zero' := by ext X; apply toMat_injective; simp
  map_add' := Lmul_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Lmul_smul, Lmul_one]

/-- `Rmul` bundled as a unital ℂ-algebra homomorphism out of the *opposite* algebra
    (`Rmul` is anti-multiplicative). -/
noncomputable def Rmulₐ : (Matrix n n ℂ)ᵐᵒᵖ →ₐ[ℂ] (HSMat n →L[ℂ] HSMat n) where
  toFun A := Rmul A.unop
  map_one' := Rmul_one
  map_mul' x y := by rw [MulOpposite.unop_mul, Rmul_mul]
  map_zero' := by ext X; apply toMat_injective; simp
  map_add' x y := by rw [MulOpposite.unop_add, Rmul_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, MulOpposite.unop_smul,
        MulOpposite.unop_one, Rmul_smul, Rmul_one]

theorem Lmulₐ_continuous : Continuous (Lmulₐ : Matrix n n ℂ → (HSMat n →L[ℂ] HSMat n)) := by
  have h : Continuous (Lmulₐ (n := n)).toLinearMap := LinearMap.continuous_of_finiteDimensional _
  exact h

theorem Rmulₐ_continuous :
    Continuous (Rmulₐ : (Matrix n n ℂ)ᵐᵒᵖ → (HSMat n →L[ℂ] HSMat n)) := by
  have h : Continuous (Rmulₐ (n := n)).toLinearMap := LinearMap.continuous_of_finiteDimensional _
  exact h

/-- Every point lies in the exp-convergence ball of a complex Banach algebra (radius `∞`). -/
private theorem mem_expBall_C {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (x : 𝔸) : x ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℂ 𝔸).radius :=
  (NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _

/-- **Exponential naturality for `Lmul`:** `exp(L_A) = L_{exp A}`. -/
theorem exp_Lmul (A : Matrix n n ℂ) :
    NormedSpace.exp (Lmul A) = Lmul (NormedSpace.exp A) :=
  (NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) Lmulₐ Lmulₐ_continuous A (mem_expBall_C A)).symm

/-- **Exponential naturality for `Rmul`:** `exp(R_A) = R_{exp A}` (via the opposite algebra). -/
theorem exp_Rmul (A : Matrix n n ℂ) :
    NormedSpace.exp (Rmul A) = Rmul (NormedSpace.exp A) := by
  have h := (NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) Rmulₐ Rmulₐ_continuous (MulOpposite.op A)
    (mem_expBall_C (MulOpposite.op A))).symm
  rw [NormedSpace.exp_op] at h
  exact h

/-! ### The relative modular operator `Δ = L_σ R_ρ⁻¹` -/

/-- **The (finite-dim) relative modular operator** `Δ_{σ|ρ} = L_σ · R_ρ⁻¹` on Hilbert–Schmidt space —
    `σ` in the numerator, `ρ` in the denominator (the convention giving Umegaki with the `−` sign). -/
noncomputable def relMod (σ ρ : Matrix n n ℂ) : HSMat n →L[ℂ] HSMat n :=
  Lmul σ * Rmul ρ⁻¹

/-- `Δ_{σ|ρ}` is self-adjoint for Hermitian `σ, ρ`. -/
theorem relMod_isSelfAdjoint {σ ρ : Matrix n n ℂ} (hσ : σ.IsHermitian) (hρ : ρ.IsHermitian) :
    IsSelfAdjoint (relMod σ ρ) := by
  show star (relMod σ ρ) = relMod σ ρ
  rw [relMod, star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      Lmul_adjoint, Rmul_adjoint, hσ.eq, Matrix.conjTranspose_nonsing_inv, hρ.eq]
  exact (Lmul_commute_Rmul σ ρ⁻¹).symm.eq

/-! ### The operator logarithm identity `log Δ = L_{log σ} − R_{log ρ}`

  The crux of the finite Umegaki reduction.  We prove it via the operator exponential:
  `Δ_{σ|ρ} = exp(L_{log σ} − R_{log ρ})`, then apply `CFC.log_exp`.  The matrix fact
  `exp(matLog A) = A` is proved through the EIGENVALUE functional calculus (`matLog_UDU` +
  `Matrix.exp_conj`/`exp_diagonal`), NOT the general `cfc` — this deliberately avoids the
  L2-operator-norm-vs-eigenvalue-CFC instance clash on `Matrix n n ℂ`. -/

/-- `matLog` of a Hermitian matrix is Hermitian (it is `U · diag(real) · Uᴴ`). -/
theorem matLog_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) : (matLog hA).IsHermitian := by
  have hDherm : (Matrix.diagonal (fun j => (Real.log (hA.eigenvalues j) : ℂ)))ᴴ
      = Matrix.diagonal (fun j => (Real.log (hA.eigenvalues j) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; funext j; simp
  rw [Matrix.IsHermitian, matLog_UDU hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDherm]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, mul_assoc]

/-- `L_H` is self-adjoint for Hermitian `H`. -/
theorem Lmul_isSelfAdjoint {H : Matrix n n ℂ} (hH : H.IsHermitian) : IsSelfAdjoint (Lmul H) := by
  show star (Lmul H) = Lmul H
  rw [ContinuousLinearMap.star_eq_adjoint, Lmul_adjoint, hH.eq]

/-- `R_H` is self-adjoint for Hermitian `H`. -/
theorem Rmul_isSelfAdjoint {H : Matrix n n ℂ} (hH : H.IsHermitian) : IsSelfAdjoint (Rmul H) := by
  show star (Rmul H) = Rmul H
  rw [ContinuousLinearMap.star_eq_adjoint, Rmul_adjoint, hH.eq]

/-- **`exp(log A) = A` at the matrix level** for positive-definite `A`, via the eigenvalue
    functional calculus (`exp(U·diag(log λ)·Uᴴ) = U·diag(λ)·Uᴴ = A`). -/
theorem exp_matLog {A : Matrix n n ℂ} (hA : A.PosDef) :
    NormedSpace.exp (matLog hA.1) = A := by
  have hsmul : star (hA.1.eigenvectorUnitary : Matrix n n ℂ)
      * (hA.1.eigenvectorUnitary : Matrix n n ℂ) = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hms : (hA.1.eigenvectorUnitary : Matrix n n ℂ)
      * star (hA.1.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hA.1.eigenvectorUnitary).2
  have hcoe : star (hA.1.eigenvectorUnitary : Matrix n n ℂ)
      = (hA.1.eigenvectorUnitary : Matrix n n ℂ)⁻¹ := (Matrix.inv_eq_left_inv hsmul).symm
  have hunit : IsUnit (hA.1.eigenvectorUnitary : Matrix n n ℂ) := ⟨⟨_, _, hms, hsmul⟩, rfl⟩
  have hD : NormedSpace.exp (fun j => (Real.log (hA.1.eigenvalues j) : ℂ))
      = RCLike.ofReal ∘ hA.1.eigenvalues := by
    rw [Pi.exp_def]; funext j
    simp only [Function.comp_apply]
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_log (hA.eigenvalues_pos j)]
    rfl
  rw [matLog_UDU hA.1, hcoe, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, hD]
  conv_rhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, hcoe]

/-- **The relative modular operator is an honest operator exponential:**
    `Δ_{σ|ρ} = exp(L_{log σ} − R_{log ρ})`. -/
theorem relMod_eq_exp {σ ρ : Matrix n n ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    relMod σ ρ = NormedSpace.exp (Lmul (matLog hσ.1) - Rmul (matLog hρ.1)) := by
  have hinvρ : NormedSpace.exp (-matLog hρ.1) = ρ⁻¹ := by
    have hsum : NormedSpace.exp (-matLog hρ.1) * NormedSpace.exp (matLog hρ.1) = 1 := by
      have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
        ((Commute.refl (matLog hρ.1)).neg_left)
        (mem_expBall_C (-matLog hρ.1)) (mem_expBall_C (matLog hρ.1))
      rw [neg_add_cancel, NormedSpace.exp_zero] at h
      exact h.symm
    rw [exp_matLog hρ] at hsum
    exact (Matrix.inv_eq_left_inv hsum).symm
  have hcomm : Commute (Lmul (matLog hσ.1)) (-(Rmul (matLog hρ.1))) :=
    (Lmul_commute_Rmul (matLog hσ.1) (matLog hρ.1)).neg_right
  rw [relMod, sub_eq_add_neg,
      NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm (mem_expBall_C _) (mem_expBall_C _),
      exp_Lmul, exp_matLog hσ, ← Rmul_neg, exp_Rmul, hinvρ]

/-- **The operator logarithm identity** (finite-dimensional core of Araki's relative entropy):
    `log Δ_{σ|ρ} = L_{log σ} − R_{log ρ}`.  This is what makes `−⟪ξ_ρ, log Δ ξ_ρ⟩` reduce to Umegaki. -/
theorem log_relMod {σ ρ : Matrix n n ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    CFC.log (relMod σ ρ) = Lmul (matLog hσ.1) - Rmul (matLog hρ.1) := by
  have hBsa : IsSelfAdjoint (Lmul (matLog hσ.1) - Rmul (matLog hρ.1)) :=
    (Lmul_isSelfAdjoint (matLog_isHermitian hσ.1)).sub (Rmul_isSelfAdjoint (matLog_isHermitian hρ.1))
  rw [relMod_eq_exp hσ hρ, CFC.log_exp _ hBsa]

end QIQTH.Araki
