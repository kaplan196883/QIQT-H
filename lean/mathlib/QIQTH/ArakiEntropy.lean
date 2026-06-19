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
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

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

/-! ### The Araki relative entropy and the Umegaki convention lock -/

/-- `⟪ξ, L_A ξ⟫_HS = tr(A · ξξᴴ)`. -/
theorem inner_ofMat_Lmul (s A : Matrix n n ℂ) :
    (inner ℂ (ofMat s) (Lmul A (ofMat s)) : ℂ) = (A * (s * sᴴ)).trace := by
  rw [hsInner_eq, Lmul_apply]; simp only [toMat_ofMat]; rw [Matrix.mul_assoc]

/-- `⟪ξ, R_A ξ⟫_HS = tr(ξ A ξᴴ)`. -/
theorem inner_ofMat_Rmul (s A : Matrix n n ℂ) :
    (inner ℂ (ofMat s) (Rmul A (ofMat s)) : ℂ) = (s * A * sᴴ).trace := by
  rw [hsInner_eq, Rmul_apply]; simp only [toMat_ofMat]

/-- **The (finite-dimensional) Araki relative entropy** `S(ρ‖σ) = −⟪ξ_ρ, log Δ_{σ|ρ} ξ_ρ⟩`,
    with the GNS vector `ξ_ρ = ρ^½` in the Hilbert–Schmidt representation. -/
noncomputable def arakiEntropy {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) : ℝ :=
  -(inner ℂ (ofMat (CFC.sqrt ρ)) ((CFC.log (relMod σ ρ)) (ofMat (CFC.sqrt ρ))) : ℂ).re

/-- **CONVENTION LOCK — the genuine Araki object reduces to Umegaki:**
    `S_Araki(ρ‖σ) = D(ρ‖σ) = tr(ρ(log ρ − log σ))`.  This is what certifies that the relative
    modular operator `Δ = L_σ R_ρ⁻¹` (σ numerator, ρ denominator) carries the correct convention. -/
theorem arakiEntropy_eq_relEntropy {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    arakiEntropy hρ hσ = relEntropy hρ.1 hσ.1 := by
  have hρ0 : (0 : Matrix n n ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ.posSemidef
  have hsq : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
  have hsH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian).eq
  have key : -(inner ℂ (ofMat (CFC.sqrt ρ)) ((CFC.log (relMod σ ρ)) (ofMat (CFC.sqrt ρ))) : ℂ)
      = (ρ * (matLog hρ.1 - matLog hσ.1)).trace := by
    rw [log_relMod hσ hρ, ContinuousLinearMap.sub_apply, inner_sub_right,
        inner_ofMat_Lmul, inner_ofMat_Rmul, hsH, hsq, Matrix.mul_sub, Matrix.trace_sub,
        Matrix.trace_mul_cycle (CFC.sqrt ρ) (matLog hρ.1), hsq,
        Matrix.trace_mul_comm ρ (matLog hρ.1), Matrix.trace_mul_comm ρ (matLog hσ.1)]
    ring
  unfold arakiEntropy relEntropy
  rw [← Complex.neg_re, key]

/-- **Non-negativity of the Araki relative entropy** (Klein, transported to the modular object):
    `S_Araki(ρ‖σ) ≥ 0` for normalized states. -/
theorem arakiEntropy_nonneg {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) : 0 ≤ arakiEntropy hρ hσ := by
  rw [arakiEntropy_eq_relEntropy]
  exact relEntropy_nonneg hρ hσ hρ1 hσ1

/-! ### The relative modular flow `Δ^{it}` (finite-dimensional Tomita–Takesaki) -/

section ModularFlow

variable {σ ρ : Matrix n n ℂ}

/-- The **relative modular generator** `K_{σ|ρ} = L_{log σ} − R_{log ρ}` (self-adjoint), i.e.
    `log Δ_{σ|ρ}` (cf. `log_relMod`); the modular flow is `exp(it·K)`. -/
noncomputable def relModGen (hσ : σ.PosDef) (hρ : ρ.PosDef) : HSMat n →L[ℂ] HSMat n :=
  Lmul (matLog hσ.1) - Rmul (matLog hρ.1)

theorem relModGen_isSelfAdjoint (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    IsSelfAdjoint (relModGen hσ hρ) :=
  (Lmul_isSelfAdjoint (matLog_isHermitian hσ.1)).sub (Rmul_isSelfAdjoint (matLog_isHermitian hρ.1))

/-- The **relative modular flow** `Δ_{σ|ρ}^{it} = exp(it · K_{σ|ρ})` — a one-parameter group of
    unitaries on Hilbert–Schmidt space, the finite-dimensional Tomita–Takesaki modular flow of the
    relative modular operator `Δ_{σ|ρ} = L_σ R_ρ⁻¹`. -/
noncomputable def relModFlow (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) : HSMat n →L[ℂ] HSMat n :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • relModGen hσ hρ)

@[simp] theorem relModFlow_zero (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    relModFlow hσ hρ 0 = 1 := by
  simp only [relModFlow, Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]

/-- **The Stone generator of the modular flow:** `d/dt Δ_{σ|ρ}^{it}|_{t=0} = i·K`, with `K = log Δ =
    relModGen` the (self-adjoint) modular Hamiltonian.  So the modular flow is the one-parameter
    unitary group generated by `i·log Δ` — its Stone generator is `i` times the modular Hamiltonian. -/
theorem hasDerivAt_relModFlow (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    HasDerivAt (fun t : ℝ => relModFlow hσ hρ t) (Complex.I • relModGen hσ hρ) 0 := by
  have hfun : (fun t : ℝ => relModFlow hσ hρ t)
      = fun t : ℝ => NormedSpace.exp (t • (Complex.I • relModGen hσ hρ)) := by
    funext t
    rw [relModFlow]
    congr 1
    rw [← smul_assoc, Complex.real_smul, mul_comm]
  rw [hfun]
  simpa using hasDerivAt_exp_smul_const (Complex.I • relModGen hσ hρ) (0 : ℝ)

/-- **The modular flow is a one-parameter group**: `Δ^{i(s+t)} = Δ^{is} · Δ^{it}`. -/
theorem relModFlow_add (hσ : σ.PosDef) (hρ : ρ.PosDef) (s t : ℝ) :
    relModFlow hσ hρ (s + t) = relModFlow hσ hρ s * relModFlow hσ hρ t := by
  have hc : Commute ((Complex.I * (s : ℂ)) • relModGen hσ hρ)
      ((Complex.I * (t : ℂ)) • relModGen hσ hρ) :=
    ((Commute.refl (relModGen hσ hρ)).smul_left _).smul_right _
  rw [relModFlow, relModFlow, relModFlow,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hc (mem_expBall_C _) (mem_expBall_C _),
    ← add_smul]
  congr 2
  push_cast; ring

/-- **The modular flow is unitary**: `Δ_{σ|ρ}^{it} ∈ U(HS)`. The generator `it·K` is skew-adjoint
    (real `t`, self-adjoint `K`), so its exponential lands in the unitary group. -/
theorem relModFlow_mem_unitary (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) :
    relModFlow hσ hρ t ∈ unitary (HSMat n →L[ℂ] HSMat n) := by
  have hskew : star ((Complex.I * (t : ℂ)) • relModGen hσ hρ)
      = -((Complex.I * (t : ℂ)) • relModGen hσ hρ) := by
    rw [star_smul, (relModGen_isSelfAdjoint hσ hρ).star_eq,
      show star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) by
        simp [Complex.conj_I, Complex.conj_ofReal], neg_smul]
  rw [relModFlow, Unitary.mem_iff, NormedSpace.star_exp, hskew]
  refine ⟨?_, ?_⟩
  · rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl _).neg_left) (mem_expBall_C _) (mem_expBall_C _),
      neg_add_cancel, NormedSpace.exp_zero]
  · rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl _).neg_right) (mem_expBall_C _) (mem_expBall_C _),
      add_neg_cancel, NormedSpace.exp_zero]

/-- **The concrete action of the modular flow** (the relative modular automorphism):
    `Δ_{σ|ρ}^{it} ξ = σ^{it} · ξ · ρ^{−it}`, with `σ^{it} = exp(it log σ)`, `ρ^{−it} = exp(−it log ρ)`.
    This is the Hilbert–Schmidt incarnation of the modular automorphism group; for `σ = ρ` it is the
    Connes cocycle's diagonal, `σ_t(A) = ρ^{it} A ρ^{-it}`. -/
theorem relModFlow_apply (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) (A : Matrix n n ℂ) :
    relModFlow hσ hρ t (ofMat A)
      = ofMat (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1) * A
          * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := by
  have hcomm : Commute (Lmul ((Complex.I * (t : ℂ)) • matLog hσ.1))
      (Rmul (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := Lmul_commute_Rmul _ _
  apply toMat_injective
  rw [relModFlow, relModGen, smul_sub, ← Lmul_smul, ← Rmul_smul, sub_eq_add_neg, ← Rmul_neg,
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm (mem_expBall_C _) (mem_expBall_C _),
    exp_Lmul, exp_Rmul, ContinuousLinearMap.mul_apply, Lmul_apply, Rmul_apply, toMat_ofMat,
    toMat_ofMat, Matrix.mul_assoc]

/-- **The modular flow fixes the GNS vector** — the defining Tomita–Takesaki property of the cyclic &
    separating vector: for the standard modular operator `Δ_ρ = Δ_{ρ|ρ}`, `Δ_ρ^{it} ξ_ρ = ξ_ρ` with the
    GNS vector `ξ_ρ = ρ^½`.  Equivalently, the state `ρ` is invariant under its own modular automorphism
    group (`ρ` is a KMS state for `σ_t`).  Since `Δ_ρ^{it}` acts by `ρ^{it}·ρ^½·ρ^{−it}` and `ρ^{it}`,
    `ρ^½` are commuting functions of `ρ`, the conjugation is trivial. -/
theorem relModFlow_fix_gns {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) :
    relModFlow hρ hρ t (ofMat (CFC.sqrt ρ)) = ofMat (CFC.sqrt ρ) := by
  have hsa : IsSelfAdjoint ρ := hρ.1
  have hρ0 : (0 : Matrix n n ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ.posSemidef
  have h0 : Commute ρ (CFC.sqrt ρ) := by
    have hsq : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ0
    nth_rewrite 1 [← hsq]
    exact (Commute.refl (CFC.sqrt ρ)).mul_left (Commute.refl (CFC.sqrt ρ))
  have hc : Commute (matLog hρ.1) (CFC.sqrt ρ) := by
    have hlog : matLog hρ.1 = cfc Real.log ρ := (hρ.1.cfc_eq Real.log).symm
    rw [hlog]
    exact hsa.commute_cfc h0 Real.log
  rw [relModFlow_apply]
  congr 1
  have hce : Commute (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)) (CFC.sqrt ρ) :=
    (hc.smul_left _).exp_left
  have hinv : NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)
      * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) = 1 := by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hρ.1)).neg_right)
      (mem_expBall_C ((Complex.I * (t : ℂ)) • matLog hρ.1))
      (mem_expBall_C (-((Complex.I * (t : ℂ)) • matLog hρ.1)))
    rw [add_neg_cancel, NormedSpace.exp_zero] at h
    exact h.symm
  rw [hce.eq, Matrix.mul_assoc, hinv, Matrix.mul_one]

/-- **The factored form of the modular flow**: `Δ_{σ|ρ}^{it} = L_{σ^{it}} · R_{ρ^{−it}}` on
    Hilbert–Schmidt space (left multiplication by `σ^{it}`, right multiplication by `ρ^{−it}`).
    Since the generator splits as `L_{log σ} − R_{log ρ}` with commuting `L`, `R` parts. -/
theorem relModFlow_eq_Lmul_Rmul (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) :
    relModFlow hσ hρ t
      = Lmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1))
        * Rmul (NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := by
  have hcomm : Commute (Lmul ((Complex.I * (t : ℂ)) • matLog hσ.1))
      (Rmul (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := Lmul_commute_Rmul _ _
  rw [relModFlow, relModGen, smul_sub, ← Lmul_smul, ← Rmul_smul, sub_eq_add_neg, ← Rmul_neg,
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm (mem_expBall_C _) (mem_expBall_C _),
    exp_Lmul, exp_Rmul]

/-- **Tomita's theorem (finite-dimensional, left algebra):** the modular flow maps the left
    multiplication algebra onto itself — `σ_t(L_A) = Δ^{it} L_A Δ^{−it} = L_{σ^{it} A σ^{−it}}`.  Acting
    on `ξ = ofMat Y` it sends `Y ↦ σ^{it}·(A·(σ^{−it} Y ρ^{it}))·ρ^{−it} = (σ^{it} A σ^{−it}) Y` because
    the `ρ`-factors cancel (`ρ^{it}ρ^{−it}=1`).  This is the modular automorphism `A ↦ σ^{it} A σ^{−it}`
    of the left algebra `L(Matrix)`. -/
theorem relModFlow_conj_Lmul (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) (A : Matrix n n ℂ) :
    relModFlow hσ hρ t * Lmul A * relModFlow hσ hρ (-t)
      = Lmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1) * A
          * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hσ.1))) := by
  have hLof : ∀ B M : Matrix n n ℂ, Lmul B (ofMat M) = ofMat (B * M) := fun B M =>
    toMat_injective (by rw [Lmul_apply, toMat_ofMat, toMat_ofMat])
  have hρinv : NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)
      * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) = 1 := by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hρ.1)).neg_right)
      (mem_expBall_C _) (mem_expBall_C _)
    rw [add_neg_cancel, NormedSpace.exp_zero] at h
    exact h.symm
  have key : ∀ Y : Matrix n n ℂ,
      (relModFlow hσ hρ t * Lmul A * relModFlow hσ hρ (-t)) (ofMat Y)
        = Lmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1) * A
            * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hσ.1))) (ofMat Y) := by
    intro Y
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      relModFlow_apply, hLof, relModFlow_apply, hLof,
      show (Complex.I * ((-t : ℝ) : ℂ)) • matLog hσ.1 = -((Complex.I * (t : ℂ)) • matLog hσ.1) by
        rw [Complex.ofReal_neg, mul_neg, neg_smul],
      show -((Complex.I * ((-t : ℝ) : ℂ)) • matLog hρ.1) = (Complex.I * (t : ℂ)) • matLog hρ.1 by
        rw [Complex.ofReal_neg, mul_neg, neg_smul, neg_neg]]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hρinv, Matrix.mul_one]
  ext X
  rw [← ofMat_toMat X]
  exact key (toMat X)

/-- **Tomita's theorem on the commutant (finite-dimensional, right algebra):** the modular flow also
    maps the *right* multiplication algebra (the commutant of `L(Matrix)`) onto itself —
    `σ_t(R_B) = Δ^{it} R_B Δ^{−it} = R_{ρ^{it} B ρ^{−it}}`.  Here the `σ`-factors cancel
    (`σ^{it}σ^{−it}=1`), leaving the `ρ`-inner automorphism `B ↦ ρ^{it} B ρ^{−it}`.  Together with
    `relModFlow_conj_Lmul` this is `σ_t(M)=M` and `σ_t(M')=M'`. -/
theorem relModFlow_conj_Rmul (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) (B : Matrix n n ℂ) :
    relModFlow hσ hρ t * Rmul B * relModFlow hσ hρ (-t)
      = Rmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * B
          * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := by
  have hRof : ∀ C M : Matrix n n ℂ, Rmul C (ofMat M) = ofMat (M * C) := fun C M =>
    toMat_injective (by rw [Rmul_apply, toMat_ofMat, toMat_ofMat])
  have hσinv : NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1)
      * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hσ.1)) = 1 := by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hσ.1)).neg_right)
      (mem_expBall_C _) (mem_expBall_C _)
    rw [add_neg_cancel, NormedSpace.exp_zero] at h
    exact h.symm
  have key : ∀ Y : Matrix n n ℂ,
      (relModFlow hσ hρ t * Rmul B * relModFlow hσ hρ (-t)) (ofMat Y)
        = Rmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * B
            * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) (ofMat Y) := by
    intro Y
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      relModFlow_apply, hRof, relModFlow_apply, hRof,
      show (Complex.I * ((-t : ℝ) : ℂ)) • matLog hσ.1 = -((Complex.I * (t : ℂ)) • matLog hσ.1) by
        rw [Complex.ofReal_neg, mul_neg, neg_smul],
      show -((Complex.I * ((-t : ℝ) : ℂ)) • matLog hρ.1) = (Complex.I * (t : ℂ)) • matLog hρ.1 by
        rw [Complex.ofReal_neg, mul_neg, neg_smul, neg_neg]]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, hσinv, Matrix.one_mul]
  ext X
  rw [← ofMat_toMat X]
  exact key (toMat X)

/-- **The Connes cocycle (finite-dimensional Radon–Nikodym derivative):**
    `(Dσ : Dρ)_t = Δ_{σ|ρ}^{it} · Δ_ρ^{−it} = L_{σ^{it} ρ^{−it}}` — the relative modular flow against the
    `ρ`-modular flow is left multiplication by the cocycle `u_t = σ^{it} ρ^{−it}`.  This is Connes'
    Radon–Nikodym derivative of the state `σ` with respect to `ρ`; the `ρ^{it}ρ^{−it}` right factors
    cancel, leaving an element of the left algebra. -/
theorem connesCocycle (hσ : σ.PosDef) (hρ : ρ.PosDef) (t : ℝ) :
    relModFlow hσ hρ t * relModFlow hρ hρ (-t)
      = Lmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1)
          * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) := by
  have hLof : ∀ B M : Matrix n n ℂ, Lmul B (ofMat M) = ofMat (B * M) := fun B M =>
    toMat_injective (by rw [Lmul_apply, toMat_ofMat, toMat_ofMat])
  have hρinv : NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)
      * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) = 1 := by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hρ.1)).neg_right)
      (mem_expBall_C _) (mem_expBall_C _)
    rw [add_neg_cancel, NormedSpace.exp_zero] at h
    exact h.symm
  have key : ∀ Y : Matrix n n ℂ,
      (relModFlow hσ hρ t * relModFlow hρ hρ (-t)) (ofMat Y)
        = Lmul (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hσ.1)
            * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))) (ofMat Y) := by
    intro Y
    rw [ContinuousLinearMap.mul_apply, relModFlow_apply, relModFlow_apply, hLof,
      show (Complex.I * ((-t : ℝ) : ℂ)) • matLog hρ.1 = -((Complex.I * (t : ℂ)) • matLog hρ.1) by
        rw [Complex.ofReal_neg, mul_neg, neg_smul], neg_neg]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hρinv, Matrix.mul_one]
  ext X
  rw [← ofMat_toMat X]
  exact key (toMat X)

/-- **The Connes cocycle chain rule (1-cocycle identity):** `u_{s+t} = u_s · σ_s(u_t)`, where
    `u_t = Δ_{σ|ρ}^{it} Δ_ρ^{−it}` (= `L_{σ^{it}ρ^{−it}}`, the cocycle operator, cf. `connesCocycle`) and
    `σ_s(·) = Δ_ρ^{is} · Δ_ρ^{−is}` is the `ρ`-modular flow.  This is what makes `t ↦ (Dσ:Dρ)_t` a genuine
    `σ`-cocycle.  Proof is pure one-parameter-group algebra: the inner `Δ_ρ^{−is}Δ_ρ^{is}` cancels and the
    remaining `Δ`'s combine by `relModFlow_add`. -/
theorem connesCocycle_chain (hσ : σ.PosDef) (hρ : ρ.PosDef) (s t : ℝ) :
    relModFlow hσ hρ (s + t) * relModFlow hρ hρ (-(s + t))
      = (relModFlow hσ hρ s * relModFlow hρ hρ (-s))
        * (relModFlow hρ hρ s * (relModFlow hσ hρ t * relModFlow hρ hρ (-t))
            * relModFlow hρ hρ (-s)) := by
  have hcancel : relModFlow hρ hρ (-s) * relModFlow hρ hρ s = 1 := by
    rw [← relModFlow_add, neg_add_cancel, relModFlow_zero]
  rw [relModFlow_add hσ hρ s t, show -(s + t) = (-t) + (-s) by ring, relModFlow_add hρ hρ (-t) (-s)]
  simp only [mul_assoc]
  rw [← mul_assoc (relModFlow hρ hρ (-s)) (relModFlow hρ hρ s), hcancel, one_mul]

/-! ### The modular conjugation `J` and `JMJ = M'` -/

/-- The **modular conjugation** `J : HSMat → HSMat`, `J(X) = X†` (conjugate transpose).  For the
    standard form on Hilbert–Schmidt space this is Tomita's antiunitary `J` — the polar part of the
    Tomita operator `S = J Δ^{1/2}`.  (It is conjugate-linear, so kept as a plain map.) -/
noncomputable def J (X : HSMat n) : HSMat n := ofMat ((toMat X)ᴴ)

@[simp] theorem toMat_J (X : HSMat n) : toMat (J X) = (toMat X)ᴴ := rfl

/-- `J` is an involution: `J² = id`. -/
theorem J_involutive (X : HSMat n) : J (J X) = X := by
  apply toMat_injective
  simp only [toMat_J, Matrix.conjTranspose_conjTranspose]

/-- **Tomita's `J M J = M'` (left → right):** `J L_A J = R_{A†}` — the modular conjugation maps the
    left multiplication algebra `M = L(Matrix)` onto its commutant `M' = R(Matrix)`. -/
theorem J_Lmul_J (A : Matrix n n ℂ) (X : HSMat n) : J (Lmul A (J X)) = Rmul Aᴴ X := by
  apply toMat_injective
  simp only [toMat_J, Lmul_apply, Rmul_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- **Tomita's `J M J = M'` (right → left):** `J R_B J = L_{B†}`. -/
theorem J_Rmul_J (B : Matrix n n ℂ) (X : HSMat n) : J (Rmul B (J X)) = Lmul Bᴴ X := by
  apply toMat_injective
  simp only [toMat_J, Lmul_apply, Rmul_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- `J` is **antiunitary**: `⟪J X, J Y⟫ = ⟪Y, X⟫` — it reverses the Hilbert–Schmidt inner product
    (an antilinear isometric involution). -/
theorem J_inner (X Y : HSMat n) : (inner ℂ (J X) (J Y) : ℂ) = inner ℂ Y X := by
  rw [hsInner_eq, hsInner_eq, toMat_J, toMat_J, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]

/-! ### The KMS condition -/

/-- **The KMS / modular condition (finite-dimensional, β = 1):** the faithful state `ω(X) = tr(ρ X)`
    satisfies the KMS condition for its own modular flow `σ_t(B) = ρ^{it} B ρ^{−it}`.  In finite
    dimensions `σ_z(B) = ρ^{iz} B ρ^{−iz}` is entire, and the KMS boundary relation
    `ω(A · σ_{−i}(B)) = ω(B · A)` holds with the imaginary-time value `σ_{−i}(B) = ρ B ρ^{−1}`.  This is
    the defining property singling out the modular flow (and `ρ` as its KMS/equilibrium state).  Pure
    trace cyclicity once `ρ^{−1}ρ = 1`. -/
theorem kms_condition (hρ : ρ.PosDef) (A B : Matrix n n ℂ) :
    (ρ * A * (ρ * B * ρ⁻¹)).trace = (ρ * B * A).trace := by
  have hinv : ρ⁻¹ * ρ = 1 :=
    Matrix.nonsing_inv_mul ρ ((Matrix.isUnit_iff_isUnit_det ρ).mp hρ.isUnit)
  rw [Matrix.trace_mul_cycle]
  congr 1
  rw [Matrix.mul_assoc (ρ * B) ρ⁻¹ ρ, hinv, Matrix.mul_one]

/-! ### The modular automorphism group `σ_t` on the matrix algebra -/

private theorem expIt_mul_expNegIt (hρ : ρ.PosDef) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)
      * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) = 1 := by
  have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hρ.1)).neg_right)
    (mem_expBall_C _) (mem_expBall_C _)
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h.symm

private theorem expNegIt_mul_expIt (hρ : ρ.PosDef) (t : ℝ) :
    NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))
      * NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) = 1 := by
  have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    ((Commute.refl ((Complex.I * (t : ℂ)) • matLog hρ.1)).neg_left)
    (mem_expBall_C _) (mem_expBall_C _)
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm

private theorem conjTranspose_expIt (hρ : ρ.PosDef) (t : ℝ) :
    (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1))ᴴ
      = NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) := by
  rw [← Matrix.star_eq_conjTranspose, NormedSpace.star_exp, star_smul,
    show star (matLog hρ.1) = matLog hρ.1 from
      (Matrix.star_eq_conjTranspose _).trans (matLog_isHermitian hρ.1),
    show star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) by
      simp [Complex.conj_I, Complex.conj_ofReal], neg_smul]

private theorem conjTranspose_expNegIt (hρ : ρ.PosDef) (t : ℝ) :
    (NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)))ᴴ
      = NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) := by
  rw [← conjTranspose_expIt hρ t, Matrix.conjTranspose_conjTranspose]

/-- The **modular automorphism** `σ_t(B) = ρ^{it} B ρ^{−it}` of the matrix algebra — the inner
    automorphism implementing the `ρ`-modular flow (cf. `relModFlow_conj_Lmul` with `σ = ρ`). -/
noncomputable def modAut (hρ : ρ.PosDef) (t : ℝ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * B
    * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))

/-- `σ_t` is **unital**: `σ_t(1) = 1`. -/
@[simp] theorem modAut_one (hρ : ρ.PosDef) (t : ℝ) : modAut hρ t 1 = 1 := by
  rw [modAut, Matrix.mul_one, expIt_mul_expNegIt hρ t]

/-- `σ_t` is **multiplicative**: `σ_t(BC) = σ_t(B) σ_t(C)`. -/
theorem modAut_mul (hρ : ρ.PosDef) (t : ℝ) (B C : Matrix n n ℂ) :
    modAut hρ t (B * C) = modAut hρ t B * modAut hρ t C := by
  simp only [modAut, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)))
    (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)), expNegIt_mul_expIt hρ t,
    Matrix.one_mul]

/-- `σ_t` is **`*`-preserving**: `σ_t(Bᴴ) = σ_t(B)ᴴ`. -/
theorem modAut_conjTranspose (hρ : ρ.PosDef) (t : ℝ) (B : Matrix n n ℂ) :
    modAut hρ t Bᴴ = (modAut hρ t B)ᴴ := by
  rw [modAut, modAut, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    conjTranspose_expNegIt hρ t, conjTranspose_expIt hρ t, Matrix.mul_assoc]

/-- `σ_0 = id`. -/
@[simp] theorem modAut_zero (hρ : ρ.PosDef) (B : Matrix n n ℂ) : modAut hρ 0 B = B := by
  simp only [modAut, Complex.ofReal_zero, mul_zero, zero_smul, neg_zero, NormedSpace.exp_zero,
    Matrix.one_mul, Matrix.mul_one]

/-- **The one-parameter group law**: `σ_{s+t} = σ_s ∘ σ_t`. -/
theorem modAut_add (hρ : ρ.PosDef) (s t : ℝ) (B : Matrix n n ℂ) :
    modAut hρ (s + t) B = modAut hρ s (modAut hρ t B) := by
  have hcomb : ∀ a b : ℂ, NormedSpace.exp (a • matLog hρ.1) * NormedSpace.exp (b • matLog hρ.1)
      = NormedSpace.exp ((a + b) • matLog hρ.1) := fun a b => by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      (((Commute.refl (matLog hρ.1)).smul_left a).smul_right b)
      (mem_expBall_C (a • matLog hρ.1)) (mem_expBall_C (b • matLog hρ.1))
    rw [← add_smul] at h
    exact h.symm
  have hfront : NormedSpace.exp ((Complex.I * (s : ℂ)) • matLog hρ.1)
      * NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)
      = NormedSpace.exp ((Complex.I * ((s + t : ℝ) : ℂ)) • matLog hρ.1) := by
    rw [hcomb, show Complex.I * (s : ℂ) + Complex.I * (t : ℂ) = Complex.I * ((s + t : ℝ) : ℂ) by
      push_cast; ring]
  have hback : NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1))
      * NormedSpace.exp (-((Complex.I * (s : ℂ)) • matLog hρ.1))
      = NormedSpace.exp (-((Complex.I * ((s + t : ℝ) : ℂ)) • matLog hρ.1)) := by
    rw [← neg_smul, ← neg_smul, hcomb,
      show -(Complex.I * (t : ℂ)) + -(Complex.I * (s : ℂ)) = -(Complex.I * ((s + t : ℝ) : ℂ)) by
        push_cast; ring, neg_smul]
  simp only [modAut, Matrix.mul_assoc]
  rw [hback, ← Matrix.mul_assoc (NormedSpace.exp ((Complex.I * (s : ℂ)) • matLog hρ.1)), hfront]

/-- **The modular flow fixes its equilibrium state:** `σ_t(ρ) = ρ` — `ρ` is invariant under its own
    modular automorphism group (the algebra-level statement of the KMS/equilibrium property,
    complementing `relModFlow_fix_gns` for the GNS vector and `kms_condition`).  Since `ρ` commutes
    with `ρ^{it}`, the conjugation is trivial. -/
@[simp] theorem modAut_fix (hρ : ρ.PosDef) (t : ℝ) : modAut hρ t ρ = ρ := by
  have hc : Commute (matLog hρ.1) ρ := by
    have hlog : matLog hρ.1 = cfc Real.log ρ := (hρ.1.cfc_eq Real.log).symm
    rw [hlog]
    exact (show IsSelfAdjoint ρ from hρ.1).commute_cfc (Commute.refl ρ) Real.log
  have hce : Commute (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)) ρ :=
    (hc.smul_left _).exp_left
  rw [modAut, hce.eq, Matrix.mul_assoc, expIt_mul_expNegIt hρ t, Matrix.mul_one]

/-- **The equilibrium state is `σ_t`-invariant:** `ω ∘ σ_t = ω`, i.e. `tr(ρ · σ_t(B)) = tr(ρ · B)` —
    the state `ω(·) = tr(ρ ·)` is stationary under its own modular flow (the functional-level KMS
    invariance, complementing `modAut_fix`'s `σ_t(ρ) = ρ`). -/
theorem modAut_state_invariant (hρ : ρ.PosDef) (t : ℝ) (B : Matrix n n ℂ) :
    (ρ * modAut hρ t B).trace = (ρ * B).trace := by
  have hc : Commute (matLog hρ.1) ρ := by
    have hlog : matLog hρ.1 = cfc Real.log ρ := (hρ.1.cfc_eq Real.log).symm
    rw [hlog]
    exact (show IsSelfAdjoint ρ from hρ.1).commute_cfc (Commute.refl ρ) Real.log
  have hce : Commute (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1)) ρ :=
    (hc.smul_left _).exp_left
  have hfix : NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) * ρ
      * NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) = ρ := by
    rw [Matrix.mul_assoc, ← hce.eq, ← Matrix.mul_assoc, expNegIt_mul_expIt hρ t, Matrix.one_mul]
  rw [modAut, show ρ * (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * B
        * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)))
      = (ρ * NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * B)
        * NormedSpace.exp (-((Complex.I * (t : ℂ)) • matLog hρ.1)) by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]

/-- **The relative entropy is the modular-Hamiltonian expectation:** `S(ρ‖σ) = −⟪ξ_ρ, K ξ_ρ⟫`, where
    `K = log Δ_{σ|ρ} = relModGen` is the generator of the modular flow (the "modular Hamiltonian") and
    `ξ_ρ = ρ^½` the GNS vector.  This is exactly the Araki definition, now phrased via the modular flow's
    generator — the bridge between the modular flow and the relative entropy (the basis of the
    entanglement "first law"). -/
theorem relEntropy_eq_neg_modGen (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1
      = -(inner ℂ (ofMat (CFC.sqrt ρ)) (relModGen hσ hρ (ofMat (CFC.sqrt ρ))) : ℂ).re := by
  rw [← arakiEntropy_eq_relEntropy hρ hσ]
  unfold arakiEntropy relModGen
  rw [log_relMod hσ hρ]

/-- **The first-law decomposition:** `S(ρ‖σ) + S(ρ) = ⟪K_σ⟫_ρ`, where `S(ρ)` is the von Neumann
    entropy, `K_σ = −log σ` is the modular Hamiltonian of `σ`, and `⟪K_σ⟫_ρ = tr(ρ K_σ) =
    −tr(ρ log σ)`.  Equivalently `S(ρ‖σ) = Δ⟪K_σ⟫ − ΔS` (modular energy change minus entropy change);
    positivity of `S(ρ‖σ)` then yields the **first-law inequality** `ΔS ≤ Δ⟪K⟫`, saturated (the
    first law `δS = δ⟪K⟫`) to first order since `S(ρ‖σ)` is second-order in `ρ − σ`. -/
theorem relEntropy_add_vonNeumann (hσ : σ.PosDef) (hρ : ρ.PosDef)
    (hd : QIQTH.QuantumEntropy.IsDensity ρ) :
    QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1 + QIQTH.QuantumEntropy.vonNeumannEntropy hd
      = -(ρ * matLog hσ.1).trace.re := by
  rw [QIQTH.QuantumEntropy.relEntropy, QIQTH.QuantumEntropy.vonNeumannEntropy_eq_neg_trace hρ hd,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

/-- **The first-law inequality:** `S(ρ) ≤ ⟪K_σ⟫_ρ` — the von Neumann entropy is bounded by the modular
    energy `tr(ρ K_σ) = −tr(ρ log σ)`, with equality iff `ρ = σ`.  Immediate from the decomposition
    `S(ρ‖σ) + S(ρ) = ⟪K_σ⟫_ρ` and the positivity of the relative entropy (Klein). -/
theorem vonNeumann_le_modEnergy (hσ : σ.PosDef) (hρ : ρ.PosDef)
    (hd : QIQTH.QuantumEntropy.IsDensity ρ) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    QIQTH.QuantumEntropy.vonNeumannEntropy hd ≤ -(ρ * matLog hσ.1).trace.re := by
  have h := relEntropy_add_vonNeumann hσ hρ hd
  have hpos := QIQTH.QuantumEntropy.relEntropy_nonneg hρ hσ hρ1 hσ1
  linarith

/-- **First-law rigidity:** the first-law inequality `S(ρ) ≤ ⟪K_σ⟫_ρ` is **saturated iff `ρ = σ`** —
    equality of entropy and modular energy holds exactly at the equilibrium state.  Immediate from the
    decomposition `S(ρ‖σ) + S(ρ) = ⟪K_σ⟫_ρ` and the faithfulness of the relative entropy
    (`relEntropy = 0 ⟺ ρ = σ`). -/
theorem firstLaw_saturation (hσ : σ.PosDef) (hρ : ρ.PosDef)
    (hd : QIQTH.QuantumEntropy.IsDensity ρ) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1)
    (hsat : QIQTH.QuantumEntropy.vonNeumannEntropy hd = -(ρ * matLog hσ.1).trace.re) : ρ = σ := by
  have h := relEntropy_add_vonNeumann hσ hρ hd
  rw [hsat] at h
  exact QIQTH.QuantumEntropy.relEntropy_eq_zero hρ hσ hρ1 hσ1 (by linarith)

end ModularFlow

end QIQTH.Araki
