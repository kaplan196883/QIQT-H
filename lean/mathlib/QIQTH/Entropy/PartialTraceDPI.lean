import QIQTH.Entropy.WeylDesign
import QIQTH.Entropy.PartialTrace
import QIQTH.Entropy.RelEntropyDPI
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Toward partial-trace data processing: the factor-2 Weyl twirl

The complete single-factor depolarization is machine-checked in `WeylDesign.lean`
(`weyl_depolarization_flat`: `Σ_{a,b} (1/m²)·W_{a,b} M W_{a,b}⋆ = (Tr M/m)·I`). The remaining route to
**partial-trace data processing** `D(Tr₂ρ ‖ Tr₂σ) ≤ D(ρ‖σ)` (Carlen §5.7) is:

1. lift the Weyl twirl to the **second tensor factor** — conjugating `ρ : Matrix (n×m)` by the unitaries
   `I_n ⊗ W_{a,b}` and averaging gives `(Tr₂ρ) ⊗ (I_m/m)` (a complete depolarization of factor 2,
   blockwise `weyl_depolarization_flat`);
2. that twirl is **mixed-unitary** (the `I_n ⊗ W_{a,b}` are unitary), so `dpi_mixed_unitary` gives
   `D((Tr₂ρ)⊗(I/m) ‖ (Tr₂σ)⊗(I/m)) ≤ D(ρ‖σ)`;
3. relative-entropy **⊗-additivity** `D(A⊗(I/m) ‖ B⊗(I/m)) = D(A‖B)` closes it.

This file starts that phase. First brick: `I_n ⊗ W` is unitary whenever `W` is — the conjugating
unitaries of the factor-2 twirl. Axiom-free.
-/

namespace QIQTH.Entropy

open Matrix
open scoped Kronecker ComplexOrder

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **`I_n ⊗ W` is unitary when `W` is** — the conjugating unitaries of the factor-2 Weyl twirl. By the
Kronecker mixed-product property `(I ⊗ W)⋆(I ⊗ W) = (I⋆I) ⊗ (W⋆W) = I ⊗ I = I`. -/
theorem one_kron_mem_unitary {W : Matrix m m ℂ} (hW : W ∈ unitary (Matrix m m ℂ)) :
    (1 : Matrix n n ℂ) ⊗ₖ W ∈ unitary (Matrix (n × m) (n × m) ℂ) := by
  rw [Unitary.mem_iff] at hW ⊢
  obtain ⟨hW1, hW2⟩ := hW
  rw [star_eq_conjTranspose] at hW1 hW2
  refine ⟨?_, ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW1, one_kronecker_one]
  · rw [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, hW2, one_kronecker_one]

/-- The `(i,j)`-block of `ρ : Matrix (n×m)` — the `m×m` matrix `c,d ↦ ρ_{(i,c)(j,d)}`. -/
def block (ρ : Matrix (n × m) (n × m) ℂ) (i j : n) : Matrix m m ℂ :=
  Matrix.of fun c d => ρ (i, c) (j, d)

/-- **`I_n ⊗ W` conjugation acts blockwise**: the `(i,a')(j,b')` entry of `(I⊗W) ρ (I⊗W)⋆` equals the
`(a',b')` entry of `W · (block i j of ρ) · W⋆`. (The identity on factor 1 just selects the `(i,j)`-block;
`W` conjugates it on factor 2.) This is what reduces the factor-2 Weyl twirl to the single-factor
`weyl_depolarization_flat` applied to each block. -/
theorem kron_conj_block (W : Matrix m m ℂ) (ρ : Matrix (n × m) (n × m) ℂ) (i j : n) (a' b' : m) :
    (((1 : Matrix n n ℂ) ⊗ₖ W) * ρ * ((1 : Matrix n n ℂ) ⊗ₖ W)ᴴ) (i, a') (j, b')
      = (W * block ρ i j * Wᴴ) a' b' := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kronecker_apply, Matrix.one_apply, block,
    Matrix.of_apply, conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, one_mul]

/-- **The factor-2 Weyl twirl is the complete depolarization of the second tensor factor**:
`Σ_{a,b} (1/M²)·(I⊗W_{a,b}) ρ (I⊗W_{a,b})⋆ = (Tr₂ρ) ⊗ (I_M/M)`. Conjugating `ρ` by the factor-2 Weyl
unitaries `I_n⊗W_{a,b}` and averaging acts blockwise (`kron_conj_block`): each `(i,j)`-block is
completely depolarized by the single-factor Weyl 1-design (`weyl_depolarization_flat`) to
`(Tr(blockᵢⱼρ)/M)·I = ((Tr₂ρ)ᵢⱼ/M)·I`. This is exactly `(Tr₂ρ)⊗(I/M)`. The twirl is mixed-unitary
(`one_kron_mem_unitary`), so `dpi_mixed_unitary` then yields partial-trace data processing. Axiom-free. -/
theorem factor2_depolarization {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (ρ : Matrix (n × Fin N) (n × Fin N) ℂ) :
    ∑ a : Fin N, ∑ b : Fin N, ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) •
        (((1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val)) * ρ
          * ((1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val))ᴴ)
      = partialTraceRight ρ ⊗ₖ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  ext ⟨i, a'⟩ ⟨j, b'⟩
  have key : (∑ a : Fin N, ∑ b : Fin N, ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) •
        (((1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val)) * ρ
          * ((1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val))ᴴ))
            (i, a') (j, b')
      = (∑ a : Fin N, ∑ b : Fin N, ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) •
          ((((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val) * block ρ i j
            * (((finRotate N) ^ a.val).permMatrix ℂ * (clock ω N) ^ b.val)ᴴ)) a' b' := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, kron_conj_block]
  rw [key, weyl_depolarization_flat hω (block ρ i j)]
  simp only [kronecker_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [show (block ρ i j).trace = partialTraceRight ρ i j from rfl]
  ring

/-! ## Relative-entropy ⊗-additivity (maximally-mixed second factor) -/

/-- `A ↦ A ⊗ₖ 1_p` as a unital ⋆-algebra homomorphism `Matrix n n ℂ →⋆ₐ Matrix (n×p)(n×p) ℂ`, for a
general second factor `p` (the two-type generalization of `TensorPower.kroneckerRightHom`). -/
@[simps]
noncomputable def kronRightHom (n p : Type*) [Fintype n] [DecidableEq n] [Fintype p]
    [DecidableEq p] : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × p) (n × p) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix p p ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := zero_kronecker 1
  map_add' A B := add_kronecker A B 1
  commutes' r := by simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma continuous_kronRightHom :
    Continuous (kronRightHom n m : Matrix n n ℂ → Matrix (n × m) (n × m) ℂ) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kronRightHom_apply, Matrix.kroneckerMap_apply]
  exact (continuous_id.matrix_elem i₁ j₁).mul continuous_const

/-- **The matrix logarithm of `A ⊗ 1` factors**: `log(A ⊗ 1_m) = (log A) ⊗ 1_m`. CFC naturality
(`map_cfc`) under the ⋆-algebra hom `kronRightHom` — the same pattern as `matLog_conj` for unitary
conjugation. -/
lemma matLog_kron_one {A : Matrix n n ℂ} (hA : A.PosDef)
    (h : (A ⊗ₖ (1 : Matrix m m ℂ)).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h = (QIQTH.QuantumEntropy.matLog hA.1) ⊗ₖ (1 : Matrix m m ℂ) := by
  unfold QIQTH.QuantumEntropy.matLog
  have hf : ContinuousOn Real.log (spectrum ℝ A) :=
    QIQTH.QuantumEntropy.continuousOn_log_spectrum hA
  rw [← h.cfc_eq Real.log, show (A ⊗ₖ (1 : Matrix m m ℂ)) = kronRightHom n m A from rfl,
    ← StarAlgHomClass.map_cfc (kronRightHom n m) Real.log A hf continuous_kronRightHom (ha := hA.1),
    kronRightHom_apply]
  exact congrArg (· ⊗ₖ (1 : Matrix m m ℂ)) (hA.1.cfc_eq Real.log)

/-- **Relative-entropy ⊗-additivity with a scalar identity second factor**:
`D(A ⊗ (c·1_m) ‖ B ⊗ (c·1_m)) = (c·dim m)·D(A‖B)`. The `c·1` factor is common to both arguments, so its
`log` cancels in `log ρ − log σ = (log A − log B)⊗1` (`matLog_smul` + `matLog_kron_one`); the trace then
factors as `Tr((A(logA−logB))⊗(c·1)) = Tr(A(logA−logB))·(c·dim m)` (`trace_kronecker`). For the
maximally-mixed factor `c = 1/dim m` this is just `D(A‖B)`. -/
theorem relEntropy_kron_one {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (hc : 0 < c)
    (hAC : (c • (A ⊗ₖ (1 : Matrix m m ℂ))).IsHermitian)
    (hBC : (c • (B ⊗ₖ (1 : Matrix m m ℂ))).IsHermitian) :
    QIQTH.QuantumEntropy.relEntropy hAC hBC
      = (c * (Fintype.card m : ℝ)) * QIQTH.QuantumEntropy.relEntropy hA.1 hB.1 := by
  have hA1 : (A ⊗ₖ (1 : Matrix m m ℂ)).PosDef := hA.kronecker Matrix.PosDef.one
  have hB1 : (B ⊗ₖ (1 : Matrix m m ℂ)).PosDef := hB.kronecker Matrix.PosDef.one
  have hdiff : QIQTH.QuantumEntropy.matLog hAC - QIQTH.QuantumEntropy.matLog hBC
      = (QIQTH.QuantumEntropy.matLog hA.1 - QIQTH.QuantumEntropy.matLog hB.1)
        ⊗ₖ (1 : Matrix m m ℂ) := by
    rw [matLog_smul hA1 hc hAC, matLog_smul hB1 hc hBC, matLog_kron_one hA, matLog_kron_one hB]
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, kronecker_apply, smul_eq_mul]
    ring
  unfold QIQTH.QuantumEntropy.relEntropy
  rw [hdiff, Matrix.smul_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.trace_smul,
    trace_kronecker, Matrix.trace_one, Complex.smul_re]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  ring

/-- Any permutation matrix is unitary. -/
theorem perm_mem_unitary {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    σ.permMatrix ℂ ∈ unitary (Matrix (Fin N) (Fin N) ℂ) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_permMatrix]
  refine ⟨?_, ?_⟩ <;> simp [← permMatrix_mul, permMatrix_one]


lemma isHermitian_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  show (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [conjTranspose_kronecker, hA, hB]

lemma isHermitian_invNat_smul {p : Type*} [Fintype p] {M : Matrix p p ℂ} (hM : M.IsHermitian)
    {N : ℕ} : ((N : ℂ)⁻¹ • M).IsHermitian := by
  show ((N : ℂ)⁻¹ • M)ᴴ = (N : ℂ)⁻¹ • M
  rw [conjTranspose_smul, star_inv₀, star_natCast, hM]

noncomputable def weylU {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N) (k : Fin N × Fin N) :
    unitary (Matrix (n × Fin N) (n × Fin N) ℂ) :=
  ⟨(1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ k.1.val).permMatrix ℂ * (clock ω N) ^ k.2.val),
    one_kron_mem_unitary (mul_mem (perm_mem_unitary _) (pow_mem (clock_mem_unitary hω) _))⟩

@[simp] lemma weylU_coe {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N) (k : Fin N × Fin N) :
    (weylU (n := n) hω k : Matrix (n × Fin N) (n × Fin N) ℂ)
      = (1 : Matrix n n ℂ) ⊗ₖ (((finRotate N) ^ k.1.val).permMatrix ℂ * (clock ω N) ^ k.2.val) := rfl

lemma realCast_smul {α : Type*} [Fintype α] [DecidableEq α] (r : ℝ) (M : Matrix α α ℂ) :
    (r : ℝ) • M = (↑r : ℂ) • M := by
  rw [← algebraMap_smul (A := ℂ) r M, Complex.coe_algebraMap]

lemma isHermitian_real_smul {α : Type*} [Fintype α] {M : Matrix α α ℂ} (hM : M.IsHermitian)
    (c : ℝ) : ((c : ℝ) • M).IsHermitian := by
  show ((c : ℝ) • M)ᴴ = (c : ℝ) • M
  rw [conjTranspose_smul, star_trivial, hM]


/-- # PARTIAL-TRACE DATA PROCESSING — `D(Tr₂ρ ‖ Tr₂σ) ≤ D(ρ‖σ)` (Carlen §6.4 + §5.7). Axiom-free. -/
theorem partial_trace_dpi {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    {ρ σ : Matrix (n × Fin N) (n × Fin N) ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    QIQTH.QuantumEntropy.relEntropy (partialTraceRight_posDef hρ).1
        (partialTraceRight_posDef hσ).1
      ≤ QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1 := by
  have hsc : ∀ X : Matrix (n × Fin N) (n × Fin N) ℂ,
      ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ : ℝ) • X = ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • X := by
    intro X
    rw [← algebraMap_smul (A := ℂ) ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) X]
    congr 1
    rw [Complex.coe_algebraMap]
    push_cast
    ring
  have hchan : ∀ τ : Matrix (n × Fin N) (n × Fin N) ℂ,
      (∑ k ∈ (Finset.univ : Finset (Fin N × Fin N)), ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ : ℝ) •
          ((weylU (n := n) hω k : Matrix (n × Fin N) (n × Fin N) ℂ) * τ
            * (star (weylU (n := n) hω k) : Matrix (n × Fin N) (n × Fin N) ℂ)))
        = partialTraceRight τ ⊗ₖ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    intro τ
    simp only [Unitary.coe_star, weylU_coe, star_eq_conjTranspose]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [hsc]
    exact factor2_depolarization hω τ
  have hkron : ∀ τ : Matrix (n × Fin N) (n × Fin N) ℂ, τ.IsHermitian →
      (partialTraceRight τ ⊗ₖ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ))).IsHermitian :=
    fun τ hτ => isHermitian_kronecker (partialTraceRight_isHermitian hτ)
      (isHermitian_invNat_smul Matrix.isHermitian_one)
  have hΦρ : (∑ k ∈ (Finset.univ : Finset (Fin N × Fin N)), ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ : ℝ) •
      ((weylU (n := n) hω k : Matrix (n × Fin N) (n × Fin N) ℂ) * ρ
        * (star (weylU (n := n) hω k) : Matrix (n × Fin N) (n × Fin N) ℂ))).IsHermitian := by
    rw [hchan ρ]; exact hkron ρ hρ.1
  have hΦσ : (∑ k ∈ (Finset.univ : Finset (Fin N × Fin N)), ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ : ℝ) •
      ((weylU (n := n) hω k : Matrix (n × Fin N) (n × Fin N) ℂ) * σ
        * (star (weylU (n := n) hω k) : Matrix (n × Fin N) (n × Fin N) ℂ))).IsHermitian := by
    rw [hchan σ]; exact hkron σ hσ.1
  have hNpos : (0:ℝ) < (N:ℝ)⁻¹ := by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hsum1 : ∑ _k ∈ (Finset.univ : Finset (Fin N × Fin N)), ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    have hN : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    push_cast; field_simp
  have hdpi := dpi_mixed_unitary (s := (Finset.univ : Finset (Fin N × Fin N)))
    Finset.univ_nonempty hρ hσ (fun _ => (N : ℝ)⁻¹ * (N : ℝ)⁻¹) (fun _ => mul_pos hNpos hNpos)
    hsum1 (weylU (n := n) hω) hΦρ hΦσ
  rw [relEntropy_congr hΦρ (hkron ρ hρ.1) hΦσ (hkron σ hσ.1) (hchan ρ) (hchan σ)] at hdpi
  refine le_of_eq_of_le ?_ hdpi
  have hsmul : ∀ τ : Matrix (n × Fin N) (n × Fin N) ℂ,
      partialTraceRight τ ⊗ₖ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ))
        = ((N : ℝ)⁻¹ : ℝ) • (partialTraceRight τ ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    intro τ
    rw [kronecker_smul, realCast_smul]
    congr 1
    push_cast
    ring
  have hH1 : (((N : ℝ)⁻¹ : ℝ) • (partialTraceRight ρ ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ))).IsHermitian :=
    isHermitian_real_smul (isHermitian_kronecker (partialTraceRight_isHermitian hρ.1)
      Matrix.isHermitian_one) _
  have hH2 : (((N : ℝ)⁻¹ : ℝ) • (partialTraceRight σ ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ))).IsHermitian :=
    isHermitian_real_smul (isHermitian_kronecker (partialTraceRight_isHermitian hσ.1)
      Matrix.isHermitian_one) _
  rw [relEntropy_congr (hkron ρ hρ.1) hH1 (hkron σ hσ.1) hH2 (hsmul ρ) (hsmul σ),
    relEntropy_kron_one (partialTraceRight_posDef hρ) (partialTraceRight_posDef hσ) hNpos,
    Fintype.card_fin]
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [inv_mul_cancel₀ hN, one_mul]

end QIQTH.Entropy
