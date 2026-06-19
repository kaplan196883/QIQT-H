import QIQTH.Entropy.WeylDesign
import QIQTH.Entropy.PartialTrace
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
open scoped Kronecker

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

end QIQTH.Entropy
