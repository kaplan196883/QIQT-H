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

end QIQTH.Entropy
