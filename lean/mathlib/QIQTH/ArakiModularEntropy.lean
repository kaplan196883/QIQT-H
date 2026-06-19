import QIQTH.ArakiEntropy
import QIQTH.Entropy.RelEntropyDPI

/-!
# The modular flow preserves the relative entropy

The modular automorphism `σ_t(B) = ρ^{it} B ρ^{−it}` (`QIQTH.Araki.modAut`) is conjugation by the
unitary `ρ^{it} = exp(it·log ρ)`, and the quantum relative entropy is invariant under unitary
conjugation (`QIQTH.Entropy.relEntropy_unitary_invariant`).  Hence the modular flow is
entropy-preserving: `S(σ_t(A) ‖ σ_t(B)) = S(A ‖ B)`.

This lives in a downstream file (rather than `ArakiEntropy.lean`) to keep the unitary-invariance
import off the Hilbert–Schmidt inner-product machinery, which it perturbs.  Only the matrix-level
objects (`modAut`, `matLog`, `expIt_*`) are used here — no HS inner product.
-/

namespace QIQTH.Araki

open QIQTH.QuantumEntropy Unitary
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

variable {n : Type} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- **The modular flow preserves relative entropy:** `S(σ_t(A) ‖ σ_t(B)) = S(A ‖ B)` — since `σ_t` is
    conjugation by the unitary `ρ^{it}`, and the relative entropy is unitarily invariant.  The modular
    automorphism group acts by entropy-preserving `*`-automorphisms. -/
theorem relEntropy_modAut_invariant (hρ : ρ.PosDef) {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ)
    (hmA : (modAut hρ t A).IsHermitian) (hmB : (modAut hρ t B).IsHermitian) :
    QIQTH.QuantumEntropy.relEntropy hmA hmB = QIQTH.QuantumEntropy.relEntropy hA.1 hB.1 := by
  have hu : NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) ∈ unitary (Matrix n n ℂ) := by
    rw [Unitary.mem_iff]
    exact ⟨by rw [Matrix.star_eq_conjTranspose, conjTranspose_expIt hρ t, expNegIt_mul_expIt hρ t],
      by rw [Matrix.star_eq_conjTranspose, conjTranspose_expIt hρ t, expIt_mul_expNegIt hρ t]⟩
  have heq : ∀ X : Matrix n n ℂ,
      ((⟨_, hu⟩ : unitary (Matrix n n ℂ)) : Matrix n n ℂ) * X
        * (star (⟨_, hu⟩ : unitary (Matrix n n ℂ)) : Matrix n n ℂ) = modAut hρ t X := by
    intro X
    show NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1) * X
        * (NormedSpace.exp ((Complex.I * (t : ℂ)) • matLog hρ.1))ᴴ = modAut hρ t X
    rw [conjTranspose_expIt hρ t, modAut]
  have h := QIQTH.Entropy.relEntropy_unitary_invariant hA hB ⟨_, hu⟩ (by rw [heq]; exact hmA)
    (by rw [heq]; exact hmB)
  rw [← h]
  exact QIQTH.Entropy.relEntropy_congr hmA _ hmB _ (heq A).symm (heq B).symm

end QIQTH.Araki
