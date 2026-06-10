/-
  **`rpow` commutes with unitary conjugation**: `(u·M·u⋆)^t = u·M^t·u⋆` for a unitary `u` and
  positive-semidefinite `M`.  A clean consequence of CFC naturality (`StarAlgHomClass.map_cfc`)
  under the inner ∗-automorphism `conjStarAlgAut u : x ↦ u·x·u⋆`, since the matrix rpow is
  `CFC.rpow a t = cfc (·^t) a` (`CFC.rpow_eq_cfc_real`).

  This is the engine for transporting the rpow through a change of orthonormal basis — used to
  relate `(A^t)ᵀ` to `(Aᵀ)^t` (the transpose moves the eigenvectors to their conjugates, a unitary
  congruence), the gating step toward the no-transpose form of Lieb's concavity that the relative
  entropy consumes.
-/
import QIQTH.Entropy.WeightedMean

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `rpow` commutes with conjugation by a unitary: `(u·M·u⋆)^t = u·M^t·u⋆`. -/
lemma rpow_unitary_conj {M : Matrix n n ℂ} (hM : M.PosDef)
    (u : unitary (Matrix n n ℂ)) {t : ℝ} :
    ((u : Matrix n n ℂ) * M * (star u : Matrix n n ℂ)) ^ t
      = (u : Matrix n n ℂ) * M ^ t * (star u : Matrix n n ℂ) := by
  have hconj : ∀ x : Matrix n n ℂ,
      (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) x
        = (u : Matrix n n ℂ) * x * (star u : Matrix n n ℂ) :=
    fun x => Unitary.conjStarAlgAut_apply u x
  -- conjugation preserves positivity (a ∗-ring equivalence is an order isomorphism)
  have hpos : (0 : Matrix n n ℂ) ≤ (u : Matrix n n ℂ) * M * (star u : Matrix n n ℂ) := by
    rw [Matrix.nonneg_iff_posSemidef, show (star u : Matrix n n ℂ) = (u : Matrix n n ℂ)ᴴ from rfl]
    exact hM.posSemidef.mul_mul_conjTranspose_same _
  -- `conjStarAlgAut u` is continuous (a fixed two-sided matrix product)
  have hcont : Continuous (⇑(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u)) := by
    have he : (⇑(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u))
        = fun x => (u : Matrix n n ℂ) * x * (star u : Matrix n n ℂ) := funext hconj
    rw [he]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  -- `·^t` is continuous on the (strictly positive) spectrum of `M`
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ M) := by
    rw [hM.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact (Real.continuousAt_rpow_const _ t (Or.inl (hM.eigenvalues_pos i).ne')).continuousWithinAt
  rw [CFC.rpow_eq_cfc_real hpos, ← hconj M,
    ← StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) (fun x : ℝ => x ^ t) M hf hcont,
    ← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg, hconj (M ^ t)]

end QIQTH.Entropy
