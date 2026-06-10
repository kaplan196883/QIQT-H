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
import QIQTH.Entropy.Lieb

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

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

/-- Entrywise complex conjugation as an `ℝ`-star-algebra automorphism of matrices.  It is a ring
    homomorphism (conjugation distributes over matrix products), `ℝ`-linear, and star-preserving
    (`conj(Mᴴ) = (conj M)ᴴ`). -/
noncomputable def conjMatStarAut : Matrix n n ℂ ≃⋆ₐ[ℝ] Matrix n n ℂ where
  toFun M := M.map (starRingEnd ℂ)
  invFun M := M.map (starRingEnd ℂ)
  left_inv M := by ext i j; simp
  right_inv M := by ext i j; simp
  map_mul' M N := by ext i j; simp [Matrix.mul_apply, map_sum]
  map_add' M N := by ext i j; simp
  map_smul' r M := by ext i j; simp
  map_star' M := by ext i j; simp [Matrix.conjTranspose_apply]

@[simp] lemma conjMatStarAut_apply (M : Matrix n n ℂ) :
    conjMatStarAut M = M.map (starRingEnd ℂ) := rfl

/-- For a Hermitian matrix, the transpose is the entrywise conjugate. -/
lemma transpose_eq_conj_of_herm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Aᵀ = A.map (starRingEnd ℂ) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  exact (hA.apply j i).symm

/-- **`rpow` commutes with transpose**: `(A^t)ᵀ = (Aᵀ)^t` for positive-definite `A`.  Transpose is
    entrywise conjugation (Hermitian `A`), which is an `ℝ`-star-algebra automorphism, so it commutes
    with the continuous functional calculus that defines the rpow. -/
lemma rpow_transpose {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ} :
    (A ^ t)ᵀ = (Aᵀ) ^ t := by
  have hAt_herm : (A ^ t).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := t))).isHermitian
  have hcont : Continuous (⇑(conjMatStarAut (n := n))) := by
    have he : (⇑(conjMatStarAut (n := n)))
        = fun M : Matrix n n ℂ => M.map (starRingEnd ℂ) := funext conjMatStarAut_apply
    rw [he]
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ A) := by
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact (Real.continuousAt_rpow_const _ t (Or.inl (hA.eigenvalues_pos i).ne')).continuousWithinAt
  have hpos' : (0 : Matrix n n ℂ) ≤ conjMatStarAut A := by
    rw [conjMatStarAut_apply, ← transpose_eq_conj_of_herm hA.1, Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_transpose_iff.2 hA.posSemidef
  rw [transpose_eq_conj_of_herm hAt_herm, transpose_eq_conj_of_herm hA.1,
    ← conjMatStarAut_apply, ← conjMatStarAut_apply,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    StarAlgHomClass.map_cfc conjMatStarAut (fun x : ℝ => x ^ t) A hf hcont,
    ← CFC.rpow_eq_cfc_real hpos']

/-- The transpose of a positive-definite matrix is positive definite. -/
lemma posDef_transpose {B : Matrix n n ℂ} (hB : B.PosDef) : Bᵀ.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hB ⊢
  refine ⟨hB.1.transpose, fun x hx => ?_⟩
  have hid : star x ⬝ᵥ Bᵀ *ᵥ x = star (star x) ⬝ᵥ B *ᵥ star x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm, star_star]
  rw [hid]
  exact hB.2 (show star x ≠ 0 by simpa using hx)

/-- **No-transpose Lieb concavity** (the relative-entropy input): for positive-definite `Aᵢ, Bᵢ`
    and `t ∈ [0,1]`, `(A,B) ↦ Tr(A^{1-t}·B^t)` is jointly concave (superadditive):
    `Tr(A₀^{1-t} B₀^t) + Tr(A₁^{1-t} B₁^t) ≤ Tr((A₀+A₁)^{1-t} (B₀+B₁)^t)`.
    Lieb's concavity at `K = 1` with the `Bᵀ` transpose removed via `rpow_transpose`. -/
theorem trace_rpow_concave {A₀ A₁ B₀ B₁ : Matrix n n ℂ}
    (hA₀ : A₀.PosDef) (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (A₀ ^ (1 - t) * B₀ ^ t).trace + (A₁ ^ (1 - t) * B₁ ^ t).trace
      ≤ ((A₀ + A₁) ^ (1 - t) * (B₀ + B₁) ^ t).trace := by
  have h := lieb_superadditive (1 : Matrix n n ℂ) hA₀ hA₁
    (posDef_transpose hB₀) (posDef_transpose hB₁) ht0 ht1
  rw [show ((B₀ᵀ) ^ t)ᵀ = B₀ ^ t by
        rw [rpow_transpose (posDef_transpose hB₀), Matrix.transpose_transpose],
      show ((B₁ᵀ) ^ t)ᵀ = B₁ ^ t by
        rw [rpow_transpose (posDef_transpose hB₁), Matrix.transpose_transpose],
      show ((B₀ᵀ + B₁ᵀ) ^ t)ᵀ = (B₀ + B₁) ^ t by
        rw [← Matrix.transpose_add, rpow_transpose (posDef_transpose (hB₀.add hB₁)),
          Matrix.transpose_transpose]] at h
  simpa using h

end QIQTH.Entropy
