/-
  Phase 2 of the DPI / Lieb program (Carlen §2.1, §3): operator convexity / monotonicity.

  This is the analytic crux of the tower.  We work with Mathlib's **Loewner order** on Hermitian
  matrices (`Matrix.instPreOrder`/`instPartialOrder`, `A ≤ B := (B − A).PosSemidef`, scoped
  `MatrixOrder`).  The foundational fact, used throughout the Schur-complement / Ando route to Lieb's
  concavity, is that the order is preserved by **congruence (conjugation)** `A ↦ V⋆AV` — from
  `PosSemidef.conjTranspose_mul_mul_same`.

  Mathlib already provides the inverse half of Löwner–Heinz (`rpow_neg_one_le_rpow_neg_one`: the inverse
  is operator-antitone).  Later in this phase: operator convexity of `t⁻¹` (Carlen Lemma 2.7) and the
  Schur complement (Lemma 3.2, `[[A,B],[B⋆,C]]` PSD ⟺ `C ≥ B⋆A⁻¹B`), which yields the joint convexity
  of `(A,B) ↦ B⋆A⁻¹B` and the operator-mean concavities feeding Lieb.
-/
import QIQTH.QuantumRelativeEntropy
import Mathlib.Analysis.Matrix.Order

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Congruence preserves the Loewner order.**  If `A ≤ B` then `V⋆AV ≤ V⋆BV` for any `V`.  (From
    `PosSemidef.conjTranspose_mul_mul_same`: conjugation preserves positive semidefiniteness, applied to
    `B − A`.)  The basic monotonicity used throughout the Schur / Ando route to Lieb's concavity. -/
lemma conjTranspose_mul_mul_le {A B : Matrix n n ℂ} (hAB : A ≤ B) (V : Matrix n m ℂ) :
    Vᴴ * A * V ≤ Vᴴ * B * V := by
  rw [Matrix.le_iff] at hAB ⊢
  have hsub : Vᴴ * B * V - Vᴴ * A * V = Vᴴ * (B - A) * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub]
  exact hAB.conjTranspose_mul_mul_same V

/-- `0 ≤ A ⇒ 0 ≤ V⋆AV` (congruence preserves positivity) — the special case `A = 0 ≤ B`. -/
lemma zero_le_conjTranspose_mul_mul {A : Matrix n n ℂ} (hA : 0 ≤ A) (V : Matrix n m ℂ) :
    0 ≤ Vᴴ * A * V := by
  have := conjTranspose_mul_mul_le hA V
  simpa using this

/-- **Congruence preserves the order (left form)** `A ≤ B ⇒ V A V⋆ ≤ V B V⋆`, from
    `PosSemidef.mul_mul_conjTranspose_same`. -/
lemma mul_mul_conjTranspose_le {A B : Matrix n n ℂ} (hAB : A ≤ B) (V : Matrix m n ℂ) :
    V * A * Vᴴ ≤ V * B * Vᴴ := by
  rw [Matrix.le_iff] at hAB ⊢
  have hsub : V * B * Vᴴ - V * A * Vᴴ = V * (B - A) * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub]
  exact hAB.mul_mul_conjTranspose_same V

/-! ### The Schur complement and the minimality of `B⋆A⁻¹B` (Carlen §3.1, Lemma 3.2)

Mathlib already proves the **Schur complement** (`Matrix.PosDef.fromBlocks₁₁`):
`fromBlocks A B B⋆ D` is PSD ⟺ `D − B⋆A⁻¹B ≥ 0` (for `A` positive definite).  This is exactly Carlen
Lemma 3.2.  From it we get the **minimality** of `B⋆A⁻¹B` (the bottom-right block making the 2×2 block
PSD), which is the engine of Ando's joint-convexity theorem (Thm 3.1, the next step toward Lieb). -/

/-- **The block `[[A, B],[B⋆, B⋆A⁻¹B]]` is positive semidefinite** for positive-definite `A` — the
    Schur-complement factorization (Carlen Lemma 3.2, ⟸ direction with zero Schur complement). -/
lemma fromBlocks_star_inv_posSemidef {A : Matrix m m ℂ} (hA : A.PosDef) [Invertible A]
    (B : Matrix m n ℂ) :
    (Matrix.fromBlocks A B Bᴴ (Bᴴ * A⁻¹ * B)).PosSemidef := by
  rw [Matrix.PosDef.fromBlocks₁₁ B (Bᴴ * A⁻¹ * B) hA, sub_self]
  exact Matrix.PosSemidef.zero

/-- **Minimality of `B⋆A⁻¹B`** (Carlen Lemma 3.2): if `fromBlocks A B B⋆ D` is PSD with `A` positive
    definite, then `B⋆A⁻¹B ≤ D`.  This is the property that drives Ando's joint convexity of
    `(A,B) ↦ B⋆A⁻¹B`. -/
lemma star_inv_le_of_fromBlocks_posSemidef {A : Matrix m m ℂ} (hA : A.PosDef) [Invertible A]
    {B : Matrix m n ℂ} {D : Matrix n n ℂ} (h : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    Bᴴ * A⁻¹ * B ≤ D := by
  rw [Matrix.le_iff]
  exact (Matrix.PosDef.fromBlocks₁₁ B D hA).mp h

end QIQTH.Entropy
