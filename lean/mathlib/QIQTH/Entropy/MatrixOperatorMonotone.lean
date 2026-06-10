/-
  Operator-monotone functions on `Matrix n n ℂ`, transported from Mathlib's Löwner–Heinz toolkit
  across the `CStarMatrix` bridge (`QIQTH.Entropy.CStarMatrixBridge`).

  Mathlib proves operator monotonicity of `√` and `rpow` (`CFC.sqrt_le_sqrt`, `CFC.rpow_le_rpow`) for a
  `CStarAlgebra`.  The bridge supplies the three missing `CStarMatrix` CFC instances, so the toolkit
  fires there; `ofMatrix_le_iff` (order coincidence) and the cfc-naturality lemmas below carry the
  results back to our Frobenius-normed `Matrix n n ℂ`.

  Headline: `matrix_sqrt_le_sqrt` — `0 ≤ A ≤ B ⟹ √A ≤ √B` (Loewner order).  This is the operator
  monotonicity of the square root, the maximality ingredient for the operator geometric mean
  (Carlen §3.3–3.5) and hence the route to Lieb's concavity.
-/
import QIQTH.Entropy.CStarMatrixBridge

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **ℝ≥0 non-unital CFC naturality across the bridge.**  `e (cfcₙ f A) = cfcₙ f (e A)` for `0 ≤ A`
    and `f` continuous with `f 0 = 0` — the non-unital companion of `ofMatrix_cfc`, used to transport
    `√` and `rpow` (both defined via the `ℝ≥0` non-unital calculus). -/
lemma ofMatrix_cfcₙ (f : ℝ≥0 → ℝ≥0) (A : Matrix n n ℂ) (hA : 0 ≤ A)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 A) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ofMatrixStarAlgEquiv (cfcₙ f A) = cfcₙ f (ofMatrixStarAlgEquiv A) :=
  NonUnitalStarAlgHomClass.map_cfcₙ ofMatrixStarAlgEquiv f A hf hf0
    (ofMatrixL (A := ℂ) (m := n) (n := n)).continuous hA
    (hφa := ofMatrix_nonneg_iff.mpr (nonneg_iff_posSemidef.mp hA))

/-- The matrix square root commutes with the bridge: `e (√A) = √(e A)` for `0 ≤ A`. -/
lemma ofMatrix_sqrt (A : Matrix n n ℂ) (hA : 0 ≤ A) :
    ofMatrixStarAlgEquiv (CFC.sqrt A) = CFC.sqrt (ofMatrixStarAlgEquiv A) := by
  rw [CFC.sqrt, CFC.sqrt]
  exact ofMatrix_cfcₙ NNReal.sqrt A hA (by fun_prop) (by simp)

/-- **Operator monotonicity of the square root on `Matrix n n ℂ`** (Löwner–Heinz, `p = 1/2`):
    `0 ≤ A ≤ B ⟹ √A ≤ √B`.  Transported from `CFC.sqrt_le_sqrt` across the `CStarMatrix` bridge. -/
theorem matrix_sqrt_le_sqrt {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    CFC.sqrt A ≤ CFC.sqrt B := by
  have hB : 0 ≤ B := hA.trans hAB
  rw [← ofMatrix_le_iff, ofMatrix_sqrt A hA, ofMatrix_sqrt B hB]
  exact CFC.sqrt_le_sqrt _ _ (ofMatrix_le_iff.mpr hAB)

/-- The square root is **monotone** on the positive cone of `Matrix n n ℂ` (packaged form). -/
theorem matrix_sqrt_monotoneOn :
    MonotoneOn (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ) {A | 0 ≤ A} :=
  fun _ hA _ _ hAB => matrix_sqrt_le_sqrt hA hAB

end QIQTH.Entropy
