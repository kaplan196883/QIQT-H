/-
  The weighted operator geometric mean `A #ₜ B`, `t ∈ [0,1]` (Kubo–Ando), via matrix `rpow`:
  `A #ₜ B = A^{1/2} (A^{-1/2} B A^{-1/2})^t A^{1/2}`.

  It interpolates the endpoints (`A #_0 B = A`, `A #_1 B = B`) and recovers the geometric mean at the
  midpoint (`A #_{1/2} B = A # B`, `wgmean_half`).  The weight-midpoint identity
  `(A#ₛB) #½ (A#ₜB) = A #_{(s+t)/2} B` (next step, from `gmean_congr`) then bisects `{0,1}` to all
  dyadic weights, which `matrix_le_of_tendsto` lifts to all `t` — the continuity route to Lieb.
-/
import QIQTH.Entropy.GeometricMean

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted operator geometric mean `A #ₜ B = A^{1/2} (A^{-1/2} B A^{-1/2})^t A^{1/2}`. -/
noncomputable def wgmean (t : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * (((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) ^ t) * CFC.sqrt A

/-- `A #ₜ B` is positive semidefinite (a congruence of the positive `(A^{-1/2}BA^{-1/2})^t`). -/
lemma wgmean_nonneg (t : ℝ) {A B : Matrix n n ℂ} : 0 ≤ wgmean t A B := by
  have h := (nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) (y := t))
    ).mul_mul_conjTranspose_same (CFC.sqrt A)
  rw [(sqrt_isHermitian A).eq] at h
  exact nonneg_iff_posSemidef.mpr h

/-- **Midpoint = geometric mean**: `A #_{1/2} B = A # B`. -/
lemma wgmean_half (A B : Matrix n n ℂ) : wgmean (1 / 2) A B = gmean A B := by
  unfold wgmean gmean
  rw [← CFC.sqrt_eq_rpow]

/-- **Left endpoint**: `A #_0 B = A`. -/
lemma wgmean_zero {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) : wgmean 0 A B = A := by
  unfold wgmean
  rw [CFC.rpow_zero _ (inner_conj_posSemidef hB), Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA]

/-- **Right endpoint**: `A #_1 B = B`. -/
lemma wgmean_one {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : 0 ≤ B) : wgmean 1 A B = B := by
  unfold wgmean
  rw [CFC.rpow_one _ (inner_conj_posSemidef hB),
    show CFC.sqrt A * ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A
        = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * B * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) by
      simp only [Matrix.mul_assoc],
    sqrt_mul_inv hA, sqrt_inv_mul hA, Matrix.one_mul, Matrix.mul_one]

end QIQTH.Entropy
