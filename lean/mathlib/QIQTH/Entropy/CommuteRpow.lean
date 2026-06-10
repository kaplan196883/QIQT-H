/-
  Commuting-product rpow: `(P * Q)^t = P^t * Q^t` for commuting positive-definite `P, Q`.

  This is the matrix fact Mathlib lacks (no simultaneous diagonalization of commuting Hermitians).
  Strategy: commuting `√` (`sqrt_mul_of_commute`, via `sqrt_unique`) iterates to the dyadic powers
  `1/2ⁿ`, hence all dyadics `k/2ⁿ`; continuity in the exponent (`continuous_matrix_rpow`) + density of
  dyadics then gives all `t`.  Feeds the tensor power `(A ⊗ B)^t = A^t ⊗ B^t` (TensorPower) and thence
  the `A^{1-t} ⊗ B^t` form of Lieb's concavity.
-/
import QIQTH.Entropy.WeightedMean

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace QIQTH.Entropy

open Matrix CStarMatrix Filter
open scoped MatrixOrder ComplexOrder NNReal Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of two commuting positive-semidefinite matrices is positive semidefinite:
    `X * Y = √X · Y · √X` (a congruence of `Y`). -/
lemma posSemidef_mul_of_commute {X Y : Matrix n n ℂ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : Commute X Y) :
    (0 : Matrix n n ℂ) ≤ X * Y := by
  have hcomm : Commute (CFC.sqrt X) Y := h.cfcₙ_nnreal NNReal.sqrt
  have heq : X * Y = CFC.sqrt X * Y * CFC.sqrt X := by
    rw [Matrix.mul_assoc, hcomm.symm.eq, ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self X hX]
  rw [heq]
  have hpsd := (nonneg_iff_posSemidef.mp hY).mul_mul_conjTranspose_same (CFC.sqrt X)
  rw [(sqrt_isHermitian X).eq] at hpsd
  exact nonneg_iff_posSemidef.mpr hpsd

/-- **Commuting square root**: `√(P * Q) = √P * √Q` for commuting positive-semidefinite `P, Q`. -/
lemma sqrt_mul_of_commute {P Q : Matrix n n ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : Commute P Q) :
    CFC.sqrt (P * Q) = CFC.sqrt P * CFC.sqrt Q := by
  have hcomm : Commute (CFC.sqrt P) (CFC.sqrt Q) :=
    ((h.cfcₙ_nnreal NNReal.sqrt).symm.cfcₙ_nnreal NNReal.sqrt).symm
  refine CFC.sqrt_unique ?_
    (posSemidef_mul_of_commute (CFC.sqrt_nonneg P) (CFC.sqrt_nonneg Q) hcomm)
  calc CFC.sqrt P * CFC.sqrt Q * (CFC.sqrt P * CFC.sqrt Q)
      = CFC.sqrt P * CFC.sqrt P * (CFC.sqrt Q * CFC.sqrt Q) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt Q), hcomm.symm.eq, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = P * Q := by rw [CFC.sqrt_mul_sqrt_self P hP, CFC.sqrt_mul_sqrt_self Q hQ]

/-- Powers of commuting matrices commute: `Commute P Q ⟹ Commute (P^a) (Q^a)` (for `0 ≤ P, Q`). -/
lemma commute_rpow {P Q : Matrix n n ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : Commute P Q) (a : ℝ) :
    Commute (P ^ a) (Q ^ a) := by
  rw [CFC.rpow_eq_cfc_real hP, CFC.rpow_eq_cfc_real hQ]
  have h1 : Commute (cfc (fun x : ℝ => x ^ a) P) Q := h.cfc_real (fun x : ℝ => x ^ a)
  exact (h1.symm.cfc_real (fun x : ℝ => x ^ a)).symm

/-- Product of commuting positive-definite matrices is positive definite. -/
lemma posDef_mul_of_commute {X Y : Matrix n n ℂ} (hX : X.PosDef) (hY : Y.PosDef) (h : Commute X Y) :
    (X * Y).PosDef := by
  have hcomm : Commute (CFC.sqrt X) Y := h.cfcₙ_nnreal NNReal.sqrt
  have heq : X * Y = CFC.sqrt X * Y * CFC.sqrt X := by
    rw [Matrix.mul_assoc, hcomm.symm.eq, ← Matrix.mul_assoc,
      CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]
  rw [heq]
  have hU : IsUnit (CFC.sqrt X) := (Matrix.isUnit_iff_isUnit_det _).mpr (sqrt_isUnit_det hX)
  have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := Y) hU).mpr hY
  rwa [Matrix.star_eq_conjTranspose, (sqrt_isHermitian X).eq] at this

/-- **The dyadic powers `1/2ᵐ` agree**: `(P*Q)^{(2ᵐ)⁻¹} = P^{(2ᵐ)⁻¹} * Q^{(2ᵐ)⁻¹}`, by induction on `m`
    (each step is the commuting square root). -/
lemma commute_rpow_inv_two_pow {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (h : Commute P Q) (m : ℕ) :
    (P * Q) ^ (((2 : ℝ) ^ m)⁻¹) = P ^ (((2 : ℝ) ^ m)⁻¹) * Q ^ (((2 : ℝ) ^ m)⁻¹) := by
  have hPQ : (P * Q).PosDef := posDef_mul_of_commute hP hQ h
  induction m with
  | zero =>
    simp only [pow_zero, inv_one]
    rw [CFC.rpow_one _ hPQ.posSemidef.nonneg, CFC.rpow_one _ hP.posSemidef.nonneg,
      CFC.rpow_one _ hQ.posSemidef.nonneg]
  | succ p ih =>
    have hstep : (((2 : ℝ) ^ p)⁻¹) / 2 = ((2 : ℝ) ^ (p + 1))⁻¹ := by
      rw [pow_succ]; ring
    rw [← hstep, ← sqrt_rpow hPQ, ih, sqrt_mul_of_commute (CFC.rpow_nonneg) (CFC.rpow_nonneg)
      (commute_rpow hP.posSemidef.nonneg hQ.posSemidef.nonneg h _), sqrt_rpow hP, sqrt_rpow hQ]

/-- `M^{m/2ᵏ} = (M^{(2ᵏ)⁻¹})^m` (rpow ↔ iterated power). -/
private lemma rpow_dyadic_eq_pow {M : Matrix n n ℂ} (hM : 0 ≤ M) (m k : ℕ) :
    M ^ ((m : ℝ) / 2 ^ k) = (M ^ (((2 : ℝ) ^ k)⁻¹)) ^ m := by
  rw [show (m : ℝ) / 2 ^ k = ((2 : ℝ) ^ k)⁻¹ * (m : ℝ) by ring,
    ← CFC.rpow_rpow_of_exponent_nonneg M ((2 : ℝ) ^ k)⁻¹ (m : ℝ) (by positivity) (by positivity),
    CFC.rpow_natCast _ m CFC.rpow_nonneg]

/-- **The dyadic powers `m/2ᵏ` agree**: `(P*Q)^{m/2ᵏ} = P^{m/2ᵏ} * Q^{m/2ᵏ}`. -/
lemma commute_rpow_dyadic {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) (h : Commute P Q)
    (m k : ℕ) :
    (P * Q) ^ ((m : ℝ) / 2 ^ k) = P ^ ((m : ℝ) / 2 ^ k) * Q ^ ((m : ℝ) / 2 ^ k) := by
  have hPQ : (P * Q).PosDef := posDef_mul_of_commute hP hQ h
  rw [rpow_dyadic_eq_pow hPQ.posSemidef.nonneg, rpow_dyadic_eq_pow hP.posSemidef.nonneg,
    rpow_dyadic_eq_pow hQ.posSemidef.nonneg, commute_rpow_inv_two_pow hP hQ h k,
    (commute_rpow hP.posSemidef.nonneg hQ.posSemidef.nonneg h _).mul_pow m]

/-- **Commuting-product rpow** (the matrix fact Mathlib lacks): `(P*Q)^t = P^t * Q^t` for commuting
    positive-definite `P, Q` and `0 ≤ t`.  Dyadic agreement (`commute_rpow_dyadic`) extends to all `t`
    by continuity in the exponent (`continuous_matrix_rpow`) and density of the dyadic approximations. -/
theorem commute_rpow_mul {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) (h : Commute P Q)
    {t : ℝ} (ht : 0 ≤ t) : (P * Q) ^ t = P ^ t * Q ^ t := by
  have hPQ : (P * Q).PosDef := posDef_mul_of_commute hP hQ h
  -- dyadic approximations ⌊t·2ʲ⌋/2ʲ → t
  have hd : Tendsto (fun j : ℕ => (⌊t * 2 ^ j⌋₊ : ℝ) / 2 ^ j) atTop (𝓝 t) := by
    have hpow : Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub hpow) tendsto_const_nhds (fun j => ?_) (fun j => ?_)
    · have h2 : (0 : ℝ) < 2 ^ j := by positivity
      rw [le_div_iff₀ h2]
      have hlt := Nat.lt_floor_add_one (t * 2 ^ j)
      have hone : ((2 : ℝ) ^ j)⁻¹ * 2 ^ j = 1 := inv_mul_cancel₀ (by positivity)
      rw [sub_mul, hone]; linarith [hlt]
    · have h2 : (0 : ℝ) < 2 ^ j := by positivity
      rw [div_le_iff₀ h2]; exact Nat.floor_le (by positivity)
  have hcont : Continuous (fun s : ℝ => P ^ s * Q ^ s) :=
    (continuous_matrix_rpow hP).matrix_mul (continuous_matrix_rpow hQ)
  refine tendsto_nhds_unique ((continuous_matrix_rpow hPQ).tendsto t |>.comp hd)
    (((hcont.tendsto t).comp hd).congr (fun j => ?_))
  exact (commute_rpow_dyadic hP hQ h ⌊t * 2 ^ j⌋₊ j).symm

end QIQTH.Entropy
