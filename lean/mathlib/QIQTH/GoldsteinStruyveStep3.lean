/-
  Step 3 — algebraic core of the tensor-multiplicativity narrowing.

  GPT-5.5-pro recommended approach: extract the **algebraic constraint**
  that tensor multiplicativity imposes at a specific witness matrix,
  rather than formalising the full Kronecker-product machinery.

  **The constraint:** evaluating
      `schurForm α β (E₁₁ ⊗ E₁₁) = schurForm α β E₁₁ ⊗ schurForm α β E₁₁`
  at the `((1,1), (1,1))` component yields
      α + β/d² = (α + β/d)².
  Combined with α + β = 1, this gives the **polynomial identity**
      α·d² + (1-α) - (α·d + (1-α))² = α·(d-1)²·(1-α)
  so the constraint reduces to `α(d-1)²(1-α) = 0`, and for `d ≥ 2`
  (where `(d-1)² > 0`) this forces `α(1-α) = 0`, hence `α ∈ {0, 1}`.

  This module proves the algebraic deduction rigorously.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace QIQTH
namespace GoldsteinStruyveStep3

/-- The algebraic constraint imposed by tensor multiplicativity at the
    `((1,1), (1,1))` component of `D(E₁₁ ⊗ E₁₁) = D(E₁₁) ⊗ D(E₁₁)`. -/
def TensorConstraintAt11 (d : ℕ) (α β : ℝ) : Prop :=
  α + β / (d : ℝ)^2 = (α + β / (d : ℝ))^2

/-- **Step 3 algebraic core (PROVED).**

    Given `α + β = 1` (Step 2's conclusion) and the tensor-mult
    constraint, we have `α(α - 1) = 0`, hence `α ∈ {0, 1}`.

    The proof works via the polynomial identity
        `α·d² + (1-α) - (α·d + (1-α))² = α·(d-1)²·(1-α)`,
    proven by `ring`. -/
theorem step3_algebraic_core
    {d : ℕ} (hd : 2 ≤ d) (α β : ℝ)
    (h_sum : α + β = 1)
    (h_constraint : TensorConstraintAt11 d α β) :
    α * (α - 1) = 0 := by
  unfold TensorConstraintAt11 at h_constraint
  -- Positivity prep.
  have hd_pos : (0 : ℝ) < d := by
    have h_nat : (0 : ℕ) < d := by omega
    exact_mod_cast h_nat
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd_minus_1_pos : (0 : ℝ) < (d : ℝ) - 1 := by
    have h_nat : (1 : ℕ) < d := by omega
    have h_real : (1 : ℝ) < (d : ℝ) := by exact_mod_cast h_nat
    linarith
  have hd_minus_1_sq_pos : 0 < ((d : ℝ) - 1)^2 := pow_pos hd_minus_1_pos 2
  have hd_minus_1_sq_ne : ((d : ℝ) - 1)^2 ≠ 0 := ne_of_gt hd_minus_1_sq_pos
  -- Substitute β = 1 - α.
  have hβ : β = 1 - α := by linarith
  rw [hβ] at h_constraint
  -- Multiply both sides of h_constraint by d² to clear denominators.
  have h_cleared : α * (d : ℝ)^2 + (1 - α) = (α * (d : ℝ) + (1 - α))^2 := by
    have step_lhs : (α + (1 - α) / (d : ℝ)^2) * (d : ℝ)^2
                  = α * (d : ℝ)^2 + (1 - α) := by field_simp
    have h_inner : (α + (1 - α) / (d : ℝ)) * (d : ℝ) = α * (d : ℝ) + (1 - α) := by
      field_simp
    have step_rhs : (α + (1 - α) / (d : ℝ))^2 * (d : ℝ)^2
                  = (α * (d : ℝ) + (1 - α))^2 := by
      rw [← mul_pow, h_inner]
    have h_mul : (α + (1 - α) / (d : ℝ)^2) * (d : ℝ)^2
               = (α + (1 - α) / (d : ℝ))^2 * (d : ℝ)^2 := by
      rw [h_constraint]
    calc α * (d : ℝ)^2 + (1 - α)
        = (α + (1 - α) / (d : ℝ)^2) * (d : ℝ)^2 := step_lhs.symm
      _ = (α + (1 - α) / (d : ℝ))^2 * (d : ℝ)^2 := h_mul
      _ = (α * (d : ℝ) + (1 - α))^2 := step_rhs
  -- Polynomial identity: LHS - RHS = α·(d-1)²·(1-α).
  have h_id : α * (d : ℝ)^2 + (1 - α) - (α * (d : ℝ) + (1 - α))^2
            = α * ((d : ℝ) - 1)^2 * (1 - α) := by ring
  -- From h_cleared, the LHS of h_id equals 0.
  have h_factored : α * ((d : ℝ) - 1)^2 * (1 - α) = 0 := by linarith [h_id, h_cleared]
  -- Extract α·(1-α) = 0 by dividing out (d-1)² ≠ 0.
  have h_rearr : α * ((d : ℝ) - 1)^2 * (1 - α)
               = ((d : ℝ) - 1)^2 * (α * (1 - α)) := by ring
  rw [h_rearr] at h_factored
  have h_alpha_1m : α * (1 - α) = 0 :=
    mul_left_cancel₀ hd_minus_1_sq_ne (h_factored.trans (mul_zero _).symm)
  -- Conclude α·(α-1) = -α·(1-α) = 0.
  have h_neg : α * (α - 1) = -(α * (1 - α)) := by ring
  linarith [h_alpha_1m, h_neg]

/-- **Step 3 — tensor narrowing (PROVED via algebraic core).**

    Combining `α + β = 1` and the tensor-multiplicativity constraint
    at the (1,1) component:  `(α, β) ∈ {(1, 0), (0, 1)}`. -/
theorem step3_tensor_narrowing
    {d : ℕ} (hd : 2 ≤ d) (α β : ℝ)
    (h_sum : α + β = 1)
    (h_constraint : TensorConstraintAt11 d α β) :
    (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) := by
  have h_core : α * (α - 1) = 0 := step3_algebraic_core hd α β h_sum h_constraint
  rcases mul_eq_zero.mp h_core with hα0 | hα1
  · right
    exact ⟨hα0, by linarith⟩
  · left
    have : α = 1 := by linarith
    exact ⟨this, by linarith⟩

end GoldsteinStruyveStep3
end QIQTH
