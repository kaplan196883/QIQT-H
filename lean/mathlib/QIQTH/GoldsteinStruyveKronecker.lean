/-
  Step 3 — Kronecker bridge.

  Connects the full tensor-multiplicativity equation
      `schurForm (ρ ⊗ σ) = schurForm ρ ⊗ schurForm σ`
  to the algebraic constraint `TensorConstraintAt11` from
  `GoldsteinStruyveStep3.lean` by evaluating both sides at the
  `((0,0), (0,0))` matrix component for the rank-1 witness
  `ρ = σ = E₁₁`.

  Strategy: keep things tractable by working at `d = 2` (any single
  `d ≥ 2` suffices, since `step3_algebraic_core` works for arbitrary
  `d ≥ 2`).

  Concretely:
    • Define E₁₁ as `Matrix.stdBasisMatrix 0 0 (1 : ℂ)` on `Fin 2`.
    • At the (0,0) entry of `schurForm 2 α β E₁₁`: equals `α + β/2`.
    • At the ((0,0),(0,0)) entry of `(E₁₁ ⊗ E₁₁) : Matrix (Fin 2 × Fin 2) ...`:
      equals 1.
    • `trace(E₁₁) = 1`, `trace(E₁₁ ⊗ E₁₁) = 1`.
    • `schurForm 4 α β (E₁₁ ⊗ E₁₁)` at ((0,0),(0,0)) equals `α + β/4`.
    • `(schurForm 2 α β E₁₁) ⊗ (schurForm 2 α β E₁₁)` at ((0,0),(0,0))
      equals `(α + β/2)²`.
    • Tensor-multiplicativity at the witness gives the algebraic
      constraint `α + β/4 = (α + β/2)²`, which is
      `TensorConstraintAt11 2 α β`.
-/

import QIQTH.GoldsteinStruyveStep3
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace QIQTH
namespace GoldsteinStruyveKronecker

open Matrix Kronecker

/-- The rank-1 witness matrix E₁₁ on `Fin n × Fin n` complex matrices:
    has value 1 at position (0,0), 0 elsewhere. -/
noncomputable def E11 (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Trace of E₁₁ is 1. -/
lemma E11_trace (n : ℕ) [NeZero n] : Matrix.trace (E11 n) = 1 := by
  unfold Matrix.trace E11
  rw [Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- E₁₁ at (0,0) is 1. -/
lemma E11_at_00 (n : ℕ) [NeZero n] : (E11 n) 0 0 = 1 := by
  simp [E11]

/-- E₁₁ at any other diagonal position is 0. -/
lemma E11_at_off (n : ℕ) [NeZero n] (i j : Fin n) (h : ¬ (i = 0 ∧ j = 0)) :
    (E11 n) i j = 0 := by
  simp [E11, h]

/-- The Schur-form density functional polymorphically over the index type. -/
noncomputable def schurFormFin (n : ℕ) [NeZero n] (α β : ℝ) :
    Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  fun ρ => (α : ℂ) • ρ + (β : ℂ) • ((Matrix.trace ρ / (n : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- The Schur form on `Fin 2 × Fin 2`-indexed matrices (the tensor space). -/
noncomputable def schurFormProd (α β : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ρ => (α : ℂ) • ρ + (β : ℂ) •
            ((Matrix.trace ρ / ((2 : ℕ) * (2 : ℕ) : ℂ)) •
             (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))

/-- The `((0,0),(0,0))` entry of `schurForm 2 α β E₁₁` equals `α + β/2`. -/
lemma schurForm_E11_at_00 (α β : ℝ) :
    (schurFormFin 2 α β (E11 2)) 0 0 = (α : ℂ) + (β : ℂ) / 2 := by
  unfold schurFormFin
  simp [Matrix.add_apply, Matrix.smul_apply, E11_at_00, E11_trace,
        Matrix.one_apply_eq, smul_eq_mul]
  ring

/-- The `((0,0),(0,0))` entry of `schurFormProd α β (E₁₁ ⊗ E₁₁)` equals `α + β/4`. -/
lemma schurFormProd_E11_kron_E11_at_00 (α β : ℝ) :
    (schurFormProd α β ((E11 2) ⊗ₖ (E11 2))) (0, 0) (0, 0)
      = (α : ℂ) + (β : ℂ) / 4 := by
  unfold schurFormProd
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
        E11_at_00, Matrix.trace_kronecker, E11_trace, Matrix.one_apply,
        smul_eq_mul]
  ring

/-- The `((0,0),(0,0))` entry of `(schurForm 2 α β E₁₁) ⊗ (schurForm 2 α β E₁₁)`
    equals `(α + β/2)²`. -/
lemma schur_kron_schur_E11_at_00 (α β : ℝ) :
    ((schurFormFin 2 α β (E11 2)) ⊗ₖ (schurFormFin 2 α β (E11 2))) (0, 0) (0, 0)
      = ((α : ℂ) + (β : ℂ) / 2) ^ 2 := by
  rw [Matrix.kroneckerMap_apply, schurForm_E11_at_00]
  ring

/-- **Step 3 Kronecker bridge.**

    For the witness `ρ = σ = E₁₁` on `Fin 2`, the tensor-multiplicativity
    equation
        `schurFormProd α β (E₁₁ ⊗ E₁₁) = (schurForm 2 α β E₁₁) ⊗ (schurForm 2 α β E₁₁)`
    implies the algebraic constraint
        `α + β/4 = (α + β/2)²`,
    which is `TensorConstraintAt11 2 α β`. -/
theorem step3_kronecker_bridge (α β : ℝ)
    (h_mult : schurFormProd α β ((E11 2) ⊗ₖ (E11 2))
              = (schurFormFin 2 α β (E11 2)) ⊗ₖ (schurFormFin 2 α β (E11 2))) :
    GoldsteinStruyveStep3.TensorConstraintAt11 2 α β := by
  -- Apply both sides at the ((0,0), (0,0)) component.
  have h_at_00 := congr_fun (congr_fun h_mult (0, 0)) (0, 0)
  -- LHS = α + β/4, RHS = (α + β/2)²
  rw [schurFormProd_E11_kron_E11_at_00, schur_kron_schur_E11_at_00] at h_at_00
  -- Now h_at_00 : (α + β/4 : ℂ) = ((α + β/2) : ℂ) ^ 2
  -- Cast back to ℝ.
  unfold GoldsteinStruyveStep3.TensorConstraintAt11
  -- Convert h_at_00 (in ℂ) to ℝ.
  have h_real : α + β / 4 = (α + β / 2)^2 := by exact_mod_cast h_at_00
  -- Simplify the coercion in the goal: ((2:ℕ):ℝ) = 2, so ((2:ℕ):ℝ)^2 = 4.
  push_cast
  linarith [h_real]

/-- **Combined Step 3, fully PROVED for d = 2.**

    The full chain: tensor multiplicativity (at the E₁₁ witness on Fin 2)
    + normalization `α + β = 1`  ⇒  `(α, β) ∈ {(1, 0), (0, 1)}`.

    Proof: Kronecker bridge gives the algebraic constraint;
    `step3_tensor_narrowing` from `GoldsteinStruyveStep3.lean`
    derives the conclusion. -/
theorem step3_tensor_narrowing_via_kronecker (α β : ℝ)
    (h_sum : α + β = 1)
    (h_mult : schurFormProd α β ((E11 2) ⊗ₖ (E11 2))
              = (schurFormFin 2 α β (E11 2)) ⊗ₖ (schurFormFin 2 α β (E11 2))) :
    (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) := by
  have h_constraint : GoldsteinStruyveStep3.TensorConstraintAt11 2 α β :=
    step3_kronecker_bridge α β h_mult
  exact GoldsteinStruyveStep3.step3_tensor_narrowing (by norm_num : 2 ≤ 2) α β h_sum h_constraint

end GoldsteinStruyveKronecker
end QIQTH
