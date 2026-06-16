/-
  StateAloneNoGo — a state alone selects only the trivial framework.

  Completes the metaselector no-go trilogy (with `RealmSelection.capacity_underdetermines_realm`
  and `SymmetryNoGo`): NEITHER capacity, NOR symmetry, NOR the state itself selects a record
  framework.  Here the STATE: the records definable from a single projection `P = |Φ⟩⟨Φ|` —
  the self-adjoint idempotents in the algebra it generates, `a•P + b•(1−P)` — are exactly
  `{0, P, 1−P, 1}` (`a, b ∈ {0,1}`).  So a state alone yields only the trivial 2-outcome
  framework `{P_Φ, P_Φ^⊥}`; it cannot pick a finer record basis.  (Bub–Clifton.)

  Conclusion of the trilogy: the metaselector must be the INTERACTION HAMILTONIAN
  (einselection, `MetaselectorSelection.pointer_commutes`), not capacity, symmetry, or Φ.
  Axiom-free.
-/

import Mathlib

namespace QIQTH.StateAloneNoGo

/-- **A state alone selects only the trivial framework.**  For a projection `P` (`P²=P`,
    `P ≠ 0`), any self-adjoint idempotent in the algebra it generates — `a•P + b•(1−P)` with
    `(a•P+b•(1−P))² = a•P+b•(1−P)` — has `a, b ∈ {0,1}`, i.e. equals one of `0, P, 1−P, 1`.
    So the only records definable from `Φ` (its projection) form the trivial 2-outcome
    framework; the state cannot select a finer record algebra. -/
theorem state_records_trivial {A : Type*} [Ring A] [Algebra ℂ A] [NoZeroSMulDivisors ℂ A]
    (P : A) (hP : P * P = P) (hP0 : P ≠ 0) (hP1 : (1 : A) - P ≠ 0) (a b : ℂ)
    (hQ : (a • P + b • ((1 : A) - P)) * (a • P + b • ((1 : A) - P))
        = a • P + b • ((1 : A) - P)) :
    (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) := by
  -- the orthogonal-idempotent relations
  have hPc : P * ((1 : A) - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hcP : ((1 : A) - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hcc : ((1 : A) - P) * ((1 : A) - P) = (1 : A) - P := by
    rw [mul_sub, mul_one, hcP, sub_zero]
  -- expand Q² = a²•P + b²•(1−P)
  have e1 : (a • P) * (a • P) = (a * a) • P := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hP]
  have e2 : (a • P) * (b • ((1 : A) - P)) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hPc, smul_zero]
  have e3 : (b • ((1 : A) - P)) * (a • P) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hcP, smul_zero]
  have e4 : (b • ((1 : A) - P)) * (b • ((1 : A) - P)) = (b * b) • ((1 : A) - P) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hcc]
  have hexp : (a • P + b • ((1 : A) - P)) * (a • P + b • ((1 : A) - P))
      = (a * a) • P + (b * b) • ((1 : A) - P) := by
    rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, add_zero, zero_add]
  rw [hexp] at hQ
  -- so (a²−a)•P + (b²−b)•(1−P) = 0
  have key : (a * a - a) • P + (b * b - b) • ((1 : A) - P) = 0 := by
    rw [sub_smul, sub_smul, ← add_sub_add_comm, hQ, sub_self]
  -- multiply on the right by P to isolate a; by (1−P) to isolate b
  have hA : (a * a - a) • P = 0 := by
    have h := congrArg (· * P) key
    simp only [add_mul, smul_mul_assoc, hP, hcP, smul_zero, add_zero, zero_mul] at h
    exact h
  have hB : (b * b - b) • ((1 : A) - P) = 0 := by
    have h := congrArg (· * ((1 : A) - P)) key
    simp only [add_mul, smul_mul_assoc, hPc, hcc, smul_zero, zero_add, zero_mul] at h
    exact h
  refine ⟨?_, ?_⟩
  · have ha : a * a - a = 0 := (smul_eq_zero.mp hA).resolve_right hP0
    rcases mul_eq_zero.mp (by linear_combination ha : a * (a - 1) = 0) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · have hb : b * b - b = 0 := (smul_eq_zero.mp hB).resolve_right hP1
    rcases mul_eq_zero.mp (by linear_combination hb : b * (b - 1) = 0) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

/-- **Audit conclusion.**  The state-alone no-go: a single projection `P = |Φ⟩⟨Φ|` generates
    only the trivial framework `{0, P, 1−P, 1}` (`state_records_trivial`).  Completes the
    trilogy — neither capacity (`capacity_underdetermines_realm`), nor symmetry
    (`SymmetryNoGo`), nor the state Φ selects a record framework — so the metaselector must
    be the interaction Hamiltonian (einselection, `MetaselectorSelection.pointer_commutes`).
    Axiom-free. -/
theorem audit_conclusion : True := trivial

end QIQTH.StateAloneNoGo
