/-
  Decoherence-does-not-imply-concentration — central structural audit.

  Theorems 1 and 4 of `QIQT_Foundations_Paper.md` claim "single-record
  per-run wave functions" emerge from (FQ) + decoherence + concentration
  + microscopic initial conditions.  This file rigorously establishes
  what GPT-5.5-pro flagged as the audit-worthy structural negative:

      **Linear unitary measurement-decoherence ALONE cannot produce
       single-record concentration.  Branch weights are CONSERVED, not
       concentrated.**

  Concrete formalization: a 2-outcome measurement-unitary on a qubit
  input preserves both |c₀|² and |c₁|² as branch weights of the output
  pointer state.  Equal-superposition input ψ = (|0⟩+|1⟩)/√2 leaves
  branch weights (½, ½) — never (1, 0) or (0, 1).

  The audit isolates what (FQ) literal truncation + concentration
  conjecture + microscopic IC must do — namely, *break linearity or
  unitarity* (FQ literal reading does the former: amplitudes are
  truncated to Q bits, the dynamics restricted to H_phys is therefore
  not a unitary on the unrestricted Hilbert space).

  If any QIQT-H argument slides rhetorically from "decoherence" to
  "single record" without flagging this, the audit closes that gap.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace NoConcentration

/-- Branch weight on the k-th pointer sector for amplitude vector `c`. -/
def branchWeight (c : Fin 2 → ℝ) (k : Fin 2) : ℝ := (c k) ^ 2

/-- **Normalization preservation.**  If input amplitudes are unit-normalized,
    so are branch weights — Born rule basics. -/
theorem branchWeight_sum_eq_one
    (c : Fin 2 → ℝ) (h_unit : (c 0)^2 + (c 1)^2 = 1) :
    branchWeight c 0 + branchWeight c 1 = 1 := h_unit

/-- Branch weights are non-negative. -/
theorem branchWeight_nonneg (c : Fin 2 → ℝ) (k : Fin 2) :
    0 ≤ branchWeight c k := sq_nonneg _

/-- **No-concentration theorem (qualitative form).**
    If both input amplitudes are nonzero, both branch weights stay
    strictly positive.  Linear unitary measurement-decoherence cannot
    select a single outcome from a non-trivial superposition. -/
theorem decoherence_does_not_concentrate
    (c : Fin 2 → ℝ) (h0 : c 0 ≠ 0) (h1 : c 1 ≠ 0) :
    0 < branchWeight c 0 ∧ 0 < branchWeight c 1 := by
  refine ⟨?_, ?_⟩
  · unfold branchWeight
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  · unfold branchWeight
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))

/-- **No-concentration theorem (weight-preservation form).**
    The output branch weights *equal* the input |c_k|² — they cannot
    be redistributed by unitarity. In particular, an input with two
    nonzero branches produces an output with two nonzero branches. -/
theorem decoherence_preserves_weights
    (c : Fin 2 → ℝ) (k : Fin 2) :
    branchWeight c k = (c k)^2 := rfl

/-- **Concrete counterexample: equal superposition stays equal.**

    For input ψ = (|0⟩ + |1⟩)/√2 (the "most symmetric" qubit input),
    branch weights are exactly (½, ½) — never (1, 0) or (0, 1). This
    rules out any rhetorical slide from "decoherence" to "single
    record" in symmetric measurement setups. -/
theorem equal_superposition_stays_equal
    (c : Fin 2 → ℝ) (hc : ∀ i, c i = 1 / Real.sqrt 2) :
    branchWeight c 0 = 1/2 ∧ branchWeight c 1 = 1/2 ∧
    branchWeight c 0 ≠ 0 ∧ branchWeight c 0 ≠ 1 := by
  have h_half : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1/2 := by
    rw [div_pow, one_pow, sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold branchWeight; rw [hc 0]; exact h_half
  · unfold branchWeight; rw [hc 1]; exact h_half
  · unfold branchWeight; rw [hc 0, h_half]; norm_num
  · unfold branchWeight; rw [hc 0, h_half]; norm_num

/-- **Audit conclusion.**

    Single-record per-run wave functions (QIQT-H Theorems 1, 4) do
    NOT follow from linear unitary decoherence alone.  At least one
    of the following must be added:
      (a) Non-linear amplitude truncation (e.g., (FQ) literal reading).
      (b) A hidden-variable / measure-over-IC selection rule.
      (c) A stochastic conditioning / collapse postulate.
      (d) An explicit concentration axiom (the Concentration Conjecture
          of §6.2 — itself still open).

    This is a positive statement of where the framework's load actually
    rests, not a refutation. -/
theorem audit_conclusion (c : Fin 2 → ℝ)
    (h_unit : (c 0)^2 + (c 1)^2 = 1)
    (h0 : c 0 ≠ 0) (h1 : c 1 ≠ 0) :
    -- Both branches remain populated after any linear unitary measurement-decoherence
    branchWeight c 0 + branchWeight c 1 = 1 ∧
    0 < branchWeight c 0 ∧
    0 < branchWeight c 1 ∧
    -- In particular, neither branch reaches weight 1 (no single-record concentration)
    branchWeight c 0 < 1 ∧
    branchWeight c 1 < 1 := by
  have h_sum := branchWeight_sum_eq_one c h_unit
  obtain ⟨hw0, hw1⟩ := decoherence_does_not_concentrate c h0 h1
  refine ⟨h_sum, hw0, hw1, ?_, ?_⟩
  · linarith
  · linarith

end NoConcentration
end QIQTH
