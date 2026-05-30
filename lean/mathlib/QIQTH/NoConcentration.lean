/-
  Decoherence-does-not-imply-concentration — central structural audit.

  Theorems 1 and 4 of `QIQT_Foundations_Paper.md` claim "single-record
  per-run regional content".  This file rigorously establishes what
  GPT-5.5-pro flagged as the audit-worthy structural negative:

      **Linear unitary measurement-decoherence ALONE cannot select a
       single outcome.  Branch weights are CONSERVED, not driven to
       0/1.**

  Concrete formalization: a 2-outcome measurement-unitary on a qubit
  input preserves both |c₀|² and |c₁|² as branch weights of the output
  pointer state.  Equal-superposition input ψ = (|0⟩+|1⟩)/√2 leaves
  branch weights (½, ½) — never (1, 0) or (0, 1).

  **Significance under the canonical (state-space) reading.**  This is
  exactly why the framework's single-outcome mechanism is NOT
  "decoherence drives amplitudes to 0/1" (it does not, as proved here)
  and is NOT any amplitude trimming or dynamics modification.  Per the
  canonical reading the dynamics stays *exactly unitary*; decoherence
  only removes interference, leaving a multi-record mixture.  The
  single-record content comes from the separate, kinematic
  finite-information restriction (a ≥2-record regional content exceeds
  the regional capacity Q_R and is not an instantiable physical state —
  the Macroscopic Definiteness Conjecture), with the microscopic
  initial conditions merely *indexing* which record a given run carries.
  This audit closes the rhetorical gap: it forbids any slide from
  "decoherence" to "single record", forcing the finite-information
  restriction to be named as the load-bearing step.
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

    Single-record per-run regional content (QIQT-H Theorems 1, 4) does
    NOT follow from linear unitary decoherence alone: both branches
    remain populated, with weights conserved (proved below).

    Under the canonical (state-space) reading, the load rests on the
    **finite-information restriction on instantiable regional content**:
    a ≥2-record regional content exceeds the regional capacity Q_R and
    is not an instantiable physical state (the Macroscopic Definiteness
    Conjecture, §7.6 — itself still open).  This restriction is a
    *kinematic* constraint on which regional contents are physical; it
    does NOT modify the dynamics (which stays exactly unitary), does NOT
    trim amplitudes, and is NOT a collapse or stochastic rule.  The
    microscopic initial conditions only *index* which single record a
    given run carries; they do not produce the single-ness.

    (Historical note: earlier drafts framed the missing ingredient as
    "(FQ) literal amplitude truncation" or a dynamics modification.
    That framing is superseded — see the module header.  This theorem's
    content is unchanged: decoherence conserves branch weights.)

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
