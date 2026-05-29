/-
  BranchLedger — the branch-summed cost bound is NOT a standard
  entropy/holographic consequence.

  GPT-5.5-pro audit:

      The quantity I_Σ^ε := Σ_k c_R(r_k) (unweighted branch-summed
      record cost) is much stronger than ordinary Shannon, Holevo,
      and holographic-capacity bounds.  N orthogonal records with
      uniform distribution and unit cost have Shannon entropy log N
      but branch-summed cost N — much larger.

      Thus  I_Σ^ε ≤ Q_R  is an ADDITIONAL framework postulate beyond
      standard holography, not a derived consequence.

  This module formalizes the counterexample concretely (binary uniform
  distribution), confirming that branch-summed bounds must be flagged
  as a separate framework commitment.

  The QIQT-H paper (QIQT_Math §9A.3) already correctly identifies the
  branch-summed bound as "not a theorem of standard holography ... but
  a *strengthening* of the holographic principle that the framework
  adopts as a superselection rule."  This module is the formal
  confirmation of that admission, plus an explicit ledger postulate
  namespace that callers must invoke explicitly.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace BranchLedger

/-- Shannon entropy of a finite probability distribution (in nats). -/
noncomputable def Shannon {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)

/-- Branch-summed cost: unweighted sum of per-record costs. -/
def branchSummedCost {ι : Type*} (s : Finset ι) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ s, c i

/-- Auxiliary:  log 2 < 2.  (Since 2 < e^2.) -/
private theorem log_two_lt_two : Real.log 2 < 2 := by
  have h_2_lt_exp2 : (2 : ℝ) < Real.exp 2 := by
    have h_add := Real.add_one_lt_exp (by norm_num : (2:ℝ) ≠ 0)
    linarith
  have h_log := Real.log_lt_log (by norm_num : (0:ℝ) < 2) h_2_lt_exp2
  rwa [Real.log_exp] at h_log

/-- **Counterexample: branch-summed cost is NOT bounded by Shannon entropy.**

    With binary uniform distribution and unit per-record cost:
      • Shannon entropy = log 2 ≈ 0.693
      • Branch-summed cost = 2
    Hence branch-summed cost > Shannon entropy.  A holographic-style
    cap on the latter does NOT cap the former. -/
theorem branchSummed_not_bounded_by_Shannon :
    Shannon (Finset.univ : Finset (Fin 2)) (fun _ => 1/2) <
    branchSummedCost (Finset.univ : Finset (Fin 2)) (fun _ => 1) := by
  -- Compute branchSummedCost = 1 + 1 = 2.
  have h_cost : branchSummedCost (Finset.univ : Finset (Fin 2)) (fun _ => (1:ℝ)) = 2 := by
    unfold branchSummedCost
    rw [Fin.sum_univ_two]; norm_num
  rw [h_cost]
  -- Compute Shannon = -(1/2 · log(1/2) + 1/2 · log(1/2)) = -log(1/2) = log 2.
  have h_log_half : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have h_shannon :
      Shannon (Finset.univ : Finset (Fin 2)) (fun _ => (1/2 : ℝ)) = Real.log 2 := by
    unfold Shannon
    rw [Fin.sum_univ_two]
    show -((1/2 : ℝ) * Real.log (1/2) + (1/2 : ℝ) * Real.log (1/2)) = Real.log 2
    rw [h_log_half]; ring
  rw [h_shannon]
  exact log_two_lt_two

/-- **Existence form** for the audit. -/
theorem exists_Shannon_lt_branchSummed :
    ∃ (N : ℕ) (p : Fin N → ℝ) (c : Fin N → ℝ),
      0 < N ∧ Shannon Finset.univ p < branchSummedCost Finset.univ c :=
  ⟨2, fun _ => 1/2, fun _ => 1, by norm_num, branchSummed_not_bounded_by_Shannon⟩

/- **Ledger postulate (namespace).**  The branch-summed bound is here
   flagged as an EXPLICIT additional framework commitment, separated
   from standard relative-entropy / Holevo / Shannon bounds. -/
namespace ExtraPostulate

/-- The branch-summed bound: total record cost on a region is bounded
    by its holographic capacity.  Framework-specific postulate beyond
    standard holography. -/
def BranchLedgerBound {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Q : ℝ) : Prop :=
  branchSummedCost s c ≤ Q

end ExtraPostulate

end BranchLedger
end QIQTH
