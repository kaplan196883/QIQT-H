/-
  Finite Shannon entropy + record-layer determinacy.

  Turns the `H_ε ≤ 0` conclusion of DoubleSlit / Theorem 6 into an
  actual *single-record* determinacy statement: if the effective
  entropy of the active-record distribution is below `δ`, then some
  record carries probability at least `exp(-δ)`.

  Begins replacing the axiomatized Fano step of Theorem 6's outer
  chain with finite classical content.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace ShannonFano

/-- Finite Shannon entropy in nats:  H(p) = −Σ p_k · log p_k. -/
noncomputable def H {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ k ∈ s, p k * Real.log (p k)

/-- For a Dirac distribution at index `i₀` (with `s` containing `i₀`),
    the entropy is zero. -/
theorem H_dirac_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i₀ : ι) (h_mem : i₀ ∈ s) :
    H s (fun i => if i = i₀ then (1 : ℝ) else 0) = 0 := by
  unfold H
  rw [Finset.sum_eq_single i₀]
  · simp [Real.log_one]
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd h_mem h

/-- **Quantitative determinacy — PROVED.**  If `H(p) ≤ δ` (in nats), then some
    probability is at least `exp(-δ)`: `max_i p_i ≥ exp(−H(p)) ≥ exp(−δ)`.  This
    is the Rényi-∞ ≤ Shannon relation, the finite-classical Fano-step content
    behind Open Problem 6 (operational distinguishability).  Proof: at the
    maximizer `i₀`, `log p_j ≤ log p_{i₀}` for every `j`, so
    `∑ p_j log p_j ≤ (∑ p_j) log p_{i₀} = log p_{i₀}`, whence
    `H = −∑ p_j log p_j ≥ −log p_{i₀}`; combined with `H ≤ δ` this gives
    `log p_{i₀} ≥ −δ`, i.e. `p_{i₀} ≥ exp(−δ)`. -/
theorem H_bound_imp_max_lb {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_le : ∀ i ∈ s, p i ≤ 1)
    (hSum : ∑ i ∈ s, p i = 1)
    (δ : ℝ) (hH : H s p ≤ δ) :
    ∃ i₀ ∈ s, Real.exp (-δ) ≤ p i₀ := by
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hSum; simp at hSum
    · exact h
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image p hne
  refine ⟨i₀, hi₀, ?_⟩
  have hpos : 0 < p i₀ := by
    by_contra h
    push_neg at h
    have hz : ∀ j ∈ s, p j = 0 := fun j hj =>
      le_antisymm (le_trans (hmax j hj) h) (hp_nn j hj)
    rw [Finset.sum_congr rfl hz] at hSum
    simp at hSum
  have hHge : - Real.log (p i₀) ≤ H s p := by
    unfold H
    have hbound : ∑ j ∈ s, p j * Real.log (p j) ≤ ∑ j ∈ s, p j * Real.log (p i₀) := by
      apply Finset.sum_le_sum
      intro j hj
      rcases eq_or_lt_of_le (hp_nn j hj) with hpj | hpj
      · rw [← hpj]; simp
      · exact mul_le_mul_of_nonneg_left (Real.log_le_log hpj (hmax j hj)) (le_of_lt hpj)
    have hrhs : ∑ j ∈ s, p j * Real.log (p i₀) = Real.log (p i₀) := by
      rw [← Finset.sum_mul, hSum, one_mul]
    rw [hrhs] at hbound
    linarith
  calc Real.exp (-δ) ≤ Real.exp (Real.log (p i₀)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = p i₀ := Real.exp_log hpos

/-- **Single-record certainty from H_ε ≤ 0.**
    The deductive bridge from Theorem 6's `H_ε ≤ 0` to "one record
    has probability 1".  Combines `H_bound_imp_max_lb` (with δ = 0)
    with `Real.exp_zero = 1` and the constraint p_i ≤ 1. -/
theorem single_record_certain {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_le : ∀ i ∈ s, p i ≤ 1)
    (hSum : ∑ i ∈ s, p i = 1)
    (hH_zero : H s p ≤ 0) :
    ∃ i₀ ∈ s, p i₀ = 1 := by
  obtain ⟨i₀, hi₀_mem, hi₀_ge⟩ :=
    H_bound_imp_max_lb s p hp_nn hp_le hSum 0 hH_zero
  refine ⟨i₀, hi₀_mem, ?_⟩
  -- Real.exp 0 = 1, so 1 ≤ p i₀ ≤ 1.
  have h1 : Real.exp (-0 : ℝ) = 1 := by simp
  rw [h1] at hi₀_ge
  exact le_antisymm (hp_le i₀ hi₀_mem) hi₀_ge

/-- **Determinacy from zero entropy — PROVED.**  If `H(p) = 0` (and `p` is a
    distribution with `p_i ≤ 1`), some record has probability exactly `1`.
    Immediate from `single_record_certain` (the `δ = 0` case of the Fano-step
    bound), discharging the former interface axiom. -/
theorem H_zero_imp_dirac {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_le : ∀ i ∈ s, p i ≤ 1)
    (hSum : ∑ i ∈ s, p i = 1) (hH : H s p = 0) :
    ∃ i₀ ∈ s, p i₀ = 1 :=
  single_record_certain s p hp_nn hp_le hSum (le_of_eq hH)

end ShannonFano
end QIQTH
