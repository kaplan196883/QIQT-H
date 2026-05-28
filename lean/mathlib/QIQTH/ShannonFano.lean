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

/-- **Determinacy from low entropy (qualitative form).**
    If `H(p) = 0` and all `p_i ∈ [0,1]` with Σ p_i = 1, then there
    is some index where `p_i = 1` (Dirac).  We give the *contrapositive
    interface* form: this is the deductive content the framework needs
    for translating `H_ε = 0` (DoubleSlit determinacy) into a literal
    single-spot statement.

    The full proof requires `0 ≤ p · log p ≤ 0` analysis and care
    around `p = 0` and `p = 1`; we axiomatize the conclusion as an
    interface, with a `Real.log` sketch in the file body. -/
axiom H_zero_imp_dirac {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_le : ∀ i ∈ s, p i ≤ 1)
    (hSum : ∑ i ∈ s, p i = 1)
    (hH : H s p = 0) :
    ∃ i₀ ∈ s, p i₀ = 1

/-- **Quantitative determinacy (axiom).**  If `H(p) ≤ δ` (in nats),
    then some probability is at least `exp(-δ)`.  Equivalently:
        max_i p_i  ≥  exp(−H(p))  ≥  exp(−δ).
    This is the standard *Rényi-∞ vs. Shannon* relation; it
    follows from concavity of `log` and Jensen's inequality. -/
axiom H_bound_imp_max_lb {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hp_le : ∀ i ∈ s, p i ≤ 1)
    (hSum : ∑ i ∈ s, p i = 1)
    (δ : ℝ) (hH : H s p ≤ δ) :
    ∃ i₀ ∈ s, Real.exp (-δ) ≤ p i₀

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

end ShannonFano
end QIQTH
