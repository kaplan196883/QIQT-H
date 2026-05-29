/-
  NoBornFromNothing — the central QIQT-H Born audit.

  GPT-5.5-pro fourth audit:

      The framework's structural axioms ((FQ), microcausality,
      Donald, holographic bound) do NOT determine the empirical
      frequencies of macroscopic outcomes.  For ANY probability
      distribution `p` on the outcome space (and any surjective
      outcome map from microscopic IC space to outcomes), there
      exists a microscopic probability measure `μ` whose push-forward
      under the outcome map equals `p`.

      In particular, Born statistics `p_k = |c_k|²` are realizable
      under SOME choice of `μ`, but so is any other distribution.
      The framework's Theorem 5 (Born from typicality) requires
      an *independent* specification of which `μ` is the physically
      realized one.  μ-selection is the load-bearing problem.

  Strategic implication: QIQT-H's Born claim is conditional on
  μ-selection, not derived from holographic / FQ structure alone.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace NoBornFromNothing

open Classical

/-- Outcome-marginal of a microscopic measure: probability of obtaining
    outcome `k` is the sum of `μ` over all microscopic IC's with that
    outcome. -/
noncomputable def outcomeMarginal {Γ Outcome : Type*}
    [Fintype Γ]
    (outcome : Γ → Outcome) (μ : Γ → ℝ) (k : Outcome) : ℝ :=
  ∑ γ, if outcome γ = k then μ γ else 0

/-- **NoBornFromNothing — universal realizability (marginal form).**

    For any target outcome distribution `p` and any surjective
    outcome map `outcome : Γ → Outcome`, there exists a microscopic
    non-negative measure `μ` whose outcome-marginal equals `p`.

    Construction: pick a section `s : Outcome → Γ` (right-inverse of
    `outcome`), and place mass `p k` on `s k` for each outcome `k`. -/
theorem exists_marginal_realizing
    {Γ Outcome : Type*} [Fintype Γ]
    [Fintype Outcome]
    (outcome : Γ → Outcome) (h_surj : Function.Surjective outcome)
    (p : Outcome → ℝ) (hp_nn : ∀ k, 0 ≤ p k) :
    ∃ μ : Γ → ℝ,
      (∀ γ, 0 ≤ μ γ) ∧
      (∀ k, outcomeMarginal outcome μ k = p k) := by
  choose s hs using h_surj
  refine ⟨fun γ => if γ = s (outcome γ) then p (outcome γ) else 0, ?_, ?_⟩
  · -- Non-negativity.
    intro γ
    show 0 ≤ if γ = s (outcome γ) then p (outcome γ) else 0
    by_cases h : γ = s (outcome γ)
    · rw [if_pos h]; exact hp_nn _
    · rw [if_neg h]
  · -- Marginal at k equals p k.  Only γ = s k contributes.
    intro k
    unfold outcomeMarginal
    have h_inner_at_sk : (s k : Γ) = s (outcome (s k)) := by rw [hs k]
    rw [Finset.sum_eq_single (s k)]
    · -- At γ = s k: outcome (s k) = k, inner if true, value p k.
      have h_o : outcome (s k) = k := hs k
      show (if outcome (s k) = k
              then (if s k = s (outcome (s k)) then p (outcome (s k)) else 0)
              else 0) = p k
      rw [if_pos h_o, if_pos h_inner_at_sk, h_o]
    · -- For γ ≠ s k: contribution is 0.
      intro γ _ hne
      show (if outcome γ = k
              then (if γ = s (outcome γ) then p (outcome γ) else 0)
              else 0) = 0
      by_cases h_o : outcome γ = k
      · -- outcome γ = k.  Inner condition γ = s (outcome γ) = s k.  But γ ≠ s k.
        rw [if_pos h_o]
        have h_inner : γ ≠ s (outcome γ) := by rw [h_o]; exact hne
        rw [if_neg h_inner]
      · rw [if_neg h_o]
    · -- s k is in univ.
      intro h
      exact absurd (Finset.mem_univ (s k)) h

/-- **NoBornFromNothing — universal realizability (full probability form).**

    Combining `exists_marginal_realizing` with `Σ_k p k = 1` gives a
    full probability distribution: μ is non-negative, sums to 1, and
    has marginal equal to p.

    Strategic point: ANY distribution p is realizable.  μ-selection
    is therefore the load-bearing input to the framework's Born claim. -/
theorem exists_probability_realizing
    {Γ Outcome : Type*} [Fintype Γ]
    [Fintype Outcome]
    (outcome : Γ → Outcome) (h_surj : Function.Surjective outcome)
    (p : Outcome → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k, p k = 1) :
    ∃ μ : Γ → ℝ,
      (∀ γ, 0 ≤ μ γ) ∧
      (∑ γ, μ γ = 1) ∧
      (∀ k, outcomeMarginal outcome μ k = p k) := by
  obtain ⟨μ, h_nn, h_marg⟩ :=
    exists_marginal_realizing outcome h_surj p hp_nn
  refine ⟨μ, h_nn, ?_, h_marg⟩
  -- Sum of μ equals sum of marginals equals sum of p, equals 1.
  have h_sum_marg : ∑ k, outcomeMarginal outcome μ k = ∑ γ, μ γ := by
    unfold outcomeMarginal
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    -- ∑_k (if outcome γ = k then μ γ else 0) = μ γ
    -- Only k = outcome γ contributes.
    rw [Finset.sum_eq_single (outcome γ)]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h_marg_eq : ∑ k, outcomeMarginal outcome μ k = ∑ k, p k :=
    Finset.sum_congr rfl (fun k _ => h_marg k)
  linarith [h_sum_marg, h_marg_eq, hp_sum]

/-- **Born specialization.**  Apply the universal realizability theorem
    with `p k := |c k|²` (Born weights) to get: there exists a microscopic
    measure `μ_Born` whose outcome-marginal equals the Born distribution.
    This is the framework's Theorem 5, stated *conditionally* — it asserts
    only that the Born distribution is *one* of the realizable ones, not
    that it is *the* physically realized one. -/
theorem born_distribution_realizable_conditional
    {Γ Outcome : Type*} [Fintype Γ]
    [Fintype Outcome]
    (outcome : Γ → Outcome) (h_surj : Function.Surjective outcome)
    (c : Outcome → ℝ)
    (hc_nn_sq : ∀ k, 0 ≤ (c k)^2) (hc_norm : ∑ k, (c k)^2 = 1) :
    ∃ μ : Γ → ℝ,
      (∀ γ, 0 ≤ μ γ) ∧
      (∑ γ, μ γ = 1) ∧
      (∀ k, outcomeMarginal outcome μ k = (c k)^2) :=
  exists_probability_realizing outcome h_surj
    (fun k => (c k)^2) hc_nn_sq hc_norm

/-- **No-Born-from-nothing corollary.**

    For ANY non-Born target distribution, there is *also* a microscopic
    measure realising it.  Hence the structural axioms cannot distinguish
    Born from any other distribution; the framework's selection of
    `μ_Born` requires an external physical principle. -/
theorem any_anti_born_realizable
    {Γ Outcome : Type*} [Fintype Γ]
    [Fintype Outcome]
    (outcome : Γ → Outcome) (h_surj : Function.Surjective outcome) :
    ∀ (p : Outcome → ℝ), (∀ k, 0 ≤ p k) → (∑ k, p k = 1) →
      ∃ μ : Γ → ℝ, ∀ k, outcomeMarginal outcome μ k = p k := by
  intro p hp_nn hp_sum
  obtain ⟨μ, _, _, h_marg⟩ :=
    exists_probability_realizing outcome h_surj p hp_nn hp_sum
  exact ⟨μ, h_marg⟩

end NoBornFromNothing
end QIQTH
