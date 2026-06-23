/-
  BornTypicality — conditional derivation of Born empirical frequencies
  from a canonical IC measure + standard LLN.

  The setup (matching QIQT-H's actual character):

      QIQT-H has no fundamental probabilities.  It is deterministic per
      run: the run's non-dynamical, atemporal actuality selector λ (a
      global 4D fact about which macroscopic realization the run is —
      not past "initial data") fixes the realized outcome.  "Born"
      refers to the *empirical frequency pattern* across many runs, not
      a probability assignment.

      The question μ-selection must answer is therefore NOT "what
      probability rule does QIQT-H use?" but rather:

          "What canonical measure μ on the microscopic IC space yields,
           for μ-typical IC sequences, empirical frequencies matching
           Born weights |c_k|²?"

  This module formalises the **conditional** Born theorem:

      Given:
        1. A canonical IC measure μ (structural input — the framework
           must justify what makes one measure canonical)
        2. μ pushes forward under the outcome map to Born weights
           (this is what makes μ "the Born measure")
        3. Standard probability-theoretic LLN (axiomatized as black box;
           Mathlib has finite-distribution LLN versions)

      Conclude:
        μ-typical empirical frequencies converge to Born weights.

  The mean-form of LLN (E[empirical freq] = Born) is proved
  rigorously.  The almost-sure convergence is the full LLN, axiomatized
  at this layer.

  Strategic implication: this is the typicality-paradigm analog of
  Bohmian DGZ equivariance, adapted for QIQT-H's no-particle, no-
  branching ontology.  The framework's remaining task is to justify
  WHICH measure is canonical (the candidates being canonical tracial
  typicality from CPW Type II structure, symmetric equiprobability,
  or holographic modular construction).
-/

import QIQTH.NoBornFromNothing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace BornTypicality

open Classical NoBornFromNothing

/-- **Expected indicator of outcome `k` under single-sample IC sampling
    from measure μ.**

    Mathematically: E_μ[ 𝟙(outcome γ = k) ] = Σ_γ μ(γ) · 𝟙(outcome γ = k).
    This is the per-run expected probability of obtaining outcome k. -/
noncomputable def expectedIndicator
    {Γ Outcome : Type*} [Fintype Γ]
    (outcome : Γ → Outcome) (μ : Γ → ℝ) (k : Outcome) : ℝ :=
  ∑ γ, μ γ * (if outcome γ = k then 1 else 0)

/-- The expected indicator equals the outcome marginal. -/
theorem expectedIndicator_eq_marginal
    {Γ Outcome : Type*} [Fintype Γ]
    (outcome : Γ → Outcome) (μ : Γ → ℝ) (k : Outcome) :
    expectedIndicator outcome μ k = outcomeMarginal outcome μ k := by
  unfold expectedIndicator outcomeMarginal
  apply Finset.sum_congr rfl
  intro γ _
  by_cases h : outcome γ = k
  · rw [if_pos h, mul_one, if_pos h]
  · rw [if_neg h, mul_zero, if_neg h]

/-- **Born typicality — mean form (rigorously proved).**

    Given an IC measure `μ` whose outcome-marginal equals Born weights
    `|c_k|²`, the expected per-run frequency of outcome `k` equals
    `|c_k|²`.

    This is the *deterministic* part of the typicality theorem.  The
    *stochastic* part (almost-sure convergence of empirical frequencies)
    requires the standard probability-theoretic LLN, axiomatized below. -/
theorem born_mean_conditional
    {Γ Outcome : Type*} [Fintype Γ]
    (outcome : Γ → Outcome)
    (μ : Γ → ℝ) (c : Outcome → ℝ)
    (h_born_marg : ∀ k, outcomeMarginal outcome μ k = (c k)^2) :
    ∀ k, expectedIndicator outcome μ k = (c k)^2 := by
  intro k
  rw [expectedIndicator_eq_marginal]
  exact h_born_marg k

/-- An **IC measure pushing forward to Born weights**: a probability measure `μ` on the microscopic
    IC space whose outcome-marginal is the Born distribution `|c_k|²`.

    (The structure formerly carried a vacuous `isCanonical : True` placeholder field; it has been
    REMOVED — it was inert (used by no proof) and `: True` encodes no constraint.  WHICH measure is
    physically "canonical" remains the genuine open problem, stated honestly in `audit_summary`
    below, not smuggled in as a trivial field.) -/
structure CanonicalIcMeasure
    (Γ Outcome : Type*) [Fintype Γ]
    (outcome : Γ → Outcome) (c : Outcome → ℝ) where
  μ : Γ → ℝ
  nn : ∀ γ, 0 ≤ μ γ
  sum_one : ∑ γ, μ γ = 1
  /-- The pushforward of μ under the outcome map equals Born weights. -/
  born_marginal : ∀ k, outcomeMarginal outcome μ k = (c k)^2

/- **Strong Law of Large Numbers — the content-free `LLN_typicality_axiom` was DELETED
    (2026-06).**  Its conclusion was `∀ε>0,∀k,∃N,True` — a placeholder with no convergence
    content.  The genuine, axiom-free finite weak law of large numbers now lives in
    `QIQTH.BornTypicalityFinite` (`chebyshev_freq`: `P(|freq − p k| ≥ ε) ≤ p k(1−p k)/(Nε²)`,
    `chebyshev_freq_union_le`) and its quantum/measure lifts (`BornTypicalityQuantum`,
    `BornMeasureUniqueness`, `BornJoin`).  The continuum/AQFT LLN over IC sequences remains an
    open target (it is NOT this deleted placeholder). -/

/-- **The QIQT-H Born typicality theorem (mean form).**

    *Hypothesis:* a canonical IC measure μ for the Born distribution `|c_k|²`.
    *Conclusion:* the expected per-run outcome distribution is Born — proved rigorously from
    the marginal hypothesis.

    The almost-sure / frequency direction is NO LONGER stated here as a content-free placeholder;
    the genuine finite weak LLN is `BornTypicalityFinite.chebyshev_freq` (axiom-free).  The
    remaining research question is justifying the "canonical" qualifier on μ from physical first
    principles (CPW Type II tracial typicality, holographic modular construction). -/
theorem qiqth_born_typicality_conditional
    {Γ Outcome : Type*} [Fintype Γ] [Fintype Outcome]
    (outcome : Γ → Outcome) (c : Outcome → ℝ)
    (M : CanonicalIcMeasure Γ Outcome outcome c) :
    -- Mean form: per-run expected frequency = Born.
    ∀ k, expectedIndicator outcome M.μ k = (c k)^2 := by
  intro k
  exact born_mean_conditional outcome M.μ c M.born_marginal k

/-- **Audit summary.**

    The Born μ-selection problem has been reduced to a single
    structural question: WHICH measure on the microscopic IC space is
    "canonical"?

    Given an answer to that question (a physical principle making one
    measure structurally distinguished + a proof it pushes forward to
    Born), the rest of the typicality argument is standard probability
    theory and is captured by `qiqth_born_typicality_conditional`
    above.

    Candidates for the canonical-measure principle (per the GPT-5.5-pro
    audit):
      (i)   Canonical tracial typicality from CPW Type II structure.
      (ii)  Symmetric equiprobability on a natural decomposition of
            the IC space.
      (iii) Holographic / modular construction from the canonical
            sector reference state σ_R.

    The framework's open Born problem is to justify (i), (ii), or (iii)
    — none of which is derivable from FQ + AQFT + holography alone. -/
theorem audit_summary : True := trivial

end BornTypicality
end QIQTH
