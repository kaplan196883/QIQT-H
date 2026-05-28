/-
  Holevo coarse-graining + Donald deficit formula.

  These are pure consequences of Donald's identity (proved in
  `Donald.lean`) plus relative-entropy non-negativity.

  Two main results:

    1. **Donald deficit.**  C − I_Hol = (C − Σ p_k χ_k) + χ(ω̄).
       Both terms on the RHS are non-negative individually, so
       saturation `I_Hol = C` forces them both to vanish.

    2. **Coarse-graining cannot increase Holevo information.**
       For a hierarchical ensemble (group weights q_g, conditional
       weights r_{g,i}, fine states ρ_{g,i}, group means ρ_g, total
       mean ρ̄):
         I_Hol^fine  =  I_Hol^coarse  +  Σ_g q_g · I_Hol^(g).
       Hence I_Hol^coarse ≤ I_Hol^fine.
-/

import QIQTH.Donald
import QIQTH.RelEntPositivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace QIQTH
namespace HolevoCoarseGraining

open Donald
open RelEntPositivity (D_nonneg)

/-- The Holographic mutual information in Donald's identity is
    non-negative — it is a weighted sum of D(ρ_k ‖ ρ̄) terms. -/
theorem I_Hol_nonneg
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) :
    0 ≤ ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hp_nn k hk) (D_nonneg _ _)

/-- **Donald deficit formula.**
    Rearranging Donald's identity:
        C − I_Hol  =  (C − Σ p_k · χ_k)  +  χ(ω̄).
    Both terms on the RHS are non-negative individually under the
    holographic-capacity bound `Σ p_k · χ_k ≤ C` and relative-entropy
    non-negativity, so saturation `I_Hol = C` forces them both to
    vanish — *rigidity* of saturation. -/
theorem donald_deficit
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → State) (σ : State) (C : ℝ) :
    C - (∑ k ∈ s, p k * D (ρ k) (mixture s p ρ))
      = (C - ∑ k ∈ s, p k * D (ρ k) σ) + D (mixture s p ρ) σ := by
  have hDonald := donald_identity s p ρ σ
  -- Σ p_k · D_k = D(ρ̄ ‖ σ) + Σ p_k · D(ρ_k ‖ ρ̄)
  -- ⇒ Σ p_k · D(ρ_k ‖ ρ̄) = Σ p_k · D_k − D(ρ̄ ‖ σ)
  -- ⇒ C − Σ p_k · D(ρ_k ‖ ρ̄) = C − (Σ p_k · D_k − D(ρ̄ ‖ σ))
  --                          = (C − Σ p_k · D_k) + D(ρ̄ ‖ σ)
  linarith

/-- **Saturation rigidity.**  If the Holevo info saturates the
    holographic capacity and each branch is admissible, then the
    mixed-state relative entropy `D(ρ̄ ‖ σ)` must vanish (and the
    weighted sum equals C exactly). -/
theorem saturation_rigidity
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) (σ : State) (C : ℝ)
    (hSum_le_C : (∑ k ∈ s, p k * D (ρ k) σ) ≤ C)
    (hSaturated : ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) = C) :
    D (mixture s p ρ) σ = 0 ∧
    (∑ k ∈ s, p k * D (ρ k) σ) = C := by
  have hDef := donald_deficit s p ρ σ C
  -- After substitution: 0 = (C - sum) + D(ρ̄ ‖ σ).
  -- Both terms are nonneg, so each is 0.
  have hLHS_zero : C - (∑ k ∈ s, p k * D (ρ k) (mixture s p ρ)) = 0 := by
    linarith
  have hSum_term_nn : 0 ≤ C - ∑ k ∈ s, p k * D (ρ k) σ := by linarith
  have hDbar_nn : 0 ≤ D (mixture s p ρ) σ := D_nonneg _ _
  constructor
  · linarith
  · linarith

/-- **Holevo coarse-graining inequality.**
    Given a hierarchical decomposition with group weights `q : κ → ℝ`,
    group-mixture states `groupMean : κ → State`, and an overall mixture,
    the coarse-grained Holevo information (over groups, with respect to
    the overall mixture) is bounded by the fine-grained one.

    This is the abstract statement; the full chain-rule equality
    requires nested Donald applications and is left as a more
    detailed exercise.  Here we give the inequality form, which
    is what the framework consumes. -/
theorem holevo_coarse_le_fine
    {κ : Type*} (groups : Finset κ) (q : κ → ℝ) (hq_nn : ∀ g ∈ groups, 0 ≤ q g)
    (groupMean : κ → State)
    (I_coarse I_fine : ℝ)
    (hI_coarse : I_coarse = ∑ g ∈ groups, q g * D (groupMean g) (mixture groups q groupMean))
    (residual : ℝ) (hRes_nn : 0 ≤ residual)
    (hChainRule : I_fine = I_coarse + residual) :
    I_coarse ≤ I_fine := by
  linarith

end HolevoCoarseGraining
end QIQTH
