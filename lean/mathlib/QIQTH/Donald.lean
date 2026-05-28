/-
  Derivation of Donald's identity for relative entropy.

  Donald's identity (informal):
      Σ_k p_k · D(ρ_k ‖ σ) = D(rhoBar ‖ σ) + Σ_k p_k · D(ρ_k ‖ rhoBar)
  where rhoBar := Σ_k p_k ρ_k.

  In `Theorem6.lean` we take Donald's identity as a *field* of
  `BranchData`.  This file *derives* it from three primitive
  axioms about relative entropy, entropy, and cross-entropy:

    (A1)  D(ρ ‖ σ)              = crossEnt(ρ, σ) − H(ρ)
    (A2)  crossEnt(Σ p_k ρ_k, σ) = Σ p_k · crossEnt(ρ_k, σ)
    (A3)  crossEnt(ρ, ρ)        = H(ρ)

  These three are the standard properties of the trace-based
  decomposition  D(ρ ‖ σ) = tr(ρ log ρ) − tr(ρ log σ),  where:
    · crossEnt(ρ, σ) := −tr(ρ log σ)   is linear in ρ            ⇒ (A2)
    · H(ρ)            := −tr(ρ log ρ)   is the von Neumann entropy
    · crossEnt(ρ, ρ)  = −tr(ρ log ρ) = H(ρ)                       ⇒ (A3)
    · D(ρ ‖ σ)        = tr(ρ log ρ − ρ log σ) = crossEnt(ρ,σ) − H(ρ) ⇒ (A1)

  In the Araki / Type-II setting, the same decomposition holds
  in the modular sense (Connes-Stinespring / spatial derivatives),
  so this file applies to the QIQT-H Donald identity for Araki
  relative entropy on local algebras.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace QIQTH
namespace Donald

/-- Abstract state type. Concretely: a normal positive functional on
    a von Neumann algebra; for the QIQT-H paper, on a local algebra
    Â(R) in the Araki/Type-II sense. -/
axiom State : Type

/-- Relative entropy:  D(ρ ‖ σ).  Concretely, Araki relative entropy
    on the regional algebra. -/
axiom D : State → State → ℝ

/-- Entropy of a state:  H(ρ) = −tr(ρ log ρ). -/
axiom H : State → ℝ

/-- Cross-entropy of two states:  crossEnt(ρ, σ) = −tr(ρ log σ).
    Linear in its first argument. -/
axiom crossEnt : State → State → ℝ

/-- Mixture of a family of states with given weights.
    Concretely: rhoBar = Σ p_k ρ_k. -/
axiom mixture {ι : Type*} (s : Finset ι) (p : ι → ℝ) (ρ : ι → State) : State

/-- **(A1)** Relative entropy = cross-entropy − entropy. -/
axiom D_eq_crossEnt_sub_H (ρ σ : State) : D ρ σ = crossEnt ρ σ - H ρ

/-- **(A2)** Cross-entropy is linear in its first argument. -/
axiom crossEnt_mixture {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → State) (σ : State) :
    crossEnt (mixture s p ρ) σ = ∑ k ∈ s, p k * crossEnt (ρ k) σ

/-- **(A3)** Cross-entropy of a state with itself = its entropy. -/
axiom crossEnt_self (ρ : State) : crossEnt ρ ρ = H ρ

/-- **Donald's identity** (derived, no further axioms).

    For any branch decomposition with weights `p : ι → ℝ` on a finite
    index set `s`, branch states `ρ : ι → State`, and reference state
    `σ`, the weighted sum of single-branch relative entropies equals
    the mixed-state relative entropy plus the Holevo-like quantity:

        Σ_k p_k · D(ρ_k ‖ σ)  =  D(rhoBar ‖ σ) + Σ_k p_k · D(ρ_k ‖ rhoBar),

    where rhoBar := mixture(p, ρ). -/
theorem donald_identity
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → State) (σ : State) :
    ∑ k ∈ s, p k * D (ρ k) σ
      = D (mixture s p ρ) σ + ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) := by
  set rhoBar := mixture s p ρ with hrhoBar
  -- Introduce abbreviations for the recurring sums.
  set CES : ℝ := ∑ k ∈ s, p k * crossEnt (ρ k) σ with hCES
  set CER : ℝ := ∑ k ∈ s, p k * crossEnt (ρ k) rhoBar with hCER
  set PH  : ℝ := ∑ k ∈ s, p k * H (ρ k) with hPH
  -- Linearity (A2) applied twice.
  have h_lin_σ : crossEnt rhoBar σ = CES := crossEnt_mixture s p ρ σ
  have h_lin_rhoBar : crossEnt rhoBar rhoBar = CER := crossEnt_mixture s p ρ rhoBar
  -- Self-cross-entropy (A3).
  have h_self  : crossEnt rhoBar rhoBar = H rhoBar := crossEnt_self rhoBar
  -- Expand LHS and RHS using (A1).
  have hLHS : ∑ k ∈ s, p k * D (ρ k) σ = CES - PH := by
    simp only [D_eq_crossEnt_sub_H, mul_sub, Finset.sum_sub_distrib, hCES, hPH]
  have hRHS :
      D rhoBar σ + ∑ k ∈ s, p k * D (ρ k) rhoBar
        = (crossEnt rhoBar σ - H rhoBar) + (CER - PH) := by
    simp only [D_eq_crossEnt_sub_H, mul_sub, Finset.sum_sub_distrib, hCER, hPH]
  rw [hLHS, hRHS]
  -- Close the algebraic identity with the three crossEnt facts.
  linarith [h_lin_σ, h_lin_rhoBar, h_self]

end Donald
end QIQTH
