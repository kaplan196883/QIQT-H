/-
  Donald's identity for relative entropy — over a `DonaldSystem` typeclass.

  Donald's identity (informal):
      Σ_k p_k · D(ρ_k ‖ σ) = D(rhoBar ‖ σ) + Σ_k p_k · D(ρ_k ‖ rhoBar)
  where rhoBar := Σ_k p_k ρ_k.

  Formerly this file declared `State/D/H/crossEnt/mixture` as opaque AXIOMS plus three
  property axioms (A1–A3).  Those eight axioms are now the fields of a typeclass
  `DonaldSystem`, and `donald_identity` is a THEOREM about any `DonaldSystem` — derived
  from the three structural identities:

    (A1)  D(ρ ‖ σ)               = crossEnt(ρ, σ) − H(ρ)
    (A2)  crossEnt(Σ p_k ρ_k, σ) = Σ p_k · crossEnt(ρ_k, σ)
    (A3)  crossEnt(ρ, ρ)         = H(ρ)

  These are the standard properties of the trace decomposition
  `D(ρ‖σ) = tr(ρ log ρ) − tr(ρ log σ)` with `crossEnt(ρ,σ) := −tr(ρ log σ)`,
  `H(ρ) := −tr(ρ log ρ)`.  The typeclass is DISCHARGED for the genuine finite-dimensional
  model by `QIQTH.QuantumEntropy.instDonaldSystemHermitianMat` (Hermitian matrices), so the
  former axioms are now derived facts about a concrete realizable interface, not assumptions.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace QIQTH

/-- **A Donald relative-entropy system** on a state type `State`: relative entropy `D`,
    entropy `H`, cross-entropy `crossEnt`, and `mixture` (the weighted combination), satisfying
    the three Donald structural identities (A1–A3).  This replaces the former opaque axioms
    `Donald.State/D/H/crossEnt/mixture` + the three identity axioms; it is discharged for
    finite-dimensional density/Hermitian matrices (`QuantumEntropy.instDonaldSystemHermitianMat`). -/
class DonaldSystem (State : Type) where
  /-- relative entropy `D(ρ‖σ)`. -/
  D : State → State → ℝ
  /-- entropy `H(ρ) = −tr(ρ log ρ)`. -/
  H : State → ℝ
  /-- cross-entropy `crossEnt(ρ,σ) = −tr(ρ log σ)`. -/
  crossEnt : State → State → ℝ
  /-- the weighted mixture `Σ p_k ρ_k`. -/
  mixture : {ι : Type} → Finset ι → (ι → ℝ) → (ι → State) → State
  /-- **(A1)** `D(ρ‖σ) = crossEnt(ρ,σ) − H(ρ)`. -/
  D_eq_crossEnt_sub_H : ∀ ρ σ, D ρ σ = crossEnt ρ σ - H ρ
  /-- **(A2)** cross-entropy is linear in its first argument. -/
  crossEnt_mixture : ∀ {ι : Type} (s : Finset ι) (p : ι → ℝ) (ρ : ι → State) (σ : State),
    crossEnt (mixture s p ρ) σ = ∑ k ∈ s, p k * crossEnt (ρ k) σ
  /-- **(A3)** `crossEnt(ρ,ρ) = H(ρ)`. -/
  crossEnt_self : ∀ ρ, crossEnt ρ ρ = H ρ

namespace Donald

open DonaldSystem

variable {State : Type} [DonaldSystem State]

/-- **Donald's identity** (a THEOREM, no axioms beyond the `DonaldSystem` structural identities).

    For any branch decomposition with weights `p : ι → ℝ` on a finite index set `s`, branch states
    `ρ : ι → State`, and reference state `σ`, the weighted sum of single-branch relative entropies
    equals the mixed-state relative entropy plus the Holevo-like quantity:

        Σ_k p_k · D(ρ_k ‖ σ)  =  D(rhoBar ‖ σ) + Σ_k p_k · D(ρ_k ‖ rhoBar),  rhoBar := mixture p ρ. -/
theorem donald_identity
    {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → State) (σ : State) :
    ∑ k ∈ s, p k * D (ρ k) σ
      = D (mixture s p ρ) σ + ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) := by
  set rhoBar := mixture s p ρ with hrhoBar
  set CES : ℝ := ∑ k ∈ s, p k * crossEnt (ρ k) σ with hCES
  set CER : ℝ := ∑ k ∈ s, p k * crossEnt (ρ k) rhoBar with hCER
  set PH  : ℝ := ∑ k ∈ s, p k * H (ρ k) with hPH
  have h_lin_σ : crossEnt rhoBar σ = CES := crossEnt_mixture s p ρ σ
  have h_lin_rhoBar : crossEnt rhoBar rhoBar = CER := crossEnt_mixture s p ρ rhoBar
  have h_self  : crossEnt rhoBar rhoBar = H rhoBar := crossEnt_self rhoBar
  have hLHS : ∑ k ∈ s, p k * D (ρ k) σ = CES - PH := by
    simp only [D_eq_crossEnt_sub_H, mul_sub, Finset.sum_sub_distrib, hCES, hPH]
  have hRHS :
      D rhoBar σ + ∑ k ∈ s, p k * D (ρ k) rhoBar
        = (crossEnt rhoBar σ - H rhoBar) + (CER - PH) := by
    simp only [D_eq_crossEnt_sub_H, mul_sub, Finset.sum_sub_distrib, hCER, hPH]
  rw [hLHS, hRHS]
  linarith [h_lin_σ, h_lin_rhoBar, h_self]

end Donald
end QIQTH
