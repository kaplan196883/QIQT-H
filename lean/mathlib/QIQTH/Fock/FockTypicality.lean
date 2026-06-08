/-
  F6 (first increment) — CLOSING THE LOOP on the genuine continuum Fock space.

  The covariant typicality-measure pipeline (`StateNetMeasure.EffectStateNet` +
  `KolmogorovFiniteFiber` Kolmogorov extension), already proven state-agnostic, is here driven by the
  genuine **quasifree vacuum state** `ω₀` (`VacuumState.lean`, F3) on the genuine **bosonic Fock space**
  `Fock H` (`FockSpace.lean`, F2) over the one-particle space `H` (`OneParticle.lean`, F1).

  `fockVacuumNet` packages a finite-outcome record net on `B(Fock H)` whose state is `ω₀ = Re⟪Ω,·Ω⟫`;
  `fock_typicalityMeasure_exists` concludes that a unique σ-additive probability typicality measure μ∞
  on the history space EXISTS.  This is the first end-to-end instance of the whole prize pipeline on the
  *continuum free-field Fock space with the vacuum state* — the exact analogue of `BHTypicalityMeasure`
  (which ran it on a generic `B(H)` normal state), now on the relativistic free field's Fock space.

  HONEST SCOPE: as in `BHTypicalityMeasure`, the net here is the deterministic record net (the state
  enters through its normalization `ω₀(1) = ⟪Ω,Ω⟫ = 1`).  What is demonstrated is the genuine coupling:
  the quasifree vacuum state on the continuum Fock space runs the entire `EffectStateNet → μ∞` machinery.
  Boost-covariance of μ∞ (the full F6 prize) is the next increment.  Axiom-free.
-/
import QIQTH.Fock.VacuumState
import QIQTH.StateNetMeasure
import Mathlib.Tactic

namespace QIQTH.Fock

open MeasureTheory QIQTH.StateNetMeasure

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A record net on `B(Fock H)` driven by the quasifree vacuum state `ω₀`.**  Its state is
    `ω₀ = Re⟪Ω, · Ω⟫` on the genuine continuum Fock space; the joint effects are the deterministic
    record effects `[x = g↾J]·1` at a fixed history `g`. -/
noncomputable def fockVacuumNet (g : ∀ i, α i) :
    EffectStateNet α (Fock H →L[ℂ] Fock H) where
  ω := vacuumStateHom
  E := fun J x => if x = J.restrict g then (1 : Fock H →L[ℂ] Fock H) else 0
  pos := fun J x => by
    rw [apply_ite vacuumStateHom, map_zero, vacuumStateHom_one]
    split <;> norm_num
  total := fun J => by
    simp only [apply_ite vacuumStateHom, map_zero, vacuumStateHom_one]
    simp [Finset.sum_ite_eq']
  coarse := fun I J h y => by
    have hcomp : Finset.restrict₂ h (J.restrict g) = I.restrict g :=
      congrFun (Finset.restrict₂_comp_restrict h) g
    simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, hcomp]
    exact if_congr eq_comm rfl rfl

/-- **End-to-end on the genuine continuum Fock space: the quasifree vacuum state drives a σ-additive
    probability typicality measure μ∞.**  For the vacuum state `ω₀` on `B(Fock H)` and a record net of
    finite outcomes, there is a unique probability measure on the history space realizing the state's
    projective Born family (via the finite-fiber Kolmogorov extension).  The whole prize pipeline runs
    on the quasifree vacuum state of the relativistic free field's Fock space. -/
theorem fock_typicalityMeasure_exists [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [∀ i, Finite (α i)] (g : ∀ i, α i) :
    ∃ μ : Measure (∀ i, α i), IsProbabilityMeasure μ ∧
      (fockVacuumNet (H := H) g).toFiniteMarginals.IsLimit μ :=
  (fockVacuumNet g).exists_typicalityMeasure

end QIQTH.Fock
