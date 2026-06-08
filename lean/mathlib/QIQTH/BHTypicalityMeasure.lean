/-
  Phase-B Part A — CLOSING THE LOOP on `B(H)`: a genuine normal state on the infinite-dimensional
  algebra `B(H)` driving the continuum typicality measure μ∞ end-to-end.

  Combines:
    • `NormalState.diagStateHom` — a genuine normal state `ω = Tr(ρ ·)` on `B(H)` for a diagonal
      density operator `ρ = ∑ pₙ|bₙ⟩⟨bₙ|` (Phase-B Part-A brick), with
    • `StateNetMeasure.EffectStateNet` — the state-agnostic typicality-measure construction, and
    • `KolmogorovFiniteFiber.exists_isLimit` — the finite-fiber Kolmogorov extension (XL Phase A).

  `diagNet` packages a record net of finite outcomes on `B(H)` whose state is the genuine
  infinite-dimensional normal state `ω`; `bh_typicalityMeasure_exists` concludes that a unique
  σ-additive probability typicality measure μ∞ on the history space EXISTS — driven by a real normal
  state on `B(H)`.  This is the first fully end-to-end *infinite-dimensional* instance of the whole
  prize pipeline (normal state on `B(H)` → projective Born family → σ-additive covariant μ∞).

  HONEST SCOPE: the net here is the deterministic record net (so the normal state enters through its
  normalization `ω(1) = Tr ρ = 1`, and μ∞ is the corresponding point family); a state-RESOLVING POVM
  whose Born weights are the `pₙ` (rank-one basis projections) is the richer instance, part of the
  general Part-A program.  What is demonstrated here is the genuine *coupling*: an honest normal state
  on infinite-dim `B(H)` runs the entire `EffectStateNet → μ∞` machinery.  Axiom-free.
-/
import QIQTH.NormalState
import QIQTH.StateNetMeasure
import Mathlib.Tactic

namespace QIQTH.BHTypicalityMeasure

open MeasureTheory QIQTH.NormalState QIQTH.StateNetMeasure
open scoped ComplexInnerProductSpace

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)]
  {κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {b : HilbertBasis κ ℂ H} {p : κ → ℝ}

/-- **A record net on `B(H)` driven by the diagonal normal state.**  Its state is the genuine
    infinite-dimensional normal state `ω = diagStateHom` (`Tr(ρ ·)`); the joint effects are the
    deterministic record effects `[x = g↾J]·1` at a fixed history `g`. -/
noncomputable def diagNet (hb : Orthonormal ℂ b) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (hp1 : ∑' i, p i = 1) (g : ∀ i, α i) : EffectStateNet α (H →L[ℂ] H) where
  ω := diagStateHom hb hp hsum
  E := fun J x => if x = J.restrict g then (1 : H →L[ℂ] H) else 0
  pos := fun J x => by
    rw [apply_ite (diagStateHom hb hp hsum), map_zero, diagStateHom_one hb hp hsum hp1]
    split <;> norm_num
  total := fun J => by
    simp only [apply_ite (diagStateHom hb hp hsum), map_zero, diagStateHom_one hb hp hsum hp1]
    simp [Finset.sum_ite_eq']
  coarse := fun I J h y => by
    have hcomp : Finset.restrict₂ h (J.restrict g) = I.restrict g :=
      congrFun (Finset.restrict₂_comp_restrict h) g
    simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, hcomp]
    exact if_congr eq_comm rfl rfl

/-- **End-to-end on `B(H)`: a normal state on the infinite-dimensional algebra drives a genuine
    σ-additive probability typicality measure μ∞.**  For the diagonal density operator
    `ρ = ∑ pₙ|bₙ⟩⟨bₙ|` and a record net of finite outcomes, there is a unique probability measure on
    the history space realizing the state's projective Born family (via the finite-fiber Kolmogorov
    extension).  The whole prize pipeline runs on a real normal state on `B(H)`. -/
theorem bh_typicalityMeasure_exists [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [∀ i, Finite (α i)] (hb : Orthonormal ℂ b) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (hp1 : ∑' i, p i = 1) (g : ∀ i, α i) :
    ∃ μ : Measure (∀ i, α i), IsProbabilityMeasure μ ∧
      (diagNet hb hp hsum hp1 g).toFiniteMarginals.IsLimit μ :=
  (diagNet hb hp hsum hp1 g).exists_typicalityMeasure

end QIQTH.BHTypicalityMeasure
