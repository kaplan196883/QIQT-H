/-
  XL-step **Phase B** (the formalizable core): the covariant typicality measure is STATE-AGNOSTIC.

  Phase A built the σ-additive covariant measure μ∞ from the matrix Born functional `Re tr(ρ ·)`.
  Phase B's mathematical content (B1) is that the SAME construction works for ANY positive normalized
  linear functional `ω` on a net of compatible local effects — not just finite-dim density matrices.
  An `EffectStateNet` packages exactly this: an additive state `ω : A →+ ℝ` on an effect monoid `A`,
  a `Finset ι`-indexed family of joint effects `E_J` with positivity, normalization, and the
  coarse-graining identity `E_I y = ∑_{x↾I = y} E_J x` (the operational content of a consistent family
  of COMPATIBLE measurements — the Fine/Bell constraint: the index must be a single decoherent
  framework).  Linearity of `ω` makes the Born weights `ω(E_J ·)` automatically a Kolmogorov-consistent
  probability family (`toFiniteMarginals`), so by the finite-fiber Kolmogorov extension (A2b) the
  σ-additive typicality measure μ∞ EXISTS for any such state (`exists_typicalityMeasure`).

  HONEST BOUNDARY (Phase B physics, CITED — not formalized, not new axioms): that such a normal state
  ω actually arises from a relativistic QFT — a normal state on a **Type III₁** local von Neumann
  algebra with Poincaré/Bisognano–Wichmann covariance — is the operator-algebra continuum frontier
  (Mathlib lacks constructive normal states / predual; Type III₁-ness is Buchholz–Wichmann).  This
  file formalizes the state-agnostic CONSTRUCTION; the existence of the physical state is the cited gap.

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import QIQTH.FiniteMarginals
import QIQTH.KolmogorovFiniteFiber
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace QIQTH.StateNetMeasure

open MeasureTheory BigOperators
open scoped ENNReal

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} {A : Type*} [AddCommMonoid A]
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)]

/-- A net of compatible local measurements under a state: an additive state `ω : A →+ ℝ` on an effect
    monoid `A`, with joint effects `E J` for each finite context `J : Finset ι`, satisfying positivity,
    normalization, and coarse-graining (a coarse effect is the fiber-sum of fine effects). -/
structure EffectStateNet (α : ι → Type*) (A : Type*) [AddCommMonoid A]
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] where
  /-- the (normal) state, as an additive ℝ-valued functional on effects. -/
  ω : A →+ ℝ
  /-- the joint effect of a context's outcome. -/
  E : ∀ J : Finset ι, (∀ j : J, α j) → A
  /-- Born weights are nonnegative. -/
  pos : ∀ J x, 0 ≤ ω (E J x)
  /-- the context is a POVM: total Born weight one. -/
  total : ∀ J, ∑ x, ω (E J x) = 1
  /-- coarse-graining: a coarse effect is the fiber-sum of the fine effects. -/
  coarse : ∀ ⦃I J : Finset ι⦄ (h : I ⊆ J) (y : ∀ i : I, α i),
    E I y = ∑ x ∈ Finset.univ.filter (fun x => Finset.restrict₂ h x = y), E J x

namespace EffectStateNet

variable (S : EffectStateNet α A)

/-- The Born probability mass function of a context (Born weights `ω(E_J ·)`). -/
noncomputable def bornPMF (J : Finset ι) : PMF (∀ j : J, α j) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (S.ω (S.E J x))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => S.pos J x), S.total J, ENNReal.ofReal_one])

@[simp] theorem bornPMF_apply (J : Finset ι) (x : ∀ j : J, α j) :
    S.bornPMF J x = ENNReal.ofReal (S.ω (S.E J x)) := rfl

/-- **B1 (state-agnostic): the Born weights of a state form a Kolmogorov-consistent probability
    family.**  Linearity of `ω` turns the coarse-graining of effects into the consistency of the Born
    measures, so any `EffectStateNet` yields a `FiniteMarginals`. -/
noncomputable def toFiniteMarginals : HistoryMeasure.FiniteMarginals α where
  μ := fun J => (S.bornPMF J).toMeasure
  isProb := fun _ => inferInstance
  proj := by
    intro I J hJI
    refine Measure.ext_of_singleton fun y => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y),
      Measure.map_apply (Finset.measurable_restrict₂ hJI) (measurableSet_singleton y),
      PMF.toMeasure_apply_fintype, bornPMF_apply, S.coarse hJI y, map_sum,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => S.pos I x), Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases eq_or_ne (Finset.restrict₂ hJI x) y with hx | hx <;>
      simp [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, bornPMF_apply, hx]

/-- **Phase B headline: the typicality measure μ∞ exists for any state on a finite-fiber net.**
    Combining B1 with the finite-fiber Kolmogorov extension (A2b): for any `EffectStateNet` with finite
    discrete outcome fibers there is a unique σ-additive probability measure μ∞ on the history space
    whose marginals are the state's Born measures.  (The physical realization of `ω` from a Type III₁
    QFT net is the cited frontier; the CONSTRUCTION is state-agnostic and machine-checked.) -/
theorem exists_typicalityMeasure [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [∀ i, Finite (α i)] :
    ∃ μ : Measure (∀ i, α i), IsProbabilityMeasure μ ∧ S.toFiniteMarginals.IsLimit μ :=
  QIQTH.KolmogorovFiniteFiber.exists_isLimit S.toFiniteMarginals

end EffectStateNet

end QIQTH.StateNetMeasure
