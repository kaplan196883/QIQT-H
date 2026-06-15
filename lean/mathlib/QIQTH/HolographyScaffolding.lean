/-
HolographyScaffolding.lean — how much holography does λ's law actually require? (2026-06-15)

After H2 was retired (capacity does NOT forbid records — a category error), the question is: does any genuine
holographic content remain load-bearing, or is it scaffolding? This module makes the precise answer
machine-checked for the one place holography might still be essential — the construction of λ's law (the
covariant σ-additive Born measure on the record net).

ANSWER: the measure's construction requires only **finiteness** of the record fibers — NOT the holographic
area-bound. The holographic bound is a *sufficient* upstream source of that finiteness (it caps the record
count at `e^{Q_R}`), but is not logically required: any finite record structure works equally, and the
construction never mentions the area `A`, the Planck length `ℓ_P`, or `Q_R`.

- `records_finite_of_holographic_bound` — sufficiency: a region's record type injecting into the
  holographically-bounded register `Fin N` (`N = ⌊e^{Q_R}⌋`) is finite.
- `measure_needs_only_finiteness` — λ's law (the σ-additive Born measure μ∞) exists for ANY `EffectStateNet`
  over discrete *finite* fibers; the hypotheses are finiteness + discreteness, with NO holographic quantity
  anywhere (it is `StateNetMeasure.exists_typicalityMeasure`, whose hypothesis is `[∀ i, Finite (α i)]`).
- The free-field instance (`Fock.weylBit_typicalityMeasure_exists`) uses `Bool` fibers — `Finite` by
  inference, holography-free.

CONCLUSION (honest): holography is **scaffolding**, not the engine. It grounds the finiteness physically
(area-scaling, covariance) and supplies the borrowed Type II entropy substrate, but λ's covariant law needs
only finiteness — so the single-world `(Φ,λ)` interpretation does not logically depend on the holographic
area-bound for its measure. The "H" in QIQT-H names the stage and the borrowed mathematics, not a load-bearing
mechanism. Axiom-free.
-/
import QIQTH.StateNetMeasure
import Mathlib.Tactic

namespace QIQTH.HolographyScaffolding

open MeasureTheory QIQTH.StateNetMeasure

/-- **Sufficiency: the holographic count bound supplies the finiteness the measure needs.** If a region's
record type `K` injects into the holographically-bounded register `Fin N` (with `N = ⌊e^{Q_R}⌋`, the
holographic cap on the number of distinguishable records), then `K` is finite — exactly the hypothesis λ's
typicality measure requires. So holography is a SUFFICIENT source of that finiteness (not a necessary one). -/
theorem records_finite_of_holographic_bound {K : Type*} {N : ℕ} (f : K → Fin N)
    (hf : Function.Injective f) : Finite K :=
  Finite.of_injective f hf

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
  [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
  [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
  {A : Type*} [AddCommMonoid A]

/-- **λ's law needs only FINITENESS, not the holographic area-bound.** For any `EffectStateNet` over discrete
finite outcome fibers, the σ-additive probability measure μ∞ realizing the Born marginals exists. The
hypotheses are finiteness + discreteness/measurability; there is NO occurrence of the boundary area `A`, the
Planck length `ℓ_P`, or the holographic capacity `Q_R` in the statement or its proof (it is exactly
`StateNetMeasure.exists_typicalityMeasure`, whose only finiteness hypothesis is `[∀ i, Finite (α i)]`). So λ's
covariant law is built on finiteness; holography (`records_finite_of_holographic_bound`) is one *sufficient*
way to ground that finiteness, not a logical requirement — any finite record structure works equally. -/
theorem measure_needs_only_finiteness (S : EffectStateNet α A) :
    ∃ μ : Measure (∀ i, α i), IsProbabilityMeasure μ ∧ S.toFiniteMarginals.IsLimit μ :=
  S.exists_typicalityMeasure

/-- Finiteness without any holographic input: `Bool` (the Weyl-bit outcome set on which the free-field record
measure `Fock.weylBit_typicalityMeasure_exists` is built) is finite by inference, no area bound invoked. -/
example : Finite Bool := inferInstance

end QIQTH.HolographyScaffolding
