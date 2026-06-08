/-
  XL-step Phase A, first increment (smoke test, ZERO quantum content) — per XL_STEP_PLAN.md §A0/§A1
  and the GPT-5.5-pro review (§0b.7): validate the `Finset ι` projective-family shape against Mathlib's
  Kolmogorov-extension API BEFORE wiring in any Born/quantum content.

  A `FiniteMarginals` is a Kolmogorov-CONSISTENT family of finite-stage probability measures — one
  probability measure `μ J` on the joint outcome space `∀ j : J, α j` of each finite context
  `J : Finset ι`, compatible under coordinate restriction (`IsProjectiveMeasureFamily`).  This is the
  abstract shape the continuum typicality measure μ∞ must extend (μ∞ on `∀ i, α i` = the histories /
  global selectors λ; its finite marginals are the Born measures).

  PRODUCT / i.i.d. CASE (reachable now via Mathlib `infinitePi`): from per-coordinate probability
  measures `ν i`, the product family `μ J = ⊗_{j∈J} ν j` is a `FiniteMarginals`, and `infinitePi ν` is a
  genuine σ-additive PROBABILITY measure on the full history space whose restriction to every finite
  context is the product marginal — i.e. the projective LIMIT exists and is unique
  (`productMarginals_isProjectiveLimit`, `productMarginals_marginal`, `limit_unique`).

  HONEST SCOPE (review §0b): this is the PRODUCT (independent-measurement) case — plumbing that
  confirms the shape, NOT the prize.  The correlated/entangled case is the finite-fiber Kolmogorov
  extension (XL_STEP_PLAN §A2b), and the index `ι` must denote COMPATIBLE/decoherent record variables
  (a joint law on incompatible POVMs is false by Fine/Bell — §0b.1).

  Axiom-free: depends only on `propext, Classical.choice, Quot.sound`.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace QIQTH.HistoryMeasure

open MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- A Kolmogorov-consistent family of finite-stage probability measures: a probability measure on the
    joint outcome space of every finite context `J : Finset ι`, compatible under coordinate restriction. -/
structure FiniteMarginals (α : ι → Type*) [∀ i, MeasurableSpace (α i)] where
  /-- the measure on each finite context's joint outcome space. -/
  μ : ∀ J : Finset ι, Measure (∀ j : J, α j)
  /-- each stage is a probability measure. -/
  isProb : ∀ J, IsProbabilityMeasure (μ J)
  /-- Kolmogorov consistency under restriction. -/
  proj : IsProjectiveMeasureFamily μ

/-- A measure on the full history space `∀ i, α i` realizing the family as its projective limit. -/
def FiniteMarginals.IsLimit (F : FiniteMarginals α) (μlim : Measure (∀ i, α i)) : Prop :=
  IsProjectiveLimit μlim F.μ

/-- **Projective limits are unique** (when they exist): the typicality measure realizing a
    `FiniteMarginals` family is determined by the finite Born marginals. -/
theorem FiniteMarginals.limit_unique (F : FiniteMarginals α) {μ ν : Measure (∀ i, α i)}
    (hμ : F.IsLimit μ) (hν : F.IsLimit ν) : μ = ν := by
  haveI : ∀ J, IsFiniteMeasure (F.μ J) := fun J => haveI := F.isProb J; inferInstance
  exact IsProjectiveLimit.unique hμ hν

/-! ### Product / i.i.d. case via Mathlib `infinitePi` (the smoke test) -/

/-- The product (i.i.d.) family from per-coordinate probability measures `ν i`:
    `μ J = ⊗_{j∈J} ν j`.  A genuine `FiniteMarginals`. -/
noncomputable def productMarginals (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] :
    FiniteMarginals α where
  μ := fun J => Measure.pi (fun i : J => ν i)
  isProb := fun _ => inferInstance
  proj := isProjectiveMeasureFamily_pi ν

/-- **Smoke test (the payoff): the i.i.d. family has a genuine σ-additive projective-limit measure.**
    `infinitePi ν` realizes `productMarginals ν` as its projective limit — confirming the `Finset ι`
    shape is compatible with Mathlib's Kolmogorov extension. -/
theorem productMarginals_isProjectiveLimit (ν : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (ν i)] :
    (productMarginals ν).IsLimit (Measure.infinitePi ν) :=
  Measure.isProjectiveLimit_infinitePi ν

/-- The limit's restriction to a finite context `J` is the product Born marginal `μ_J`
    (Born for every finite decoherent partition — product case). -/
theorem productMarginals_marginal (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    (J : Finset ι) :
    (Measure.infinitePi ν).map J.restrict = (productMarginals ν).μ J :=
  Measure.infinitePi_map_restrict ν

/-- The limit measure is a probability measure on the full history space. -/
theorem productMarginals_isProbabilityMeasure (ν : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (Measure.infinitePi ν) := inferInstance

/-! ### A3/A4/A5 — properties of the typicality measure μ∞ (conditional on a limit; compose with A2b) -/

/-- **A3 — Born marginals at the limit.**  The history measure restricts to the finite Born measure at
    every context `J` — "Born for every finite decoherent record partition," at the continuum.  (This is
    the defining property of the projective limit, isolated as the headline statement.) -/
theorem isLimit_marginal {F : FiniteMarginals α} {μ : Measure (∀ i, α i)} (h : F.IsLimit μ)
    (J : Finset ι) : μ.map J.restrict = F.μ J := h J

/-- **A5 — no-signaling at the limit.**  The marginal on a sub-context `J ⊆ J'` is the restriction of
    the larger context's marginal: `μ↾J = (μ↾J')↾J`.  So including remote measurements `J' ∖ J` cannot
    change the local statistics — operational no-signaling for the whole history measure. -/
theorem isLimit_marginal_mono {F : FiniteMarginals α} {μ : Measure (∀ i, α i)} (h : F.IsLimit μ)
    {J J' : Finset ι} (hJ : J ⊆ J') :
    μ.map J.restrict = (μ.map J'.restrict).map (Finset.restrict₂ hJ) := by
  rw [h J, h J', ← F.proj J' J hJ]

/-- **A4 — covariance of the typicality measure.**  A symmetry `e` of the history space under which the
    pushforward `μ.map e` is again a projective limit of the SAME family is measure-preserving:
    `μ.map e = μ`.  The hypothesis `F.IsLimit (μ.map e)` is exactly "the symmetry preserves every Born
    marginal" (the family-level form of P2's `μ_covariant`); the conclusion follows from uniqueness. -/
theorem isLimit_map_eq {F : FiniteMarginals α} {μ : Measure (∀ i, α i)} (h : F.IsLimit μ)
    {e : (∀ i, α i) → (∀ i, α i)} (he : F.IsLimit (μ.map e)) : μ.map e = μ :=
  F.limit_unique he h

end QIQTH.HistoryMeasure
