/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 1.1 — measurability of the matter-representation fiber

Toward the matter representation `π(a)` of the crossed product `M ⋊_σ ℝ` on `L²(ℝ; H)` (see
`P4_WALL_CAMPAIGN_PLAN.md`), with `π(a)ξ(s) = σ_{-s}(a)(ξ s) = Δ^{-is} a Δ^{is}(ξ s)`.  First sub-step: the
**measurability of the fiber map** `s ↦ σ_{-s}(a)(ξ s)`.

The operator family `s ↦ Δ^{is} = modUnitary S s` is only *strongly* continuous (not norm-measurable), so we use
Mathlib's `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` — stated for an **opaque** CLM family
(so `modUnitary`'s heavy `borelFC` definition is never unfolded during unification).  `H` (the one-particle
space) is assumed separable (`[SecondCountableTopology H]`), which is physical.  Bounded operators only.
Axiom-free.
-/
import QIQTH.CrossedProduct
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option maxHeartbeats 1000000

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **Generic:** the uncurry of a strongly-continuous family of bounded operators is strongly measurable.
    Stated for an opaque family `U` so `modUnitary`'s `borelFC` definition is never unfolded. -/
theorem stronglyMeasurable_uncurry_clmFamily (U : ℝ → H →L[ℂ] H)
    (hU : ∀ x, Continuous (fun i => U i x)) :
    StronglyMeasurable (Function.uncurry (fun i x => U i x)) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hU
    (fun i => (U i).continuous.stronglyMeasurable)

/-- **Applying the modular flow along a measurable time reparametrization preserves measurability.**  For an
    `AEStronglyMeasurable` field `g : ℝ → H` and a measurable time `τ : ℝ → ℝ`, `s ↦ Δ^{i τ(s)}(g s)` is
    `AEStronglyMeasurable`.  (Used with `τ = id` and `τ = (-·)` to build `σ_{-s}`.) -/
theorem aesm_modUnitary_comp (S : StandardSubspace H) {τ : ℝ → ℝ}
    (hτ : AEMeasurable τ (volume : Measure ℝ)) {g : ℝ → H}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun s => modUnitary S (τ s) (g s)) (volume : Measure ℝ) := by
  have key : AEStronglyMeasurable
      (Function.uncurry (fun i x => modUnitary S i x) ∘ fun s => (τ s, g s)) (volume : Measure ℝ) :=
    (stronglyMeasurable_uncurry_clmFamily (modUnitary S)
      (fun x => modUnitary_stronglyContinuous S x)).aestronglyMeasurable.comp_aemeasurable
      (hτ.prodMk hg.aemeasurable)
  exact key

/-- **★ Phase 1.1 — the matter-representation fiber is measurable.**  For a bounded operator `a` and an
    `AEStronglyMeasurable` field `ξ : ℝ → H`, the fiber `s ↦ σ_{-s}(a)(ξ s) = Δ^{-is} a Δ^{is}(ξ s)` is
    `AEStronglyMeasurable` — the first sub-step of `π(a)` as an operator on `L²(ℝ; H)`. -/
theorem aesm_matterFiber (S : StandardSubspace H) (a : H →L[ℂ] H) {ξ : ℝ → H}
    (hξ : AEStronglyMeasurable ξ (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun s => modularAut S (-s) a (ξ s)) (volume : Measure ℝ) := by
  -- σ_{-s}(a)(ξ s) = Δ^{-is} (a (Δ^{is} (ξ s)))
  have h1 : AEStronglyMeasurable (fun s => modUnitary S s (ξ s)) (volume : Measure ℝ) :=
    aesm_modUnitary_comp S aemeasurable_id hξ
  have h2 : AEStronglyMeasurable (fun s => a (modUnitary S s (ξ s))) (volume : Measure ℝ) :=
    a.continuous.comp_aestronglyMeasurable h1
  have h3 : AEStronglyMeasurable
      (fun s => modUnitary S (-s) (a (modUnitary S s (ξ s)))) (volume : Measure ℝ) :=
    aesm_modUnitary_comp S aemeasurable_id.neg h2
  refine h3.congr (Filter.Eventually.of_forall (fun s => ?_))
  simp only [modularAut, neg_neg, ContinuousLinearMap.mul_apply]

/-- **The conjugation is norm-contractive:** `‖σ_t(a) v‖ ≤ ‖a‖·‖v‖` (the modular unitaries are isometries, so
    `‖σ_t(a)‖ ≤ ‖a‖`).  The pointwise bound powering the `L²` estimate for `π(a)`. -/
theorem norm_modularAut_apply_le (S : StandardSubspace H) (t : ℝ) (a : H →L[ℂ] H) (v : H) :
    ‖modularAut S t a v‖ ≤ ‖a‖ * ‖v‖ := by
  rw [modularAut]
  simp only [ContinuousLinearMap.mul_apply]
  rw [modUnitary_norm]
  calc ‖a (modUnitary S (-t) v)‖
      ≤ ‖a‖ * ‖modUnitary S (-t) v‖ := a.le_opNorm _
    _ = ‖a‖ * ‖v‖ := by rw [modUnitary_norm]

/-- **★ Phase 1.2 (Lᵖ membership) — `π(a)ξ ∈ L²(ℝ;H)`.**  For `ξ ∈ L²(ℝ;H)`, the fiber `s ↦ σ_{-s}(a)(ξ s)` is
    in `L²` (measurable by Phase 1.1, dominated by `‖a‖·‖ξ s‖` via the contraction bound). -/
theorem memLp_matterFiber (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun s => modularAut S (-s) a (ξ s)) 2 (volume : Measure ℝ) :=
  MemLp.of_le_mul (Lp.memLp ξ) (aesm_matterFiber S a (Lp.aestronglyMeasurable ξ))
    (Filter.Eventually.of_forall (fun s => norm_modularAut_apply_le S (-s) a (ξ s)))

end QIQTH.StandardSubspaceModular
