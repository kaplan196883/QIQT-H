/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 2 — the translation (clock) unitary group `λ_t` on `L²(ℝ;H)`

Toward the crossed product `M ⋊_σ ℝ` (see `P4_WALL_CAMPAIGN_PLAN.md` / `PHASE2_TRANSLATION_PLAN.md`), the
`L²(ℝ)` **clock factor** is the translation group `λ_t : L²(ℝ;H) →L[ℂ] L²(ℝ;H)`, `(λ_t ξ)(s) = ξ(s + t)`.

Mathlib provides `Lp.compMeasurePreservingₗᵢ ℂ f hf : Lp H 2 μ →ₗᵢ[ℂ] Lp H 2 μ` — precomposition with a
measure-preserving `f` as a **ℂ-linear isometry**.  With `f = (· + t)` (translation, measure-preserving for
`volume`) this gives `λ_t` directly; `Lp.compMeasurePreserving_comp`/`_id` give the one-parameter group law.

Bounded operators only — the (unbounded) clock energy `X` = generator of `λ_t` is Phase 4 (Stone).  Axiom-free.
-/
import QIQTH.CrossedProductRep
import Mathlib.MeasureTheory.Group.Measure

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Translation `(· + t)` is measure-preserving on `(ℝ, volume)` (left/right Haar invariance). -/
theorem measurePreserving_addRight_volume (t : ℝ) :
    MeasurePreserving (· + t) (volume : Measure ℝ) volume :=
  measurePreserving_add_right volume t

/-- **★ Phase 2.1 — the clock translation `λ_t`** as a bounded ℂ-linear operator on `L²(ℝ;H)`:
    `(λ_t ξ)(s) = ξ(s + t)`, built from Mathlib's `compMeasurePreservingₗᵢ` (a ℂ-linear isometry). -/
noncomputable def clockTransl (t : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_addRight_volume t)).toContinuousLinearMap

theorem clockTransl_apply (t : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockTransl t ξ = Lp.compMeasurePreserving (· + t) (measurePreserving_addRight_volume t) ξ := rfl

/-- The fiber: `(λ_t ξ)(s) = ξ(s + t)` a.e. -/
theorem clockTransl_coeFn (t : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockTransl t ξ =ᵐ[volume] fun s => ξ (s + t) := by
  rw [clockTransl_apply]
  exact Lp.coeFn_compMeasurePreserving ξ (measurePreserving_addRight_volume t)

/-- `λ_t` is an isometry: `‖λ_t ξ‖ = ‖ξ‖`. -/
@[simp] theorem clockTransl_norm (t : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    ‖clockTransl t ξ‖ = ‖ξ‖ := by
  rw [clockTransl_apply]
  exact Lp.norm_compMeasurePreserving ξ (measurePreserving_addRight_volume t)

end QIQTH.StandardSubspaceModular
