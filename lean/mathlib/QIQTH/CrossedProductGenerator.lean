/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 4.1 — strong continuity of the clock group `λ_t`

Toward the clock energy `X` = the generator of `λ_t = clockTransl t` (see `PHASE4_GENERATOR_PLAN.md`), the first
(tractable) step is **strong continuity**: `t ↦ λ_t ξ` is continuous in `L²(ℝ;H)` for each `ξ`.  With the group
law + isometry (Phase 2), this completes "`λ_t` is a **strongly-continuous one-parameter unitary group**" — the
exact hypothesis of **Stone's theorem**, which would then yield `X` (the next, frontier step).

Built from Mathlib's `Lp.ContinuousAt.compMeasurePreservingLp` (continuity of `L^p`-composition with a
continuously-varying measure-preserving map) — the varying map being translation `(· + t)`, continuous into
`C(ℝ,ℝ)` as the curry of continuous addition.  Bounded operators only; Stone (`X` as a self-adjoint operator)
is the cited frontier.  Axiom-free.
-/
import QIQTH.CrossedProductTranslation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Translation `t ↦ (· + t)` as a continuous family `ℝ → C(ℝ,ℝ)` (the curry of continuous addition). -/
noncomputable def translMap : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun p : ℝ × ℝ => p.2 + p.1, by fun_prop⟩

@[simp] theorem translMap_apply (t x : ℝ) : translMap t x = x + t := rfl

/-- **★ Phase 4.1 — strong continuity of the clock group.**  `t ↦ λ_t ξ` is continuous in `L²(ℝ;H)`.  With the
    group law (`clockTransl_add`) and isometry (`clockTransl_norm`), `λ_t` is a strongly-continuous one-parameter
    unitary group — Stone's theorem hypothesis (the generator `X` is the next, frontier, step). -/
theorem clockTransl_stronglyContinuous (ξ : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun t => clockTransl t ξ) := by
  have hg : Continuous (fun t : ℝ => translMap t) := translMap.continuous
  refine continuous_iff_continuousAt.2 fun t => ?_
  have key : ContinuousAt
      (fun t => Lp.compMeasurePreserving (translMap t) (measurePreserving_addRight_volume t) ξ) t :=
    ContinuousAt.compMeasurePreservingLp continuousAt_const hg.continuousAt
      (fun t => measurePreserving_addRight_volume t) (by simp)
  exact key

end QIQTH.StandardSubspaceModular
