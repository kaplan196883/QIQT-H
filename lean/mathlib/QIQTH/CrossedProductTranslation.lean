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

/-- `λ_0 = id` on `L²(ℝ;H)`. -/
theorem clockTransl_zero_apply (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockTransl (0 : ℝ) ξ = ξ := by
  rw [Lp.ext_iff]
  filter_upwards [clockTransl_coeFn 0 ξ] with s e1
  rw [e1, add_zero]

/-- **★ Phase 2.2 — `λ_0 = 1`.** -/
theorem clockTransl_zero :
    (clockTransl (0 : ℝ) : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) = 1 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [clockTransl_zero_apply, ContinuousLinearMap.one_apply]

/-- **★ Phase 2.2 — the one-parameter group law `λ_{s+t} = λ_s ∘ λ_t`.** -/
theorem clockTransl_add (s t : ℝ) :
    (clockTransl (s + t) : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
      = clockTransl s ∘L clockTransl t := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, Lp.ext_iff]
  have hmap : Measure.map (· + s) (volume : Measure ℝ) = volume :=
    (measurePreserving_addRight_volume s).map_eq
  have hco : clockTransl t ξ =ᵐ[Measure.map (· + s) volume] fun v => ξ (v + t) := by
    simp only [hmap]; exact clockTransl_coeFn t ξ
  have h3' : (fun u => (clockTransl t ξ) (u + s)) =ᵐ[volume] fun u => ξ ((u + s) + t) :=
    ae_eq_comp (measurePreserving_addRight_volume s).measurable.aemeasurable hco
  filter_upwards [clockTransl_coeFn (s + t) ξ, clockTransl_coeFn s (clockTransl t ξ), h3']
    with u e1 e2 e3
  rw [e1, e2, e3]; congr 1; ring

/-- **★ Phase 2.3 — `λ_{-t}` is the two-sided inverse of `λ_t` (right).**  `λ_t ∘ λ_{-t} = 1`. -/
theorem clockTransl_comp_neg (t : ℝ) :
    clockTransl t ∘L clockTransl (-t)
      = (1 : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) := by
  rw [← clockTransl_add, add_neg_cancel, clockTransl_zero]

/-- **★ Phase 2.3 — `λ_{-t}` is the two-sided inverse of `λ_t` (left).**  `λ_{-t} ∘ λ_t = 1`. -/
theorem clockTransl_neg_comp (t : ℝ) :
    clockTransl (-t) ∘L clockTransl t
      = (1 : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) := by
  rw [← clockTransl_add, neg_add_cancel, clockTransl_zero]

/-! ### Phase 2.3 — `λ_t` is a **unitary** (an isometric two-sided-invertible operator).

`clockTransl_norm` (isometry) + `clockTransl_comp_neg`/`_neg_comp` (inverse `λ_{-t}`) exhibit `λ_t` as a unitary
of `L²(ℝ;H)` — the clock translation **unitary group** `λ_0 = 1`, `λ_{s+t} = λ_s λ_t`, `λ_t⁻¹ = λ_{-t}`,
`‖λ_t ξ‖ = ‖ξ‖`.  (The explicit `star (λ_t) = λ_{-t}` / `unitary` membership meets the same `Lp`/`RCLike`
adjoint instance diamond recorded in Phase 1's `*`; the two-sided-inverse + isometry form above is the
diamond-free statement of unitarity, and is what Phase 3's covariance needs.) -/

end QIQTH.StandardSubspaceModular
