/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 3 — the covariance relation of the crossed product `M ⋊_σ ℝ`

Joins the matter representation `π(a) = matterRep S a` (Phase 1) and the clock translation group
`λ_t = clockTransl t` (Phase 2) via the **covariance relation** — the defining identity of the crossed product
`M ⋊_σ ℝ` (see `PHASE3_COVARIANCE_PLAN.md`):
```
  λ_{-t} ∘ π(a) ∘ λ_t  =  π(σ_t a)      (σ_t = modularAut S t).
```
Fiberwise both sides are `modularAut S (t-s) a (ξ s)` (via `modularAut_add`).  Bounded operators only — the
clock energy `X` (generator) is Phase 4, the trace Phase 5.  Axiom-free.
-/
import QIQTH.CrossedProductTranslation

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **★ Phase 3.1 — the covariance relation `λ_{-t} π(a) λ_t = π(σ_t a)`.**  The defining identity of the
    crossed product `M ⋊_σ ℝ`: conjugating the matter representation by the clock translation implements the
    modular automorphism `σ_t = modularAut S t`. -/
theorem covariance (S : StandardSubspace H) (a : H →L[ℂ] H) (t : ℝ) :
    (clockTransl (-t) ∘L matterRep S a ∘L clockTransl t :
        Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
      = matterRep S (modularAut S t a) := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Lp.ext_iff]
  have hmap : Measure.map (· + (-t)) (volume : Measure ℝ) = volume :=
    (measurePreserving_addRight_volume (-t)).map_eq
  have haem : AEMeasurable (· + (-t)) (volume : Measure ℝ) :=
    (measurePreserving_addRight_volume (-t)).measurable.aemeasurable
  -- shift the matter-fiber `ζ = π(a)(λ_t ξ)` by `(· + (-t))`
  have hζ_shift : (fun s => (matterRep S a (clockTransl t ξ)) (s + (-t))) =ᵐ[volume]
      fun s => modularAut S (-(s + (-t))) a ((clockTransl t ξ) (s + (-t))) := by
    have hco : matterRep S a (clockTransl t ξ)
        =ᵐ[Measure.map (· + (-t)) volume] fun u => modularAut S (-u) a ((clockTransl t ξ) u) := by
      simp only [hmap]; exact matterRepFun_coeFn S a (clockTransl t ξ)
    exact ae_eq_comp haem hco
  -- shift the clock-fiber `λ_t ξ` by `(· + (-t))`
  have hη_shift : (fun s => (clockTransl t ξ) (s + (-t))) =ᵐ[volume]
      fun s => ξ ((s + (-t)) + t) := by
    have hco : clockTransl t ξ =ᵐ[Measure.map (· + (-t)) volume] fun v => ξ (v + t) := by
      simp only [hmap]; exact clockTransl_coeFn t ξ
    exact ae_eq_comp haem hco
  filter_upwards [clockTransl_coeFn (-t) (matterRep S a (clockTransl t ξ)), hζ_shift, hη_shift,
    matterRepFun_coeFn S (modularAut S t a) ξ] with s e1 e2 e3 e4
  have ht1 : -(s + (-t)) = -s + t := by ring
  have ht2 : (s + (-t)) + t = s := by ring
  rw [e1, e2, e3, matterRep_apply, e4, ← modularAut_add, ht1, ht2]

end QIQTH.StandardSubspaceModular
