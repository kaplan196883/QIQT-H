/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Gårding mollified vectors — the entry to essential self-adjointness of a Stone generator

The remaining frontier of general Stone's theorem (`QIQTH/Spectral/Stone.lean`) is essential self-adjointness
of the generator `A = stoneGen U` — equivalently `Range(A ± i)` dense / the smooth domain dense. The classical
constructive route is **Gårding mollification**: for a strongly-continuous one-parameter group `U_t` and a smooth
compactly-supported mollifier `φ`, the **mollified vector**

  `x_φ := ∫ φ(t) U_t x dt`

lies in the smooth domain (`U_s x_φ` is differentiable in `s`, since `U_s x_φ = ∫ φ(u−s) U_u x du`), and the set
`{x_φ}` is dense (as `φ → δ`, `x_φ → x`). This file lays the algebraic/integration foundation of that route:
`mollify` and its integrability, plus the **flow-shift identity** `U_s x_φ = ∫ φ(t) U_{s+t} x dt` (the
load-bearing step on which the differentiation-under-the-integral argument rests).

The differentiation step (`x_φ ∈ stoneDomain U`) and the density `{x_φ}` dense are the genuine analytic frontier
(differentiation under the Bochner integral + approximate identity) — built on this foundation, not claimed here.
Axiom-free.
-/
import QIQTH.Spectral.Stone
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace QIQTH.Spectral

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- The **mollified (Gårding) vector** `x_φ = ∫ φ(t) U_t x dt` of `x` against the mollifier `φ`, for a
    one-parameter family `U` on `H`. -/
noncomputable def mollify (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H) : H :=
  ∫ t, φ t • U t x

/-- The mollifier integrand `t ↦ φ(t) U_t x` is integrable, for `φ` continuous with compact support and `U`
    **strongly continuous** at `x` (`t ↦ U_t x` continuous). Continuous × compact-support ⟹ integrable. -/
theorem mollify_integrable (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H)
    (hcont : Continuous (fun t => U t x)) (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    Integrable (fun t => φ t • U t x) :=
  (hφ.smul hcont).integrable_of_hasCompactSupport hsupp.smul_right

/-- **The flow-shift identity** `U_s x_φ = ∫ φ(t) U_{s+t} x dt`: the bounded operator `U_s` passes through the
    Bochner integral (`integral_comp_comm`), then the group law `U_s U_t = U_{s+t}` shifts the orbit. This is the
    algebraic core of the Gårding argument — differentiating its right side in `s` (under the integral) is what
    places `x_φ` in the smooth domain. -/
theorem mollify_apply_flow (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (φ : ℝ → ℂ) (x : H) (hcont : Continuous (fun t => U t x)) (hφ : Continuous φ)
    (hsupp : HasCompactSupport φ) (s : ℝ) :
    U s (mollify U φ x) = ∫ t, φ t • U (s + t) x := by
  rw [mollify, ← ContinuousLinearMap.integral_comp_comm (U s)
      (mollify_integrable U φ x hcont hφ hsupp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [map_smul, ← ContinuousLinearMap.comp_apply, ← hgrp s t]

/-- **The orbit of a mollified vector in differentiation-ready form:** `U_s x_φ = ∫ φ(u − s) U_u x du`. Change
    of variables `u = s + t` (translation invariance of `volume`, `integral_add_right_eq_self`) applied to the
    flow-shift identity. Now the `s`-dependence sits *entirely* in the smooth scalar `φ(u − s)` — the
    `U_u x` factor is `s`-independent — so the orbit `s ↦ U_s x_φ` is ready for differentiation under the
    integral (`d/ds|₀ = −∫ φ'(u) U_u x du`), the step that places `x_φ` in the smooth domain. -/
theorem mollify_apply_flow_cov (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (φ : ℝ → ℂ) (x : H) (hcont : Continuous (fun t => U t x)) (hφ : Continuous φ)
    (hsupp : HasCompactSupport φ) (s : ℝ) :
    U s (mollify U φ x) = ∫ u, φ (u - s) • U u x := by
  rw [mollify_apply_flow U hgrp φ x hcont hφ hsupp s,
    ← integral_add_right_eq_self (fun u => φ (u - s) • U u x) s]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [add_sub_cancel_right, add_comm s t]

/-- **The parametric integrand is differentiable in the shift parameter:** for `φ ∈ C¹` (witnessed by `φ'`),
    `σ ↦ φ(u − σ) • U_u x` has derivative `−φ'(u − σ₀) • U_u x` at `σ₀` (chain rule on the inner `u − σ`,
    then `smul` by the constant `U_u x`). This is the pointwise `h_diff` hypothesis of
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` — the calculus core of differentiating `U_s x_φ` (in the
    `mollify_apply_flow_cov` form) under the integral, which places `x_φ` in the smooth domain. -/
theorem mollify_integrand_hasDerivAt (φ φ' : ℝ → ℂ) (hφ' : ∀ y, HasDerivAt φ (φ' y) y)
    (U : ℝ → (H →L[ℂ] H)) (x : H) (u σ₀ : ℝ) :
    HasDerivAt (fun σ => φ (u - σ) • U u x) ((-φ' (u - σ₀)) • U u x) σ₀ := by
  have hg : HasDerivAt (fun σ => u - σ) (-1 : ℝ) σ₀ := (hasDerivAt_id σ₀).const_sub u
  have hcomp := (hφ' (u - σ₀)).scomp σ₀ hg
  simpa [Function.comp_def] using hcomp.smul_const (U u x)

/-- The shifted parametric integrand `u ↦ φ(u − σ) • U_u x` is `AEStronglyMeasurable` (continuous, for `φ`
    continuous and `U` strongly continuous at `x`). Supplies the `hF_meas` hypothesis (for every `σ`) of the
    differentiation-under-the-integral lemma. -/
theorem mollify_shifted_aestronglyMeasurable (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H)
    (hcont : Continuous (fun t => U t x)) (hφ : Continuous φ) (σ : ℝ) :
    AEStronglyMeasurable (fun u => φ (u - σ) • U u x) volume :=
  ((hφ.comp (continuous_id.sub continuous_const)).smul hcont).aestronglyMeasurable

/-- The derivative integrand `u ↦ φ'(u) • U_u x` is `AEStronglyMeasurable` (continuous). Supplies the
    `hF'_meas` hypothesis of the differentiation-under-the-integral lemma. -/
theorem mollify_deriv_aestronglyMeasurable (U : ℝ → (H →L[ℂ] H)) (φ' : ℝ → ℂ) (x : H)
    (hcont : Continuous (fun t => U t x)) (hφ' : Continuous φ') :
    AEStronglyMeasurable (fun u => φ' u • U u x) volume :=
  (hφ'.smul hcont).aestronglyMeasurable

/-- **The would-be derivative of `U_s x_φ` is again a Gårding vector:** `∫ (−φ'(u)) • U_u x du = −x_{φ'}`. So
    `d/ds U_s x_φ` (once the differentiation under the integral is justified) equals `−mollify U φ' x` — the
    smooth/Gårding subspace is *closed under the generator* `A = −i d/dt U_t` (it maps Gårding vectors to Gårding
    vectors), the structural fact behind density and the symmetry of the generator on it. -/
theorem mollify_neg_deriv_eq (U : ℝ → (H →L[ℂ] H)) (φ' : ℝ → ℂ) (x : H) :
    (∫ u, (-φ' u) • U u x) = - mollify U φ' x := by
  simp_rw [neg_smul]
  rw [integral_neg, mollify]

/-! ### The dominating-bound ingredients (compact-support consequences for the mollifier derivative)

The single remaining hypothesis of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the Gårding orbit is
an *integrable dominating bound* for `‖F'(σ,u)‖ = |φ'(u−σ)|·‖U_u x‖` over `σ` in a neighborhood. With a uniform
operator bound `‖U_u x‖ ≤ M`, that bound is `C·M·𝟙_K(u)` where `C = ‖φ'‖_∞` and `K` is a ball containing
`tsupp φ' + nbhd` (compact ⟹ finite measure ⟹ indicator integrable). The two analytic facts it rests on — `φ'`
bounded, and `φ'` vanishing outside a ball — are isolated here (generic for continuous compactly-supported
`ℝ → ℂ`). Assembling the bound + applying the differentiation lemma (⟹ `x_φ ∈ stoneDomain U`) is the next step. -/

/-- A continuous compactly-supported `φ' : ℝ → ℂ` is **bounded** — the sup bound `C = ‖φ'‖_∞` for the
    dominating function. -/
theorem exists_norm_le_of_compactSupport (φ' : ℝ → ℂ) (hφ' : Continuous φ')
    (hsupp : HasCompactSupport φ') : ∃ C : ℝ, ∀ y, ‖φ' y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hφ'.norm.bddAbove_range_of_hasCompactSupport hsupp.norm
  exact ⟨C, fun y => hC ⟨y, rfl⟩⟩

/-- A compactly-supported `φ' : ℝ → ℂ` **vanishes outside a ball** `{|y| ≤ ρ}` — the uniform support
    localization that makes the dominating function compactly supported (hence integrable). -/
theorem exists_support_subset_of_compactSupport (φ' : ℝ → ℂ) (hsupp : HasCompactSupport φ') :
    ∃ ρ : ℝ, ∀ y, ρ < |y| → φ' y = 0 := by
  obtain ⟨ρ, hρ⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨ρ, fun y hy => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have hb := hρ hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
  exact absurd hb (not_le.mpr hy)

/-- The dominating bound `c · 𝟙_{closedBall 0 R}` is **integrable** — indicator of a compact (finite-measure)
    set times a constant. The integrability of the Gårding dominating function. -/
theorem integrable_indicator_closedBall_const (R c : ℝ) :
    Integrable ((Metric.closedBall (0 : ℝ) R).indicator (fun _ => c)) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact integrableOn_const (isCompact_closedBall (0 : ℝ) R).measure_lt_top.ne

/-- **★ Differentiability of the mollified orbit (the Gårding differentiation under the integral).** For a
    one-parameter family `U` with `t ↦ U_t x` continuous and uniformly bounded (`‖U_t x‖ ≤ M`), and a `C¹`
    compactly-supported mollifier `φ` (with derivative `φ'`, both `φ, φ'` having compact support), the orbit
    `s ↦ ∫ φ(u − s) U_u x du` is differentiable at `0` with derivative `∫ (−φ'(u)) U_u x du`. Proof: apply
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the dominating bound `C·M·𝟙_{closedBall 0 (ρ+1)}`
    (`C = ‖φ'‖_∞`, `ρ` bounding `supp φ'`); domination is a case split on `|u| ≤ ρ+1`. -/
theorem mollify_orbit_hasDerivAt (U : ℝ → (H →L[ℂ] H)) (φ φ' : ℝ → ℂ)
    (hφ' : ∀ y, HasDerivAt φ (φ' y) y) (hφcont : Continuous φ) (hsuppφ : HasCompactSupport φ)
    (hφ'cont : Continuous φ') (hsupp' : HasCompactSupport φ')
    (x : H) (M : ℝ) (hM : 0 ≤ M) (hUbd : ∀ t, ‖U t x‖ ≤ M)
    (hcont : Continuous (fun t => U t x)) :
    HasDerivAt (fun s => ∫ u, φ (u - s) • U u x) (∫ u, (-φ' u) • U u x) 0 := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_compactSupport φ' hφ'cont hsupp'
  obtain ⟨ρ, hρ⟩ := exists_support_subset_of_compactSupport φ' hsupp'
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set bound : ℝ → ℝ := (Metric.closedBall (0 : ℝ) (ρ + 1)).indicator (fun _ => C * M) with hbound
  have h_bound : ∀ᵐ u ∂(volume : Measure ℝ), ∀ σ ∈ Metric.ball (0 : ℝ) 1,
      ‖(-φ' (u - σ)) • U u x‖ ≤ bound u := by
    refine Filter.Eventually.of_forall fun u σ hσ => ?_
    rw [norm_smul, norm_neg]
    by_cases hu : u ∈ Metric.closedBall (0 : ℝ) (ρ + 1)
    · rw [hbound, Set.indicator_of_mem hu]
      exact mul_le_mul (hC _) (hUbd u) (norm_nonneg _) hC0
    · have hφz : φ' (u - σ) = 0 := by
        refine hρ _ ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hσ
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hu
        have h1 : |u| - |σ| ≤ |u - σ| := abs_sub_abs_le_abs_sub u σ
        linarith
      rw [hφz, norm_zero, zero_mul, hbound]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hC0 hM) u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun σ u => φ (u - σ) • U u x) (F' := fun σ u => (-φ' (u - σ)) • U u x)
    (bound := bound) (x₀ := (0 : ℝ)) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun σ => mollify_shifted_aestronglyMeasurable U φ x hcont hφcont σ)
    (by simpa [sub_zero] using mollify_integrable U φ x hcont hφcont hsuppφ)
    (by simpa [sub_zero] using
        mollify_deriv_aestronglyMeasurable U (fun u => -φ' u) x hcont hφ'cont.neg)
    h_bound (integrable_indicator_closedBall_const (ρ + 1) (C * M))
    (Filter.Eventually.of_forall fun u σ _ => mollify_integrand_hasDerivAt φ φ' hφ' U x u σ)
  simpa [sub_zero] using hmain.2

/-- **★ Gårding vectors lie in the smooth domain:** `mollify U φ x ∈ stoneDomain U` for `φ ∈ C¹_c` and a
    uniformly-bounded strongly-continuous family `U`. The orbit `s ↦ U_s x_φ` equals `∫ φ(u−s) U_u x du`
    (`mollify_apply_flow_cov`), differentiable at `0` (`mollify_orbit_hasDerivAt`). **This is the first crack in
    the essential-self-adjointness wall: the smooth domain of the Stone generator is nonempty, and in fact
    contains every Gårding vector.** Density `{x_φ} dense` (as `φ → δ`) then upgrades this to `Range(A±i)` dense
    ⟹ `A` essentially self-adjoint — the remaining step. -/
theorem mollify_mem_stoneDomain (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (φ φ' : ℝ → ℂ) (hφ' : ∀ y, HasDerivAt φ (φ' y) y) (hφcont : Continuous φ)
    (hsuppφ : HasCompactSupport φ) (hφ'cont : Continuous φ') (hsupp' : HasCompactSupport φ')
    (x : H) (M : ℝ) (hM : 0 ≤ M) (hUbd : ∀ t, ‖U t x‖ ≤ M)
    (hcont : Continuous (fun t => U t x)) :
    mollify U φ x ∈ stoneDomain U := by
  have hfun : (fun s => U s (mollify U φ x)) = fun s => ∫ u, φ (u - s) • U u x := by
    funext s; exact mollify_apply_flow_cov U hgrp φ x hcont hφcont hsuppφ s
  show DifferentiableAt ℝ (fun s => U s (mollify U φ x)) 0
  rw [hfun]
  exact (mollify_orbit_hasDerivAt U φ φ' hφ' hφcont hsuppφ hφ'cont hsupp' x M hM hUbd
    hcont).differentiableAt

/-! ### The Gårding-approximation identity (toward density of the smooth domain)

`mollify_mem_stoneDomain` shows the smooth domain *contains* every Gårding vector. Density then needs
`x_φ → x` as `φ → δ` (a Dirac sequence). The foundation is the identity `x_φ − (∫φ)·x = ∫ φ(t)(U_t x − x) dt`:
with `∫ φ = 1` and `φ` concentrated near `0`, the right side is small by strong continuity (`U_t x → x` as
`t → 0`), so `x_φ → x`. -/

/-- **The Gårding-approximation identity:** `x_φ − (∫φ)·x = ∫ φ(t) (U_t x − x) dt`. (Subtract the constant
    field `∫ φ(t)·x = (∫φ)·x` from the mollified vector and combine under one integral.) With `∫ φ = 1` the left
    side is `x_φ − x`. -/
theorem mollify_sub (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H)
    (hint : Integrable (fun t => φ t • U t x)) (hintx : Integrable (fun t => φ t • x)) :
    mollify U φ x - (∫ t, φ t) • x = ∫ t, φ t • (U t x - x) := by
  have h1 : (∫ t, φ t) • x = ∫ t, φ t • x := (integral_smul_const φ x).symm
  rw [mollify, h1, ← integral_sub hint hintx]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_sub]

/-- **The Gårding-approximation estimate:** `‖x_φ − (∫φ)·x‖ ≤ ∫ ‖φ(t)‖ ‖U_t x − x‖ dt` (norm of the integral
    ≤ integral of the norm). With `φ ≥ 0` concentrated near `0` and `∫φ = 1`, the bound `→ 0` by strong
    continuity — this is the convergence `x_φ → x` that makes the smooth domain dense. -/
theorem norm_mollify_sub_le (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H)
    (hint : Integrable (fun t => φ t • U t x)) (hintx : Integrable (fun t => φ t • x)) :
    ‖mollify U φ x - (∫ t, φ t) • x‖ ≤ ∫ t, ‖φ t‖ * ‖U t x - x‖ := by
  rw [mollify_sub U φ x hint hintx]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul]

end QIQTH.Spectral
