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
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

/-- **The Gårding-approximation ε-bound:** if `‖U_t x − x‖ ≤ ε` wherever `φ(t) ≠ 0` (i.e. on `supp φ`), then
    `‖x_φ − (∫φ)·x‖ ≤ ε · ∫ ‖φ‖`. For a Dirac sequence (`∫|φ| = 1`, `φ` supported in a shrinking neighborhood
    of `0`) this is `≤ ε` and `→ 0` by strong continuity — the convergence `x_φ → x` driving density of the
    smooth domain. -/
theorem norm_mollify_sub_le_uniform (U : ℝ → (H →L[ℂ] H)) (φ : ℝ → ℂ) (x : H) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ∀ t, φ t ≠ 0 → ‖U t x - x‖ ≤ ε) (hφ_int : Integrable φ)
    (hint : Integrable (fun t => φ t • U t x)) (hintx : Integrable (fun t => φ t • x)) :
    ‖mollify U φ x - (∫ t, φ t) • x‖ ≤ ε * ∫ t, ‖φ t‖ := by
  refine le_trans (norm_mollify_sub_le U φ x hint hintx) ?_
  have hf_int : Integrable (fun t => ‖φ t‖ * ‖U t x - x‖) := by
    have h2 : (fun t => ‖φ t‖ * ‖U t x - x‖) = fun t => ‖φ t • (U t x - x)‖ := by
      funext t; rw [norm_smul]
    rw [h2]
    exact ((hint.sub hintx).congr
      (Filter.Eventually.of_forall fun t => (smul_sub (φ t) (U t x) x).symm)).norm
  have hg_int : Integrable (fun t => ε * ‖φ t‖) := hφ_int.norm.const_mul ε
  calc ∫ t, ‖φ t‖ * ‖U t x - x‖
      ≤ ∫ t, ε * ‖φ t‖ := by
        refine integral_mono hf_int hg_int (fun t => ?_)
        rcases eq_or_ne (φ t) 0 with h0 | h0
        · simp [h0]
        · rw [mul_comm ε]
          exact mul_le_mul_of_nonneg_left (hε t h0) (norm_nonneg _)
    _ = ε * ∫ t, ‖φ t‖ := integral_const_mul ε _

/-- **A normalized Gårding mollifier yields a smooth-domain vector `ε`-close to `x`.** Combining
    `mollify_mem_stoneDomain` (the Gårding vector is in the smooth domain) with `norm_mollify_sub_le_uniform`
    (the `ε`-bound): if `φ ∈ C¹_c` averages to `x` (`(∫φ)·x = x`, true when `∫φ = 1`) and is supported where
    `‖U_t x − x‖ ≤ ε`, then `x_φ ∈ stoneDomain U` and `‖x_φ − x‖ ≤ ε · ∫‖φ‖`. With a Dirac bump (`∫‖φ‖ = 1`,
    support shrinking) this gives, for every `x` and `ε`, a smooth-domain vector within `ε` — i.e. **density of
    the smooth domain** (the remaining input to essential self-adjointness). The only missing piece is supplying
    such a bump (Mathlib `ContDiffBump.normed`). -/
theorem exists_mem_stoneDomain_norm_sub_le (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (φ φ' : ℝ → ℂ)
    (hφ' : ∀ y, HasDerivAt φ (φ' y) y) (hφcont : Continuous φ) (hsuppφ : HasCompactSupport φ)
    (hφ'cont : Continuous φ') (hsupp' : HasCompactSupport φ') (x : H) (ε M : ℝ)
    (hε0 : 0 ≤ ε) (hM : 0 ≤ M) (hUbd : ∀ t, ‖U t x‖ ≤ M) (hcont : Continuous (fun t => U t x))
    (hφ_int : Integrable φ) (hint : Integrable (fun t => φ t • U t x))
    (hintx : Integrable (fun t => φ t • x)) (hφone : (∫ t, φ t) • x = x)
    (hsmall : ∀ t, φ t ≠ 0 → ‖U t x - x‖ ≤ ε) :
    ∃ y ∈ stoneDomain U, ‖y - x‖ ≤ ε * ∫ t, ‖φ t‖ := by
  refine ⟨mollify U φ x, mollify_mem_stoneDomain U hgrp φ φ' hφ' hφcont hsuppφ hφ'cont hsupp'
    x M hM hUbd hcont, ?_⟩
  have hrw : mollify U φ x - x = mollify U φ x - (∫ t, φ t) • x := by rw [hφone]
  rw [hrw]
  exact norm_mollify_sub_le_uniform U φ x ε hε0 hsmall hφ_int hint hintx

/-- **Strong continuity ⟹ the mollifier-support smallness condition.** For a family with `U_0 = 1` and
    `t ↦ U_t x` continuous, for every `ε > 0` there is `δ > 0` with `‖U_t x − x‖ < ε` for `|t| < δ`. A
    mollifier supported in `(−δ, δ)` then satisfies the `hsmall` hypothesis of
    `exists_mem_stoneDomain_norm_sub_le` — the bridge from the `C₀`-group hypothesis to density. -/
theorem exists_delta_norm_sub_lt (U : ℝ → (H →L[ℂ] H)) (hU0 : U 0 = 1) (x : H)
    (hcont : Continuous (fun t => U t x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ‖U t x - x‖ < ε := by
  have h0 : U 0 x = x := by rw [hU0, ContinuousLinearMap.one_apply]
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuous_iff.mp hcont) 0 ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h := hδ' t (by rw [Real.dist_eq, sub_zero]; exact ht)
  rwa [h0, dist_eq_norm] at h

set_option maxHeartbeats 1000000 in
/-- **★★ The smooth domain of the Stone generator is DENSE** for a contractive strongly-continuous family
    (`U_0 = 1`, `‖U_t y‖ ≤ ‖y‖`, `t ↦ U_t y` continuous). Proof: for `x` and `r > 0`, strong continuity gives
    `δ` with `‖U_t x − x‖ < r/2` for `|t| < δ` (`exists_delta_norm_sub_lt`); a normalized `C^∞` bump `φ`
    (`ContDiffBump.normed`, `ℝ → ℂ`-coerced) supported in `(−δ/2, δ/2)` then yields, via
    `exists_mem_stoneDomain_norm_sub_le`, a Gårding vector `x_φ ∈ stoneDomain U` with `‖x_φ − x‖ ≤ (r/2)·1 < r`.
    **This discharges the density hypothesis of `stoneGen_le_adjoint` — the last analytic input to essential
    self-adjointness of the Stone generator** (`X = A_edge`, `P`, `K`). -/
theorem stoneDomain_dense (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    Dense ((stoneDomain U : Set H)) := by
  rw [Metric.dense_iff]
  intro x r hr
  have hε : 0 < r / 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_norm_sub_lt U hU0 x (hSC x) (r / 2) hε
  let f : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  set φ : ℝ → ℂ := fun t => (g t : ℂ) with hφ
  set φ' : ℝ → ℂ := fun t => Complex.ofReal (deriv g t) with hφ'
  have hgC1 : ContDiff ℝ 1 g := f.contDiff_normed
  have hgcont : Continuous g := hgC1.continuous
  have hφcont : Continuous φ := Complex.continuous_ofReal.comp hgcont
  have hsuppg : HasCompactSupport g := f.hasCompactSupport_normed
  have hsuppφ : HasCompactSupport φ := hsuppg.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hφ'cont : Continuous φ' :=
    Complex.continuous_ofReal.comp (hgC1.continuous_deriv (le_refl 1))
  have hsuppφ' : HasCompactSupport φ' := hsuppg.deriv.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hderiv : ∀ y, HasDerivAt φ (φ' y) y := fun y =>
    ((hgC1.differentiable one_ne_zero).differentiableAt.hasDerivAt).ofReal_comp
  have hφint : Integrable φ := hφcont.integrable_of_hasCompactSupport hsuppφ
  have hint : Integrable (fun t => φ t • U t x) :=
    mollify_integrable U φ x (hSC x) hφcont hsuppφ
  have hintx : Integrable (fun t => φ t • x) :=
    (hφcont.smul continuous_const).integrable_of_hasCompactSupport hsuppφ.smul_right
  have hintegral : (∫ t, φ t) = 1 := by
    have hofr : (∫ t, φ t) = ((∫ t, g t : ℝ) : ℂ) := by simp only [hφ]; exact integral_ofReal
    rw [hofr, hg, f.integral_normed (μ := volume), Complex.ofReal_one]
  have hφone : (∫ t, φ t) • x = x := by rw [hintegral, one_smul]
  have hnorm1 : (∫ t, ‖φ t‖) = 1 := by
    have heq : (fun t => ‖φ t‖) = g := by
      funext t
      simp only [hφ, Complex.norm_real]
      exact abs_of_nonneg (f.nonneg_normed t)
    rw [heq, hg, f.integral_normed (μ := volume)]
  have hsmall : ∀ t, φ t ≠ 0 → ‖U t x - x‖ ≤ r / 2 := by
    intro t ht
    have htg : g t ≠ 0 := by
      intro h; apply ht; simp only [hφ, h, Complex.ofReal_zero]
    have htsupp : t ∈ Function.support g := Function.mem_support.mpr htg
    rw [hg, f.support_normed_eq (μ := volume), Metric.mem_ball, Real.dist_eq, sub_zero] at htsupp
    refine le_of_lt (hδ' t ?_)
    have hlt : |t| < δ / 2 := htsupp
    linarith
  obtain ⟨y, hy_mem, hy_le⟩ := exists_mem_stoneDomain_norm_sub_le U hgrp φ φ' hderiv hφcont hsuppφ
    hφ'cont hsuppφ' x (r / 2) ‖x‖ (le_of_lt hε) (norm_nonneg x) (fun t => hUbd t x) (hSC x)
    hφint hint hintx hφone hsmall
  refine ⟨y, ?_, hy_mem⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖y - x‖ ≤ (r / 2) * ∫ t, ‖φ t‖ := hy_le
    _ = r / 2 := by rw [hnorm1, mul_one]
    _ < r := by linarith

/-! ### The resolvent `R = (1 − iA)⁻¹` (toward `Range(A ± i)` dense)

Essential self-adjointness of the symmetric generator `A = stoneGen U` needs `Range(A ± i)` dense. The classical
witness is the **resolvent** of a one-parameter unitary group: for a contraction-bounded group,
`R x := ∫₀^∞ e^{−t} U_t x dt` is a bounded operator equal to `(1 − iA)⁻¹` (since formally
`∫₀^∞ e^{−t} e^{itA} dt = (1 − iA)⁻¹`), so `(1 − iA) = −i(A + i)` is surjective and `Range(A + i) = H`. This file
lays its foundation: the half-line integrand `e^{−t} U_t x` is integrable (exponential decay dominates the
bounded orbit). Showing `R x ∈ stoneDomain U` and the resolvent identity `(A + i)(R x) = i x` (differentiating
the half-line integral) is the genuine Mathlib-grade operator-theory frontier, built on this. -/

/-- The **resolvent integral** `R x = ∫₀^∞ e^{−t} U_t x dt = (1 − iA)⁻¹ x` for the generator `A` of `U_t`. -/
noncomputable def resolvent (U : ℝ → (H →L[ℂ] H)) (x : H) : H :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) • U t x

/-- The resolvent integrand `t ↦ e^{−t} U_t x` is integrable on `(0, ∞)`: exponential decay `e^{−t}` dominates
    the uniformly-bounded orbit (`‖U_t x‖ ≤ ‖x‖`), and `∫₀^∞ e^{−t} dt < ∞` (`exp_neg_integrableOn_Ioi`). -/
theorem resolvent_integrand_integrableOn (U : ℝ → (H →L[ℂ] H)) (x : H)
    (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    IntegrableOn (fun t => Real.exp (-t) • U t x) (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (fun t => Real.exp (-t) * ‖x‖) (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-1 * t)) (Set.Ioi (0 : ℝ)) :=
      exp_neg_integrableOn_Ioi 0 one_pos
    simp only [neg_one_mul] at h1
    exact h1.mul_const ‖x‖
  refine Integrable.mono' hg
    ((Real.continuous_exp.comp continuous_neg).smul hcont).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hUbd t) (Real.exp_pos _).le

/-- **The resolvent is a contraction:** `‖R x‖ ≤ ‖x‖`. Since `‖e^{−t} U_t x‖ ≤ e^{−t}‖x‖` and `∫₀^∞ e^{−t} = 1`,
    `R = (1 − iA)⁻¹` is a bounded operator (norm `≤ 1`) — so `1 − iA = −i(A + i)` has a bounded right inverse, the
    step that will give `Range(A + i) = H`. -/
theorem norm_resolvent_le (U : ℝ → (H →L[ℂ] H)) (x : H)
    (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    ‖resolvent U x‖ ≤ ‖x‖ := by
  have hnormint : IntegrableOn (fun t => ‖Real.exp (-t) • U t x‖) (Set.Ioi (0 : ℝ)) :=
    (resolvent_integrand_integrableOn U x hUbd hcont).norm
  have hgint : IntegrableOn (fun t => Real.exp (-t) * ‖x‖) (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-1 * t)) (Set.Ioi (0 : ℝ)) :=
      exp_neg_integrableOn_Ioi 0 one_pos
    simp only [neg_one_mul] at h1
    exact h1.mul_const ‖x‖
  calc ‖resolvent U x‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖Real.exp (-t) • U t x‖ := by
        rw [resolvent]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * ‖x‖ := by
        refine setIntegral_mono_on hnormint hgint measurableSet_Ioi fun t _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hUbd t) (Real.exp_pos _).le
    _ = (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) * ‖x‖ := integral_mul_const ‖x‖ _
    _ = 1 * ‖x‖ := by rw [integral_exp_neg_Ioi_zero]
    _ = ‖x‖ := one_mul _

/-- **The flow-on-resolvent identity** `U_s (R x) = ∫₀^∞ e^{−t} U_{s+t} x dt`: the bounded operator `U_s` passes
    through the (set) Bochner integral (`integral_comp_comm`), then the group law `U_s U_t = U_{s+t}` shifts the
    orbit. Differentiating its right side in `s` (after the change of variables `u = s+t`, giving
    `e^s ∫_s^∞ e^{−u} U_u x du`, whose `d/ds|₀ = R x − x` by the FTC) is what gives the resolvent identity
    `(A + i)(R x) = i x` — the route to `Range(A + i) = H`. -/
theorem resolvent_apply_flow (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) (s : ℝ) :
    U s (resolvent U x) = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) • U (s + t) x := by
  rw [resolvent, ← ContinuousLinearMap.integral_comp_comm (U s)
      (resolvent_integrand_integrableOn U x hUbd hcont)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [ContinuousLinearMap.map_smul_of_tower, ← ContinuousLinearMap.comp_apply, ← hgrp s t]

/-- **The resolvent is additive:** `R (x + y) = R x + R y` (linearity of the integral + `U_t` linear). -/
theorem resolvent_add (U : ℝ → (H →L[ℂ] H)) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (x y : H) :
    resolvent U (x + y) = resolvent U x + resolvent U y := by
  rw [resolvent, resolvent, resolvent,
    ← integral_add (resolvent_integrand_integrableOn U x (fun t => hUbd t x) (hSC x))
      (resolvent_integrand_integrableOn U y (fun t => hUbd t y) (hSC y))]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [map_add, smul_add]

/-- **The resolvent is ℂ-homogeneous:** `R (c • x) = c • R x` (`integral_smul` + `U_t` ℂ-linear). With
    `resolvent_add` and the contraction bound `norm_resolvent_le`, `R` is a bounded ℂ-linear operator. -/
theorem resolvent_smul (U : ℝ → (H →L[ℂ] H)) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (c : ℂ) (x : H) :
    resolvent U (c • x) = c • resolvent U x := by
  rw [resolvent, resolvent, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [map_smul, smul_comm]

/-- **The resolvent commutes with the flow:** `U_s (R x) = R (U_s x)`. From `resolvent_apply_flow`
    (`U_s (R x) = ∫₀^∞ e^{−t} U_{s+t} x dt`) and `R (U_s x) = ∫₀^∞ e^{−t} U_t (U_s x) dt = ∫₀^∞ e^{−t} U_{t+s} x dt`
    (group law), which agree since `U_{s+t} = U_{t+s}`. So `R` commutes with `U_s`, hence with the generator
    `A` — a resolvent/spectral consistency property. -/
theorem resolvent_comm_flow (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) (s : ℝ) :
    U s (resolvent U x) = resolvent U (U s x) := by
  rw [resolvent_apply_flow U hgrp x hUbd hcont s, resolvent]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← ContinuousLinearMap.comp_apply, ← hgrp t s, add_comm s t]

/-- **The resolvent orbit in differentiation-ready form:** `U_s (R x) = e^s ∫_s^∞ e^{−u} U_u x du`. Change of
    variables `u = s + t` (`setIntegral_preimage_emb` for the translation, `preimage_add_const_Ioi`) applied to
    `resolvent_apply_flow`, pulling out `e^s`. Now the `s`-dependence sits in the smooth `e^s` factor and the
    *integration limit* `s` only — so the FTC for the improper integral with variable lower limit gives
    `d/ds|₀ = R x − x`, placing `R x` in the smooth domain and yielding the resolvent identity `(A + i)(R x) = i x`. -/
theorem resolvent_apply_flow_cov (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) (s : ℝ) :
    U s (resolvent U x) = Real.exp s • ∫ u in Set.Ioi s, Real.exp (-u) • U u x := by
  rw [resolvent_apply_flow U hgrp x hUbd hcont s]
  have hpre : (fun t : ℝ => t + s) ⁻¹' Set.Ioi s = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have heq : (∫ u in Set.Ioi s, Real.exp (-u) • U u x)
      = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t + s)) • U (t + s) x := by
    have h := (measurePreserving_add_right volume s).setIntegral_preimage_emb
      (MeasurableEquiv.addRight s).measurableEmbedding
      (fun u => Real.exp (-u) • U u x) (Set.Ioi s)
    rw [hpre] at h
    exact h.symm
  rw [heq, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_smul, ← Real.exp_add, show s + -(t + s) = -t by ring, add_comm s t]

/-- The resolvent integrand is integrable on `(a, ∞)` for any lower limit `a` (exponential decay; generalizes
    `resolvent_integrand_integrableOn`, needed for the FTC splitting `∫_{Ioi s} = ∫_{Ioi 0} − ∫_0^s`). -/
theorem resolvent_integrand_integrableOn_Ioi (U : ℝ → (H →L[ℂ] H)) (x : H) (a : ℝ)
    (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    IntegrableOn (fun t => Real.exp (-t) • U t x) (Set.Ioi a) := by
  have hg : IntegrableOn (fun t => Real.exp (-t) * ‖x‖) (Set.Ioi a) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-1 * t)) (Set.Ioi a) :=
      exp_neg_integrableOn_Ioi a one_pos
    simp only [neg_one_mul] at h1
    exact h1.mul_const ‖x‖
  refine Integrable.mono' hg
    ((Real.continuous_exp.comp continuous_neg).smul hcont).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hUbd t) (Real.exp_pos _).le

/-- **FTC for the resolvent's half-line integral:** `d/ds ∫_s^∞ e^{−u} U_u x du = −(e^{−s} U_s x)`. Via the
    splitting `∫_{Ioi s} = ∫_{Ioi s₀} − ∫_{s₀}^s` (`integral_Ioi_sub_Ioi'`) and the fundamental theorem of
    calculus (`integral_hasDerivAt_right`, the integrand continuous). This is the derivative of `G(s)` that
    feeds the product rule `d/ds (e^s G(s))|₀ = R x − x`, hence `R x ∈ stoneDomain U` and `(A + i)(R x) = i x`. -/
theorem resolvent_halfline_hasDerivAt (U : ℝ → (H →L[ℂ] H)) (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖)
    (hcont : Continuous (fun t => U t x)) (s : ℝ) :
    HasDerivAt (fun σ => ∫ u in Set.Ioi σ, Real.exp (-u) • U u x)
      (-(Real.exp (-s) • U s x)) s := by
  have hfcont : Continuous (fun u => Real.exp (-u) • U u x) :=
    (Real.continuous_exp.comp continuous_neg).smul hcont
  have hcongr : (fun σ => ∫ u in Set.Ioi σ, Real.exp (-u) • U u x)
      =ᶠ[nhds s] fun σ => (∫ u in Set.Ioi s, Real.exp (-u) • U u x)
        - ∫ u in s..σ, Real.exp (-u) • U u x := by
    refine Filter.Eventually.of_forall fun σ => ?_
    rw [eq_sub_iff_add_eq,
      ← intervalIntegral.integral_Ioi_sub_Ioi' (resolvent_integrand_integrableOn_Ioi U x s hUbd hcont)
        (resolvent_integrand_integrableOn_Ioi U x σ hUbd hcont)]
    abel
  have hftc : HasDerivAt (fun σ => ∫ u in s..σ, Real.exp (-u) • U u x)
      (Real.exp (-s) • U s x) s :=
    intervalIntegral.integral_hasDerivAt_right (hfcont.intervalIntegrable s s)
      (hfcont.stronglyMeasurableAtFilter volume (nhds s)) hfcont.continuousAt
  refine HasDerivAt.congr_of_eventuallyEq ?_ hcongr
  simpa using (hasDerivAt_const s (∫ u in Set.Ioi s, Real.exp (-u) • U u x)).sub hftc

/-- **The resolvent orbit is differentiable at `0` with derivative `R x − x`.** Product rule on the
    differentiation-ready form `U_s (R x) = e^s G(s)` (`resolvent_apply_flow_cov`): `d/ds(e^s G(s))|₀ =
    e^0 G(0) + e^0 G'(0) = R x + (−U_0 x) = R x − x`, using `G(0) = R x`, `G'(0) = −U_0 x`
    (`resolvent_halfline_hasDerivAt`), `U_0 = 1`. So **`R x` lies in the smooth domain** (the orbit is
    differentiable at `0`) and the derivative `R x − x` will give the resolvent identity `(A + i)(R x) = i x`. -/
theorem resolvent_orbit_hasDerivAt (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    HasDerivAt (fun s => U s (resolvent U x)) (resolvent U x - x) 0 := by
  have hfun : (fun s => U s (resolvent U x))
      = fun s => Real.exp s • ∫ u in Set.Ioi s, Real.exp (-u) • U u x := by
    funext s; exact resolvent_apply_flow_cov U hgrp x hUbd hcont s
  rw [hfun]
  have hprod := (Real.hasDerivAt_exp 0).smul (resolvent_halfline_hasDerivAt U x hUbd hcont 0)
  convert hprod using 1
  simp only [Real.exp_zero, one_smul, neg_zero, hU0, ContinuousLinearMap.one_apply]
  rw [show (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) • U u x) = resolvent U x from rfl]
  abel

/-- **★ The resolvent lands in the smooth domain:** `R x ∈ stoneDomain U`. The orbit `s ↦ U_s (R x)` is
    differentiable at `0` (`resolvent_orbit_hasDerivAt`). So *every* `R x` is a smooth vector — the resolvent
    maps `H` into the generator's domain, the key to `Range(A + i) = H`. -/
theorem resolvent_mem_stoneDomain (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    resolvent U x ∈ stoneDomain U :=
  (resolvent_orbit_hasDerivAt U hgrp hU0 x hUbd hcont).differentiableAt

/-- **★ The resolvent identity (generator form):** `A (R x) = −i (R x − x)`, i.e. `stoneGen U (R x) =
    −i (R x − x)`. From the orbit derivative `d/ds U_s(R x)|₀ = R x − x` and the generator identification
    `i • A y = d/ds U_s y|₀`. Equivalently `(A + i)(R x) = i x` — so `Range(A + i) ⊇ {i x : x ∈ H} = H`, the
    deficiency-index-zero fact that makes `A` essentially self-adjoint. -/
theorem resolvent_stoneGen (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (x : H) (hUbd : ∀ t, ‖U t x‖ ≤ ‖x‖) (hcont : Continuous (fun t => U t x)) :
    stoneGen U ⟨resolvent U x, resolvent_mem_stoneDomain U hgrp hU0 x hUbd hcont⟩
      = -Complex.I • (resolvent U x - x) := by
  apply stoneGen_eq_of_hasDerivAt
  convert resolvent_orbit_hasDerivAt U hgrp hU0 x hUbd hcont using 1
  rw [smul_smul, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]

section SelfAdjoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **★★ The Stone generator is contained in its adjoint, unconditionally:** `stoneGen U ⊆ (stoneGen U)†`
    for a contractive one-parameter *unitary* group. This combines `stoneGen_le_adjoint` (the conditional
    `A ⊆ A†`, needing density of the smooth domain) with `stoneDomain_dense` (which now *discharges* that
    density). The symmetric densely-defined generator is contained in its `LinearPMap` adjoint — the textbook
    "symmetric operator" statement, with the density hypothesis no longer carried. Self-adjointness `Ā = Ā†`
    of the closure then follows from the Cayley/`Range(A ± i)`-dense criterion (the remaining structural step;
    the Cayley estimates `‖(A±i)x‖² = ‖Ax‖²+‖x‖²` giving injectivity are already in `Spectral/Stone.lean`). -/
theorem stoneGen_subset_adjoint (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    stoneGen U ≤ (stoneGen U).adjoint :=
  stoneGen_le_adjoint U hgrp hU0 hUinner (stoneDomain_dense U hgrp hU0 hUbd hSC)

/-- **★ The Stone generator is closable; its closure `Ā` exists.** A symmetric densely-defined operator has a
    closed extension — its own adjoint `A†` (closed by `LinearPMap.adjoint_isClosed`, given the smooth domain is
    dense) — and `A ⊆ A†` (`stoneGen_subset_adjoint`), so `A` is closable (`IsClosable.leIsClosable`). This is
    the prerequisite for forming the closure `Ā = (stoneGen U).closure` and asking `Ā = Ā†` (self-adjointness). -/
theorem stoneGen_isClosable (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    (stoneGen U).IsClosable :=
  (LinearPMap.adjoint_isClosed (T := stoneGen U)
      (stoneDomain_dense U hgrp hU0 hUbd hSC)).isClosable.leIsClosable
    (stoneGen_subset_adjoint U hgrp hU0 hUinner hUbd hSC)

end SelfAdjoint

end QIQTH.Spectral
