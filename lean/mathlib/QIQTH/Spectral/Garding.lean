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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace QIQTH.Spectral

open MeasureTheory
open scoped CompactlySupported
open CompactlySupportedContinuousMap

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

/-- **★★ `A + i` is surjective: `Range(A + i) = H`.** For any `y`, the vector `z := R(−i y)` lies in the smooth
    domain (`resolvent_mem_stoneDomain`) and `(A + i) z = A z + i z = −i(z − (−i y)) + i z = i(−i y) = y`
    (`resolvent_stoneGen`). So the deficiency subspace `Range(A + i)^⊥ = ker(A† − i) = 0` — the
    essential-self-adjointness criterion (with the `A − i` mirror) for the Stone generator. -/
theorem stoneGen_add_I_surjective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    ∃ z : stoneDomain U, stoneGen U z + Complex.I • (z : H) = y := by
  have hmem := resolvent_mem_stoneDomain U hgrp hU0 (-Complex.I • y)
    (fun t => hUbd t (-Complex.I • y)) (hSC (-Complex.I • y))
  refine ⟨⟨resolvent U (-Complex.I • y), hmem⟩, ?_⟩
  have hgen : stoneGen U (⟨resolvent U (-Complex.I • y), hmem⟩ : stoneDomain U)
      = -Complex.I • (resolvent U (-Complex.I • y) - (-Complex.I • y)) :=
    resolvent_stoneGen U hgrp hU0 (-Complex.I • y)
      (fun t => hUbd t (-Complex.I • y)) (hSC (-Complex.I • y))
  rw [hgen]
  show -Complex.I • (resolvent U (-Complex.I • y) - (-Complex.I • y))
    + Complex.I • resolvent U (-Complex.I • y) = y
  rw [smul_sub, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, neg_smul]
  abel

/-- A smooth vector of `U` is a smooth vector of the **reversed group** `t ↦ U_{−t}` (the orbit `t ↦ U_{−t} x`
    is differentiable at `0`, `hasDerivAt_stoneGen_neg`). -/
theorem mem_stoneDomain_reversed (U : ℝ → (H →L[ℂ] H)) (x : H) (hx : x ∈ stoneDomain U) :
    x ∈ stoneDomain (fun t => U (-t)) :=
  (hasDerivAt_stoneGen_neg U ⟨x, hx⟩).differentiableAt

/-- **The reversed group's generator is `−A`:** `stoneGen (t ↦ U_{−t}) x = −stoneGen U x`. From
    `hasDerivAt_stoneGen_neg` (`d/dt U_{−t} x|₀ = −i A x`) and generator identification. The bridge that turns
    `Range(A + i) = H` for the reversed group into `Range(A − i) = H` for `A`. -/
theorem stoneGen_reversed_eq (U : ℝ → (H →L[ℂ] H)) (x : H) (hx : x ∈ stoneDomain U) :
    stoneGen (fun t => U (-t)) ⟨x, mem_stoneDomain_reversed U x hx⟩ = -(stoneGen U ⟨x, hx⟩) := by
  apply stoneGen_eq_of_hasDerivAt
  rw [smul_neg]
  exact hasDerivAt_stoneGen_neg U ⟨x, hx⟩

/-- Reverse of `mem_stoneDomain_reversed`: a smooth vector of `t ↦ U_{−t}` is a smooth vector of `U` (apply the
    backward-orbit derivative to the reversed group; `U_{−(−t)} = U_t`). -/
theorem mem_stoneDomain_of_reversed (U : ℝ → (H →L[ℂ] H)) (x : H)
    (hx : x ∈ stoneDomain (fun t => U (-t))) : x ∈ stoneDomain U := by
  have h := hasDerivAt_stoneGen_neg (fun t => U (-t)) ⟨x, hx⟩
  simp only [neg_neg] at h
  exact h.differentiableAt

/-- **★★ `A − i` is surjective: `Range(A − i) = H`** (the second deficiency index). Apply
    `stoneGen_add_I_surjective` to the reversed group `t ↦ U_{−t}` (whose generator is `−A`,
    `stoneGen_reversed_eq`) and the vector `−y`: the witness `w` gives `−A w + i w = −y`, i.e. `A w − i w = y`.
    Together with `stoneGen_add_I_surjective` (`Range(A + i) = H`), **both deficiency indices of the symmetric
    generator `A = stoneGen U` are zero** — the essential-self-adjointness criterion is met. -/
theorem stoneGen_sub_I_surjective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    ∃ z : stoneDomain U, stoneGen U z - Complex.I • (z : H) = y := by
  have hgrp' : ∀ s t, (fun r => U (-r)) (s + t) = (fun r => U (-r)) s ∘L (fun r => U (-r)) t := by
    intro s t; show U (-(s + t)) = U (-s) ∘L U (-t); rw [neg_add, hgrp]
  have hU0' : (fun r => U (-r)) 0 = 1 := by show U (-0) = 1; rw [neg_zero, hU0]
  have hUbd' : ∀ (t : ℝ) (w : H), ‖(fun r => U (-r)) t w‖ ≤ ‖w‖ := fun t w => hUbd (-t) w
  have hSC' : ∀ w : H, Continuous (fun t => (fun r => U (-r)) t w) := fun w => (hSC w).comp continuous_neg
  obtain ⟨wsub, hw⟩ := stoneGen_add_I_surjective (fun t => U (-t)) hgrp' hU0' hUbd' hSC' (-y)
  have hwmemU : (wsub : H) ∈ stoneDomain U := mem_stoneDomain_of_reversed U (wsub : H) wsub.2
  have hbridge : stoneGen (fun t => U (-t)) wsub = -(stoneGen U ⟨(wsub : H), hwmemU⟩) :=
    stoneGen_reversed_eq U (wsub : H) hwmemU
  rw [hbridge] at hw
  refine ⟨⟨(wsub : H), hwmemU⟩, ?_⟩
  show stoneGen U ⟨(wsub : H), hwmemU⟩ - Complex.I • (wsub : H) = y
  have hrw : stoneGen U ⟨(wsub : H), hwmemU⟩ - Complex.I • (wsub : H)
      = -(-(stoneGen U ⟨(wsub : H), hwmemU⟩) + Complex.I • (wsub : H)) := by abel
  rw [hrw, hw, neg_neg]

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

/-- **★★ The `+` deficiency subspace is trivial:** `ker(A† − i) = Range(A + i)^⊥ = 0`. If `y ⊥ Range(A + i)`
    (`⟪(A + i)x, y⟫ = 0` for all `x` in the domain) then `y = 0`: since `A + i` is surjective
    (`stoneGen_add_I_surjective`), `y = (A + i)z` for some `z`, so `⟪y, y⟫ = ⟪(A + i)z, y⟫ = 0`. One of the two
    vanishing deficiency indices that make `A = stoneGen U` essentially self-adjoint. -/
theorem deficiency_add_trivial (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H)
    (h : ∀ z : stoneDomain U, (inner ℂ (stoneGen U z + Complex.I • (z : H)) y : ℂ) = 0) :
    y = 0 := by
  obtain ⟨z, hz⟩ := stoneGen_add_I_surjective U hgrp hU0 hUbd hSC y
  have hyy := h z
  rw [hz] at hyy
  exact inner_self_eq_zero.mp hyy

/-- **★★ The `−` deficiency subspace is trivial:** `ker(A† + i) = Range(A − i)^⊥ = 0` (mirror of
    `deficiency_add_trivial`, via `stoneGen_sub_I_surjective`). The second vanishing deficiency index. With both,
    `A = stoneGen U` is essentially self-adjoint. -/
theorem deficiency_sub_trivial (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H)
    (h : ∀ z : stoneDomain U, (inner ℂ (stoneGen U z - Complex.I • (z : H)) y : ℂ) = 0) :
    y = 0 := by
  obtain ⟨z, hz⟩ := stoneGen_sub_I_surjective U hgrp hU0 hUbd hSC y
  have hyy := h z
  rw [hz] at hyy
  exact inner_self_eq_zero.mp hyy

/-- **★★ `ker(A† − i) = 0` (adjoint eigenvector form):** if `A† w = i w` then `w = 0`. Using the formal-adjoint
    relation `⟪A z, w⟫ = ⟪z, A† w⟫`, the condition `A† w = i w` makes `⟪(A + i) z, w⟫ = 0` for all `z`, so
    `w ⊥ Range(A + i) = H` ⟹ `w = 0` (`deficiency_add_trivial`). This is the precise input
    (`A†` has no `+i`-eigenvector) of the self-adjointness criterion. -/
theorem ker_adjoint_sub_I_trivial (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (w : H) (hw : w ∈ (stoneGen U).adjoint.domain)
    (heig : (stoneGen U).adjoint ⟨w, hw⟩ = Complex.I • w) : w = 0 := by
  apply deficiency_add_trivial U hgrp hU0 hUbd hSC w
  intro z
  have hfa := ((LinearPMap.adjoint_isFormalAdjoint (T := stoneGen U)
    (stoneDomain_dense U hgrp hU0 hUbd hSC)).symm) z ⟨w, hw⟩
  rw [heig] at hfa
  rw [inner_add_left, hfa, inner_smul_right, inner_smul_left, Complex.conj_I]
  ring

/-- **★★ `ker(A† + i) = 0` (adjoint eigenvector form):** if `A† w = −i w` then `w = 0` (mirror, via
    `deficiency_sub_trivial`). With `ker_adjoint_sub_I_trivial`, `A†` has *no* `±i`-eigenvectors — the textbook
    essential-self-adjointness criterion (`A ⊆ A†`, both deficiency subspaces trivial). -/
theorem ker_adjoint_add_I_trivial (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖)
    (hSC : ∀ y : H, Continuous (fun t => U t y)) (w : H) (hw : w ∈ (stoneGen U).adjoint.domain)
    (heig : (stoneGen U).adjoint ⟨w, hw⟩ = -Complex.I • w) : w = 0 := by
  apply deficiency_sub_trivial U hgrp hU0 hUbd hSC w
  intro z
  have hfa := ((LinearPMap.adjoint_isFormalAdjoint (T := stoneGen U)
    (stoneDomain_dense U hgrp hU0 hUbd hSC)).symm) z ⟨w, hw⟩
  rw [heig] at hfa
  rw [inner_sub_left, hfa, inner_smul_right, inner_smul_left, Complex.conj_I]
  ring

/-- **★★★ The Stone generator is self-adjoint: `A† = A`, `IsSelfAdjoint (stoneGen U)`.** The *basic criterion
    for self-adjointness*: a symmetric operator `A ⊆ A†` with `Range(A ± i) = H` is self-adjoint — no Cayley
    transform needed. Given `A ⊆ A†` (`stoneGen_subset_adjoint`), it remains to show `A† ⊆ A`: for
    `y ∈ dom(A†)`, surjectivity gives `z ∈ dom(A)` with `(A + i)z = (A† + i)y`; then `A†(y − z) = −i(y − z)`,
    so `y − z = 0` by `ker_adjoint_add_I_trivial`, hence `y = z ∈ dom(A)`. Thus `A = A†`. **This is the spectral
    theorem's hypothesis for `A = stoneGen U` (`X = A_edge`, `P`, `K`): the generator of a contractive
    strongly-continuous unitary group is a genuine self-adjoint unbounded operator.** -/
theorem stoneGen_isSelfAdjoint (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    IsSelfAdjoint (stoneGen U) := by
  have hsub : stoneGen U ≤ (stoneGen U).adjoint := stoneGen_subset_adjoint U hgrp hU0 hUinner hUbd hSC
  rw [LinearPMap.isSelfAdjoint_def]
  refine (LinearPMap.eq_of_le_of_domain_eq hsub (le_antisymm hsub.1 fun y hy => ?_)).symm
  obtain ⟨z, hz⟩ := stoneGen_add_I_surjective U hgrp hU0 hUbd hSC
    ((stoneGen U).adjoint ⟨y, hy⟩ + Complex.I • y)
  have hzadj : (z : H) ∈ (stoneGen U).adjoint.domain := hsub.1 z.2
  have hsubmem : y - (z : H) ∈ (stoneGen U).adjoint.domain := Submodule.sub_mem _ hy hzadj
  have hAz : (stoneGen U).adjoint ⟨(z : H), hzadj⟩ = stoneGen U z :=
    (hsub.2 (x := z) (y := ⟨(z : H), hzadj⟩) rfl).symm
  have heig : (stoneGen U).adjoint ⟨y - (z : H), hsubmem⟩ = -Complex.I • (y - (z : H)) := by
    have hpair : (⟨y - (z : H), hsubmem⟩ : (stoneGen U).adjoint.domain)
        = ⟨y, hy⟩ - ⟨(z : H), hzadj⟩ := rfl
    rw [hpair, LinearPMap.map_sub, hAz]
    have hzval : stoneGen U z
        = (stoneGen U).adjoint ⟨y, hy⟩ + Complex.I • y - Complex.I • (z : H) := by rw [← hz]; abel
    rw [hzval]; module
  have hzero : y - (z : H) = 0 :=
    ker_adjoint_add_I_trivial U hgrp hU0 hUbd hSC (y - (z : H)) hsubmem heig
  rw [sub_eq_zero.mp hzero]; exact z.2

/-- **★★ `A + i` is a bijection `dom(A) → H`** (the Cayley-transform foundation). Injective from the
    bounded-below estimate `‖x‖ ≤ ‖(A + i)x‖` (`stoneGen_norm_le_norm_add_smul_I`), surjective from
    `stoneGen_add_I_surjective`. So `(A + i)⁻¹ : H → dom(A)` exists, the building block of the Cayley transform
    `V = (A − i)(A + i)⁻¹` (a unitary, by the Cayley isometry `‖(A−i)x‖=‖(A+i)x‖`), whose bounded spectral
    measure transports to the unbounded spectral theorem for `A` ⟹ Stone. -/
theorem stoneGen_add_I_bijective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    Function.Bijective (fun z : stoneDomain U => stoneGen U z + Complex.I • (z : H)) := by
  refine ⟨fun z1 z2 h => ?_, fun y => stoneGen_add_I_surjective U hgrp hU0 hUbd hSC y⟩
  have hb := stoneGen_norm_le_norm_add_smul_I U hgrp hU0 hUinner (z1 - z2)
  have hz : stoneGen U (z1 - z2) + Complex.I • ((z1 - z2 : stoneDomain U) : H) = 0 := by
    have e1 : stoneGen U (z1 - z2) = stoneGen U z1 - stoneGen U z2 :=
      LinearPMap.map_sub (stoneGen U) z1 z2
    have e2 : ((z1 - z2 : stoneDomain U) : H) = (z1 : H) - (z2 : H) := rfl
    rw [e1, e2, smul_sub]
    have hrw : stoneGen U z1 - stoneGen U z2 + (Complex.I • (z1 : H) - Complex.I • (z2 : H))
        = (stoneGen U z1 + Complex.I • (z1 : H)) - (stoneGen U z2 + Complex.I • (z2 : H)) := by abel
    rw [hrw, show stoneGen U z1 + Complex.I • (z1 : H)
      = stoneGen U z2 + Complex.I • (z2 : H) from h, sub_self]
  rw [hz, norm_zero] at hb
  have hzz : ((z1 - z2 : stoneDomain U) : H) = 0 := norm_le_zero_iff.mp hb
  rw [Submodule.coe_sub, sub_eq_zero] at hzz
  exact Subtype.ext hzz

/-- The bijection `A + i : dom(A) ≃ H` (from `stoneGen_add_I_bijective`); its inverse `(A + i)⁻¹` is
    `(cayleyEquiv U ⋯).symm`. -/
noncomputable def cayleyEquiv (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    stoneDomain U ≃ H :=
  Equiv.ofBijective _ (stoneGen_add_I_bijective U hgrp hU0 hUinner hUbd hSC)

/-- **The Cayley transform `V = (A − i)(A + i)⁻¹`** of the self-adjoint generator `A = stoneGen U`: for `y ∈ H`,
    `V y = (A − i) z` where `z = (A + i)⁻¹ y` is the unique smooth vector with `(A + i)z = y`. -/
noncomputable def cayley (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    H :=
  stoneGen U ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y)
    - Complex.I • (((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : stoneDomain U) : H)

/-- **★★ The Cayley transform is an isometry:** `‖V y‖ = ‖y‖`. With `z = (A + i)⁻¹ y` (so `(A + i)z = y`),
    `‖V y‖ = ‖(A − i)z‖ = ‖(A + i)z‖ = ‖y‖` (the Cayley isometry `stoneGen_norm_cayley_eq`). Together with
    surjectivity (`A − i` also bijective) this makes `V` a **unitary** — the operator whose bounded spectral
    measure transports to the unbounded spectral theorem for the self-adjoint `A`. -/
theorem norm_cayley (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    ‖cayley U hgrp hU0 hUinner hUbd hSC y‖ = ‖y‖ := by
  rw [cayley]
  set z := (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y with hzdef
  have hz : stoneGen U z + Complex.I • (z : H) = y :=
    (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).apply_symm_apply y
  rw [stoneGen_norm_cayley_eq U hgrp hU0 hUinner z, hz]

/-- **`A − i` is a bijection `dom(A) → H`** (the mirror of `stoneGen_add_I_bijective`). Injective from the
    bounded-below estimate `‖x‖ ≤ ‖(A − i)x‖` (= `‖(A + i)x‖` by the Cayley isometry); surjective from
    `stoneGen_sub_I_surjective`. So `(A − i)⁻¹ : H → dom(A)` exists too. -/
theorem stoneGen_sub_I_bijective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    Function.Bijective (fun z : stoneDomain U => stoneGen U z - Complex.I • (z : H)) := by
  refine ⟨fun z1 z2 h => ?_, fun y => stoneGen_sub_I_surjective U hgrp hU0 hUbd hSC y⟩
  have hb := stoneGen_norm_le_norm_add_smul_I U hgrp hU0 hUinner (z1 - z2)
  rw [← stoneGen_norm_cayley_eq U hgrp hU0 hUinner (z1 - z2)] at hb
  have hz : stoneGen U (z1 - z2) - Complex.I • ((z1 - z2 : stoneDomain U) : H) = 0 := by
    have e1 : stoneGen U (z1 - z2) = stoneGen U z1 - stoneGen U z2 := LinearPMap.map_sub (stoneGen U) z1 z2
    have e2 : ((z1 - z2 : stoneDomain U) : H) = (z1 : H) - (z2 : H) := rfl
    rw [e1, e2, smul_sub]
    have hrw : stoneGen U z1 - stoneGen U z2 - (Complex.I • (z1 : H) - Complex.I • (z2 : H))
        = (stoneGen U z1 - Complex.I • (z1 : H)) - (stoneGen U z2 - Complex.I • (z2 : H)) := by abel
    rw [hrw, show stoneGen U z1 - Complex.I • (z1 : H) = stoneGen U z2 - Complex.I • (z2 : H) from h, sub_self]
  rw [hz, norm_zero] at hb
  have hzz : ((z1 - z2 : stoneDomain U) : H) = 0 := norm_le_zero_iff.mp hb
  rw [Submodule.coe_sub, sub_eq_zero] at hzz
  exact Subtype.ext hzz

/-- **★★ The Cayley transform `V = (A − i)(A + i)⁻¹` is a bijection of `H`** (hence, with `norm_cayley`, a
    **unitary**): `V = (A − i) ∘ (A + i)⁻¹` is the composition of the bijection `A − i : dom(A) → H`
    (`stoneGen_sub_I_bijective`) with the bijection `(A + i)⁻¹ : H → dom(A)` (`(cayleyEquiv).symm`). This is the
    operator whose bounded spectral measure (Mathlib gap) transports to the unbounded spectral theorem for `A`. -/
theorem cayley_bijective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    Function.Bijective (cayley U hgrp hU0 hUinner hUbd hSC) :=
  (stoneGen_sub_I_bijective U hgrp hU0 hUinner hUbd hSC).comp
    (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm.bijective

/-- `(A + i)⁻¹` is **additive**: `(A+i)⁻¹(y₁+y₂) = (A+i)⁻¹y₁ + (A+i)⁻¹y₂`. By injectivity of `A+i`, both sides
    map under `A+i` to `y₁+y₂` (using `LinearPMap.map_add` for `A`). -/
theorem cayleyEquiv_symm_add (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y₁ y₂ : H) :
    (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm (y₁ + y₂)
      = (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁
        + (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂ := by
  set e := cayleyEquiv U hgrp hU0 hUinner hUbd hSC with he
  apply e.injective
  have hL : e (e.symm (y₁ + y₂)) = y₁ + y₂ := Equiv.apply_symm_apply _ _
  have h1 : e (e.symm y₁) = y₁ := Equiv.apply_symm_apply _ _
  have h2 : e (e.symm y₂) = y₂ := Equiv.apply_symm_apply _ _
  have hR : e (e.symm y₁ + e.symm y₂) = e (e.symm y₁) + e (e.symm y₂) := by
    show stoneGen U (e.symm y₁ + e.symm y₂)
        + Complex.I • ((e.symm y₁ + e.symm y₂ : stoneDomain U) : H)
      = (stoneGen U (e.symm y₁) + Complex.I • (e.symm y₁ : H))
        + (stoneGen U (e.symm y₂) + Complex.I • (e.symm y₂ : H))
    have hadd : stoneGen U (e.symm y₁ + e.symm y₂)
        = stoneGen U (e.symm y₁) + stoneGen U (e.symm y₂) := LinearPMap.map_add (stoneGen U) _ _
    rw [hadd, show ((e.symm y₁ + e.symm y₂ : stoneDomain U) : H)
        = (e.symm y₁ : H) + (e.symm y₂ : H) from rfl, smul_add]
    abel
  rw [hL, hR, h1, h2]

/-- `(A + i)⁻¹` is **ℂ-homogeneous**: `(A+i)⁻¹(c•y) = c•(A+i)⁻¹y`. By injectivity of `A+i` (using
    `LinearPMap.map_smul` for `A` and `smul_comm` for the `i•` term). -/
theorem cayleyEquiv_symm_smul (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (c : ℂ) (y : H) :
    (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm (c • y)
      = c • (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y := by
  set e := cayleyEquiv U hgrp hU0 hUinner hUbd hSC with he
  apply e.injective
  have hL : e (e.symm (c • y)) = c • y := Equiv.apply_symm_apply _ _
  have h1 : e (e.symm y) = y := Equiv.apply_symm_apply _ _
  have hR : e (c • e.symm y) = c • e (e.symm y) := by
    show stoneGen U (c • e.symm y) + Complex.I • ((c • e.symm y : stoneDomain U) : H)
      = c • (stoneGen U (e.symm y) + Complex.I • (e.symm y : H))
    have hsmul : stoneGen U (c • e.symm y) = c • stoneGen U (e.symm y) :=
      LinearPMap.map_smul (stoneGen U) c _
    rw [hsmul, show ((c • e.symm y : stoneDomain U) : H) = c • (e.symm y : H) from rfl, smul_add,
      smul_comm Complex.I c]
  rw [hL, hR, h1]

/-- **★ The Cayley transform is additive:** `V(y₁+y₂) = V y₁ + V y₂` (from `cayleyEquiv_symm_add` +
    `LinearPMap.map_add`). -/
theorem cayley_add (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y₁ y₂ : H) :
    cayley U hgrp hU0 hUinner hUbd hSC (y₁ + y₂)
      = cayley U hgrp hU0 hUinner hUbd hSC y₁ + cayley U hgrp hU0 hUinner hUbd hSC y₂ := by
  simp only [cayley, cayleyEquiv_symm_add]
  have hadd : stoneGen U ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁
      + (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂)
      = stoneGen U ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁)
        + stoneGen U ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂) :=
    LinearPMap.map_add (stoneGen U) _ _
  rw [hadd,
    show (((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁
      + (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂ : stoneDomain U) : H)
      = ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁ : H)
      + ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂ : H) from rfl, smul_add]
  abel

/-- **★ The Cayley transform is ℂ-homogeneous:** `V(c•y) = c•V y` (from `cayleyEquiv_symm_smul` +
    `LinearPMap.map_smul`). -/
theorem cayley_smul (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (c : ℂ) (y : H) :
    cayley U hgrp hU0 hUinner hUbd hSC (c • y) = c • cayley U hgrp hU0 hUinner hUbd hSC y := by
  simp only [cayley, cayleyEquiv_symm_smul]
  have hsmul : stoneGen U (c • (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y)
      = c • stoneGen U ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y) :=
    LinearPMap.map_smul (stoneGen U) c _
  rw [hsmul,
    show ((c • (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : stoneDomain U) : H)
      = c • ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H) from rfl, smul_sub,
    smul_comm Complex.I c]

/-- **The Cayley transform as a ℂ-linear map** `V : H →ₗ[ℂ] H` (additive + homogeneous). -/
noncomputable def cayleyLM (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) : H →ₗ[ℂ] H where
  toFun := cayley U hgrp hU0 hUinner hUbd hSC
  map_add' := cayley_add U hgrp hU0 hUinner hUbd hSC
  map_smul' := cayley_smul U hgrp hU0 hUinner hUbd hSC

/-- **★★★ The Cayley transform `V = (A − i)(A + i)⁻¹` is a unitary** `H ≃ₗᵢ[ℂ] H`: a ℂ-linear (`cayleyLM`),
    bijective (`cayley_bijective`), norm-preserving (`norm_cayley`) equivalence. This is the bounded unitary
    operator of the spectral theorem — the object whose (bounded) spectral measure, transported back through the
    Cayley correspondence, yields the unbounded spectral theorem for the self-adjoint generator `A = stoneGen U`
    (`X = A_edge`, `P`, `K`). The transport + bounded-PVM spectral theorem are the genuine Mathlib-grade gap. -/
noncomputable def cayleyUnitary (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) : H ≃ₗᵢ[ℂ] H :=
  { LinearEquiv.ofBijective (cayleyLM U hgrp hU0 hUinner hUbd hSC) (cayley_bijective U hgrp hU0 hUinner hUbd hSC) with
    norm_map' := norm_cayley U hgrp hU0 hUinner hUbd hSC }

/-- **★★ The Cayley unitary is a unitary element of the C\*-algebra** `H →L[ℂ] H`: `star V * V = V * star V = 1`.
    Since `star ↑V = ↑V.symm` (`LinearIsometryEquiv.star_eq_symm`) and `V.symm ∘ V = V ∘ V.symm = id`. This places
    `V = (A − i)(A + i)⁻¹` into Mathlib's `unitary (H →L[ℂ] H)` group — the doorway to the **continuous functional
    calculus**: `V` is a normal (indeed unitary) C\*-algebra element, so `cfc f V` exists for continuous `f` and
    `spectrum ℂ V ⊆ circle`. (The *Borel/PVM* functional calculus — `∫ z dE` — is the remaining Mathlib gap.) -/
theorem cayley_mem_unitary (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff, LinearIsometryEquiv.star_eq_symm]
  refine ⟨?_, ?_⟩ <;> · ext x; simp

/-- **The Cayley unitary as an element of `unitary (H →L[ℂ] H)`** — the bundled C\*-algebra unitary, ready for
    Mathlib's `cfc`/`spectrum` machinery (toward the spectral theorem for the self-adjoint generator `A`). -/
noncomputable def cayleyUnitaryElt (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    unitary (H →L[ℂ] H) :=
  ⟨cayleyUnitary U hgrp hU0 hUinner hUbd hSC, cayley_mem_unitary U hgrp hU0 hUinner hUbd hSC⟩

/-- **★★ The spectrum of the Cayley unitary lies on the unit circle:** `spectrum ℂ V ⊆ sphere 0 1`. This is the
    geometric foundation of the spectral theorem for `V = (A − i)(A + i)⁻¹`: its (eventual) spectral measure — the
    circle-PVM — is supported on `S¹`, and the inverse Cayley map `z ↦ i(1 + z)(1 − z)⁻¹` pulls that circle (minus
    the excluded point `1`, the image of `∞`) back to the real spectrum of the self-adjoint generator
    `A = stoneGen U`. Free from `spectrum.subset_circle_of_unitary` applied to `cayley_mem_unitary`. -/
theorem cayley_spectrum_subset_circle (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) ⊆ Metric.sphere (0 : ℂ) 1 :=
  spectrum.subset_circle_of_unitary (cayley_mem_unitary U hgrp hU0 hUinner hUbd hSC)

/-- **★ The Cayley defect `1 − V`:** `y − V y = 2i · (A + i)⁻¹ y`. With `z = (A + i)⁻¹ y` (so `(A + i)z = y`),
    `y − V y = (Az + iz) − (Az − iz) = 2i·z`. -/
theorem cayley_one_sub (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    y - cayley U hgrp hU0 hUinner hUbd hSC y
      = (2 * Complex.I) • ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H) := by
  rw [cayley]
  set s := (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y with hs
  have h0 : (cayleyEquiv U hgrp hU0 hUinner hUbd hSC) s = y :=
    (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).apply_symm_apply y
  have hz : stoneGen U s + Complex.I • (s : H) = y := h0
  rw [← hz]
  module

/-- **★★ `1` is not an eigenvalue of the Cayley unitary `V`** — `ker(1 − V) = 0`, equivalently `y ↦ y − V y` is
    injective. This is the precise condition that `V = (A − i)(A + i)⁻¹` is the **Cayley transform of a
    (densely-defined) self-adjoint operator** `A`: from `cayley_one_sub`, `y − V y = 2i·(A + i)⁻¹ y`, and
    `(A + i)⁻¹` is injective. (The inverse Cayley map `A = i(1 + V)(1 − V)⁻¹` is thus well-defined on `ran(1 − V)`,
    the dense smooth domain — the route back from the circle-spectral data to the generator.) -/
theorem cayley_one_sub_injective (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    Function.Injective (fun y : H => y - cayley U hgrp hU0 hUinner hUbd hSC y) := by
  intro y₁ y₂ h
  simp only [cayley_one_sub] at h
  have hu : ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₁ : H)
      = ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y₂ : H) :=
    smul_right_injective H (mul_ne_zero (by norm_num) Complex.I_ne_zero) h
  exact (cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm.injective (Subtype.coe_injective hu)

/-- **★★ `1 − V` has dense range** — `ran(1 − V)` is dense in `H`. From `cayley_one_sub`,
    `y − V y = 2i·(A + i)⁻¹ y`, so `ran(1 − V) = 2i · ran((A + i)⁻¹) = 2i · dom(A)`, the smooth domain
    `stoneDomain U`, which is dense (`stoneDomain_dense`); scaling by the nonzero `2i` (a homeomorphism) preserves
    density. Together with `cayley_one_sub_injective` (`ker(1 − V) = 0`), this is the **full statement that `V` is
    the Cayley transform of a densely-defined self-adjoint operator** `A = i(1 + V)(1 − V)⁻¹` — the inverse Cayley
    is well-defined on a dense domain. -/
theorem cayley_one_sub_denseRange (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    DenseRange (fun y : H => y - cayley U hgrp hU0 hUinner hUbd hSC y) := by
  have hc : (2 * Complex.I) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hrange : Set.range (fun y : H => ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H))
      = (stoneDomain U : Set H) := by
    ext z
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨y, rfl⟩; exact ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y).2
    · exact ⟨cayleyEquiv U hgrp hU0 hUinner hUbd hSC ⟨z, hz⟩, by simp⟩
  have hf : DenseRange (fun y : H => ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H)) := by
    show Dense (Set.range (fun y : H => ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H)))
    rw [hrange]; exact stoneDomain_dense U hgrp hU0 hUbd hSC
  have hcomp : (fun y : H => y - cayley U hgrp hU0 hUinner hUbd hSC y)
      = (Homeomorph.smulOfNeZero (2 * Complex.I) hc)
        ∘ (fun y : H => ((cayleyEquiv U hgrp hU0 hUinner hUbd hSC).symm y : H)) := by
    funext y
    simp only [Function.comp_apply, Homeomorph.smulOfNeZero_apply]
    exact cayley_one_sub U hgrp hU0 hUinner hUbd hSC y
  rw [hcomp]
  exact (Homeomorph.smulOfNeZero (2 * Complex.I) hc).surjective.denseRange.comp hf
    (Homeomorph.smulOfNeZero (2 * Complex.I) hc).continuous

/-- **★ The spectrum of the Cayley unitary is compact:** `IsCompact (spectrum ℂ V)`. With
    `cayley_spectrum_subset_circle`, `spectrum ℂ V` is a **compact subset of the unit circle** `S¹`. This is the
    topological precondition the **Riesz–Markov–Kakutani** construction of the scalar spectral measures consumes:
    on the compact `σ(V)`, `C(σ(V)) = C_c(σ(V))`, so the positive functional `f ↦ ⟨x, cfc f V x⟩` (the continuous
    functional calculus is in hand since `V ∈ unitary`, and `H →L[ℂ] H` is a `StarOrderedRing`) yields a finite
    Borel measure `μ_x` on `S¹` by `RealRMK.rieszMeasure` — the first rung of the operator → PVM keystone. -/
theorem cayley_spectrum_isCompact (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    IsCompact (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
  spectrum.isCompact _

/-- **★ The Cayley unitary is star-normal:** `IsStarNormal V` (from `cayley_mem_unitary` via
    `isStarNormal_of_mem_unitary`) — the predicate the continuous functional calculus over `ℂ` requires. -/
theorem cayley_isStarNormal (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    IsStarNormal (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) :=
  isStarNormal_of_mem_unitary (cayley_mem_unitary U hgrp hU0 hUinner hUbd hSC)

/-- **★ Positive operator ⟹ nonnegative expectation:** for `0 ≤ T` in the C\*-order on `H →L[ℂ] H`,
    `0 ≤ re⟪x, T x⟫` for every `x`. This is the **functional-positivity step** of the operator → PVM construction:
    once the continuous functional calculus delivers `0 ≤ cfc f V` for `f ≥ 0` on `σ(V)` (`V ∈ unitary` is
    star-normal, so `cfc` applies; `H →L[ℂ] H` is a `StarOrderedRing`), this lemma gives that `f ↦ re⟪x, cfc f V x⟫`
    is a *positive* linear functional on `C(σ(V), ℝ)` — exactly the input `RealRMK.rieszMeasure` turns into the
    scalar spectral measure `μ_x` of `V`. Via `ContinuousLinearMap.nonneg_iff_isPositive` + `IsPositive`. -/
theorem nonneg_re_inner_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (x : H) :
    0 ≤ (inner ℂ x (T x) : ℂ).re :=
  ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT).re_inner_nonneg_right x

-- The ℂ-normal continuous functional calculus is a *local-instance theorem* in Mathlib
-- (`IsStarNormal.instContinuousFunctionalCalculus`, needs a nonempty spectrum, hence `Nontrivial`); enable it
-- here so `cfc` applies to the Cayley unitary `V` (the named generators `X=A_edge`, `P`, `K` live on nontrivial
-- spaces, so `[Nontrivial H]` is harmless).
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- **★★ The continuous functional calculus recovers `V` from the coordinate function:** `cfc id V = V`. This is
    the `C(σ(V))`-level form of the spectral statement `V = ∫_{S¹} z dE(z)` — the coordinate function `z ↦ z`,
    applied to `V` through its (continuous) spectral data, returns `V` itself. Once the bounded-PVM `E` on `S¹`
    exists (the genuine Mathlib gap), this *becomes* `V = ∫ z dE`; here it is the continuous-FC shadow of that
    identity, and the base case of the functional calculus `cfc f V` (with `cfc_map_id`) the scalar-measure
    construction integrates against. (`[Nontrivial H]`: the ℂ-normal CFC needs a nonempty spectrum; `X=A_edge`,
    `P`, `K` all live on nontrivial Hilbert spaces.) -/
theorem cayley_cfc_id [Nontrivial H] (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    cfc (id : ℂ → ℂ) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = cayleyUnitary U hgrp hU0 hUinner hUbd hSC :=
  cfc_id ℂ _ (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)

/-- **★ The continuous functional calculus of the constant `1` is the identity:** `cfc 1 V = 1`. The `C(σ(V))`-level
    form of `∫_{S¹} 1 dE = 1` — the **resolution of identity** / total mass of `V`'s spectral measure. With
    `cayley_cfc_id` (`cfc id V = V`, the first moment `∫ z dE = V`), these are the two defining moments the scalar
    spectral measures `μ_x` are pinned by: total mass `μ_x(σ(V)) = re⟪x, (cfc 1 V) x⟫ = ‖x‖²`, and first moment
    `∫ z dμ_x = re⟪x, (cfc id V) x⟫ = re⟪x, V x⟫`. -/
theorem cayley_cfc_one [Nontrivial H] (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (hU0 : U 0 = 1) (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    cfc (1 : ℂ → ℂ) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) = 1 :=
  cfc_one ℂ _ (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)

/-- **★★ The scalar spectral functional is positive on `|f|²` test functions:**
    `0 ≤ re⟪x, cfc (conj f · f) V x⟫` for any `f` continuous on `σ(V)`. Indeed
    `cfc (conj f · f) V = cfc (star f) V * cfc f V = (cfc f V)⋆ (cfc f V) ≥ 0` (`cfc_mul` + `cfc_star` +
    `star_mul_self_nonneg`), so the expectation is `‖cfc f V x‖² ≥ 0` by `nonneg_re_inner_nonneg`. Since the
    functions `conj f · f = |f|²` generate the nonnegative cone of `C(σ(V), ℝ)`, this is the **positivity of the
    Riesz–Markov functional** `g ↦ re⟪x, cfc g V x⟫` — the property `RealRMK.rieszMeasure` turns into the finite
    Borel scalar spectral measure `μ_x` of `V` (with `∫ g dμ_x = re⟪x, cfc g V x⟫`). -/
theorem cayley_cfc_sq_re_inner_nonneg [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H) :
    0 ≤ (inner ℂ x
      (cfc (fun z => star (f z) * f z) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  apply nonneg_re_inner_nonneg
  rw [cfc_mul (fun z => star (f z)) f _ hf.star hf, cfc_star]
  exact star_mul_self_nonneg _

/-- **★★ The Riesz–Markov functional is positive on the whole nonnegative cone:**
    `0 ≤ re⟪x, cfc g V x⟫` for any `g` continuous on `σ(V)` that is real and `≥ 0` there. Reduce to the square case
    (`cayley_cfc_sq_re_inner_nonneg`) via `g = |√g|²`: with `h z = √((g z).re)` (continuous, real),
    `conj(h)·h = g` on `σ(V)` (since `g` is real-nonneg there), so `cfc g V = cfc (conj h · h) V` (`cfc_congr`).
    This is the exact positivity hypothesis `g ↦ re⟪x, cfc g V x⟫` needs to be bundled as a positive linear
    functional `C_c(σ(V), ℝ) →ₚ[ℝ] ℝ` and fed to `RealRMK.rieszMeasure` ⟹ the scalar spectral measure `μ_x`. -/
theorem cayley_cfc_re_inner_nonneg_of_nonneg [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (g : ℂ → ℂ) (hg : ContinuousOn g (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hgnn : ∀ z ∈ spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H),
      0 ≤ (g z).re ∧ (g z).im = 0) (x : H) :
    0 ≤ (inner ℂ x (cfc g (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  have hcont : ContinuousOn (fun z => (Complex.ofReal (Real.sqrt (g z).re) : ℂ))
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_sqrt.comp_continuousOn (Complex.continuous_re.comp_continuousOn hg))
  have hpt : (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)).EqOn
      (fun z => star (Complex.ofReal (Real.sqrt (g z).re)) * Complex.ofReal (Real.sqrt (g z).re)) g := by
    intro z hz
    obtain ⟨hge, him⟩ := hgnn z hz
    show star (Complex.ofReal (Real.sqrt (g z).re)) * Complex.ofReal (Real.sqrt (g z).re) = g z
    rw [← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hge]
    apply Complex.ext <;> simp [him]
  have key := cayley_cfc_sq_re_inner_nonneg U hgrp hU0 hUinner hUbd hSC
    (fun z => Complex.ofReal (Real.sqrt (g z).re)) hcont x
  exact le_of_le_of_eq key
    (congrArg (fun T : H →L[ℂ] H => (inner ℂ x (T x)).re) (cfc_congr hpt))

/-- **★ The scalar spectral functional is additive:**
    `re⟪x, cfc (f + g) V x⟫ = re⟪x, cfc f V x⟫ + re⟪x, cfc g V x⟫` for `f, g` continuous on `σ(V)`. Via `cfc_add`
    + inner-product additivity — the additive half of the linearity of the Riesz–Markov functional. -/
theorem cayley_cfc_re_inner_add [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f g : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hg : ContinuousOn g (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (x : H) :
    (inner ℂ x (cfc (fun z => f z + g z) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re
      = (inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re
        + (inner ℂ x (cfc g (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  rw [cfc_add (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) (f := f) (g := g)
      (hf := hf) (hg := hg), ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]

/-- **★ The scalar spectral functional is ℝ-homogeneous:**
    `re⟪x, cfc (c • f) V x⟫ = c · re⟪x, cfc f V x⟫` for `c : ℝ`, `f` continuous on `σ(V)`. Via `cfc_const_mul`
    + `inner_smul_right` — the homogeneous half of the linearity of the Riesz–Markov functional. With
    `cayley_cfc_re_inner_add` and `cayley_cfc_re_inner_nonneg_of_nonneg`, `g ↦ re⟪x, cfc g V x⟫` is a **positive
    ℝ-linear functional** — every component `RealRMK.rieszMeasure` needs to produce `μ_x`. -/
theorem cayley_cfc_re_inner_smul [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (c : ℝ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (x : H) :
    (inner ℂ x (cfc (fun z => (c : ℂ) * f z) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re
      = c * (inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  rw [cfc_const_mul (c : ℂ) f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) hf,
    ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]

/-- **The expectation functional** `Φ_x : (H →L[ℂ] H) →L[ℂ] ℂ`, `T ↦ ⟪x, T x⟫`, bundled as a ℂ-linear continuous
    map (`innerSL ℂ x` ∘ the evaluation `T ↦ T x`). Precomposed with `cfcHom V` (the ⋆-algebra hom of the
    continuous functional calculus) and postcomposed with `Complex.reCLM`, this is exactly the Riesz–Markov
    functional `g ↦ re⟪x, cfc g V x⟫` whose positivity (`cayley_cfc_re_inner_nonneg_of_nonneg`) and linearity
    (`cayley_cfc_re_inner_add`/`_smul`) are now proven — the bundled object the `μ_x` construction packages as a
    `C_c(σ(V), ℝ) →ₚ[ℝ] ℝ` and feeds to `RealRMK.rieszMeasure`. -/
noncomputable def expectationCLM (x : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)

@[simp] theorem expectationCLM_apply (x : H) (T : H →L[ℂ] H) :
    expectationCLM x T = inner ℂ x (T x) := rfl

/-- **The real expectation functional** `T ↦ re⟪x, T x⟫` as an **ℝ-linear** continuous map
    `(H →L[ℂ] H) →L[ℝ] ℝ` (`Complex.reCLM ∘ Φ_x`, restricting scalars to `ℝ`). Precomposed with `cfcHom V` and
    restricted to the real continuous functions `C_c(σ(V), ℝ)`, this is the bundled Riesz–Markov functional
    `g ↦ re⟪x, cfc g V x⟫` — its positivity (`cayley_cfc_re_inner_nonneg_of_nonneg`) and ℝ-linearity
    (`cayley_cfc_re_inner_add`/`_smul`) are exactly the `→ₚ[ℝ]` data `RealRMK.rieszMeasure` consumes to build `μ_x`. -/
noncomputable def reExpectationCLM (x : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((expectationCLM x).restrictScalars ℝ)

@[simp] theorem reExpectationCLM_apply (x : H) (T : H →L[ℂ] H) :
    reExpectationCLM x T = (inner ℂ x (T x)).re := rfl

/-- **The Riesz–Markov functional on `C(σ(V), ℂ)`** as a bundled **ℝ-linear** continuous map
    `φ ↦ re⟪x, cfcHom V φ x⟫` = `reExpectationCLM x ∘ (cfcL V)|_ℝ`, where `cfcL V : C(σ(V), ℂ) →L[ℂ] (H →L[ℂ] H)`
    is the continuous functional calculus bundled as a CLM. Restricting the domain to the real functions
    `C_c(σ(V), ℝ)` (via the `ℝ↪ℂ` embedding) yields the positive ℝ-linear functional whose positivity
    (`cayley_cfc_re_inner_nonneg_of_nonneg`) `RealRMK.rieszMeasure` turns into the scalar spectral measure `μ_x`. -/
noncomputable def cfcReExpectationCLM [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ) →L[ℝ] ℝ :=
  (reExpectationCLM x).comp
    ((cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)).restrictScalars ℝ)

@[simp] theorem cfcReExpectationCLM_apply [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (φ : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ)) :
    cfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x φ
      = (inner ℂ x (cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC) φ x)).re := rfl

/-- **The Riesz–Markov functional on the REAL functions `C(σ(V), ℝ)`** as a bundled ℝ-linear continuous map:
    `g ↦ re⟪x, cfcHom V (↑∘g) x⟫` = `cfcReExpectationCLM x ∘ (ℝ↪ℂ)`, where the `ℝ↪ℂ` embedding is
    `Complex.ofRealCLM.compLeftContinuous (σ(V))` (postcompose each `g : C(σ(V),ℝ)` with `Complex.ofReal`). Since
    `σ(V)` is compact (`cayley_spectrum_isCompact`), `C(σ(V), ℝ) = C_c(σ(V), ℝ)`, so this is — up to that
    repackaging into `→ₚ[ℝ]` with the proven positivity — exactly the input `RealRMK.rieszMeasure` consumes to
    build the scalar spectral measure `μ_x`. -/
noncomputable def realCfcReExpectationCLM [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ) →L[ℝ] ℝ :=
  (cfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x).comp
    (ContinuousLinearMap.compLeftContinuous ℝ
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM)

@[simp] theorem realCfcReExpectationCLM_apply [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (g : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)) :
    realCfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x g
      = (inner ℂ x (cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)
          (ContinuousLinearMap.compLeftContinuous ℝ
            (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM g) x)).re := rfl

/-- **★★ The Riesz–Markov functional is monotone (positive):** `0 ≤ g ⟹ 0 ≤ realCfcReExpectationCLM x g` for
    `g : C(σ(V), ℝ)`. Bridging `cfcL ha (↑∘g) = cfcHom ha (↑∘g) = cfc (extend (↑∘g)) V` (`cfcL_apply` +
    `cfcHom_eq_cfc_extend`), the extended function is continuous on `σ(V)` and real-`≥ 0` there (it equals `↑(g ω)`
    on the spectrum), so `cayley_cfc_re_inner_nonneg_of_nonneg` applies. With the ℝ-linearity of
    `realCfcReExpectationCLM` (it is a CLM), this is exactly the `→o`/`monotone'` field that upgrades it to a
    **`C(σ(V), ℝ) →ₚ[ℝ] ℝ` positive linear functional** — the input `RealRMK.rieszMeasure` consumes to build `μ_x`. -/
theorem realCfcReExpectation_nonneg [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (g : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)) (hg : 0 ≤ g) :
    0 ≤ realCfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x g := by
  rw [realCfcReExpectationCLM_apply]
  set φ : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ) :=
    ContinuousLinearMap.compLeftContinuous ℝ
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM g with hφ
  have hbridge : cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC) φ
      = cfc (Function.extend Subtype.val φ (0 : ℂ → ℂ))
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) := by
    rw [cfcL_apply]
    exact cfcHom_eq_cfc_extend 0 (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC) φ
  rw [hbridge]
  refine cayley_cfc_re_inner_nonneg_of_nonneg U hgrp hU0 hUinner hUbd hSC _ ?_ ?_ x
  · rw [continuousOn_iff_continuous_restrict]
    have h : (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)).restrict
        (Function.extend Subtype.val φ (0 : ℂ → ℂ)) = φ := by ext z; simp
    rw [h]; exact map_continuous φ
  · intro z hz
    have hval : φ ⟨z, hz⟩ = (Complex.ofReal (g ⟨z, hz⟩) : ℂ) := rfl
    have hz2 : Function.extend Subtype.val φ (0 : ℂ → ℂ) z = (Complex.ofReal (g ⟨z, hz⟩) : ℂ) :=
      (Subtype.val_injective.extend_apply φ (0 : ℂ → ℂ) ⟨z, hz⟩).trans hval
    rw [hz2]
    exact ⟨by rw [Complex.ofReal_re]; exact (ContinuousMap.le_def.mp hg) ⟨z, hz⟩,
      Complex.ofReal_im _⟩

/-- **★★★ The scalar spectral functional as a positive linear functional** `C(σ(V), ℝ) →ₚ[ℝ] ℝ`,
    `g ↦ re⟪x, cfc g V x⟫`. Bundles the ℝ-linear `realCfcReExpectationCLM x` with the monotonicity
    `realCfcReExpectation_nonneg` (a linear map is monotone iff `0 ≤ y ⟹ 0 ≤ f y`, via `f b − f a = f (b − a) ≥ 0`).
    This is **the input the Riesz–Markov–Kakutani theorem consumes**: transported to `C_c(σ(V), ℝ)` (compact
    spectrum) and fed to `RealRMK.rieszMeasure`, it yields the **scalar spectral measure `μ_x`** of `V` with
    `∫ g dμ_x = re⟪x, cfc g V x⟫` (total mass `‖x‖²`, first moment `re⟪x, V x⟫`). -/
noncomputable def cfcPLM [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := (realCfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x).toLinearMap
  monotone' := by
    intro a b hab
    have h := realCfcReExpectation_nonneg U hgrp hU0 hUinner hUbd hSC x (b - a) (sub_nonneg.mpr hab)
    rw [map_sub] at h
    exact sub_nonneg.mp h

@[simp] theorem cfcPLM_apply [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (g : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)) :
    cfcPLM U hgrp hU0 hUinner hUbd hSC x g
      = realCfcReExpectationCLM U hgrp hU0 hUinner hUbd hSC x g := rfl

/-- **★★★ The scalar spectral functional on the compactly-supported functions** `C_c(σ(V), ℝ) →ₚ[ℝ] ℝ`,
    `f ↦ re⟪x, cfc f V x⟫` — `cfcPLM` precomposed with the forgetful map `C_c(σ(V),ℝ) → C(σ(V),ℝ)` (the spectrum is
    compact, so this is a bijection). This is **exactly the type `RealRMK.rieszMeasure` consumes**: feeding it
    yields the scalar spectral measure `μ_x` of `V` with `∫ f dμ_x = re⟪x, cfc f V x⟫`. -/
noncomputable def cfcPLMcc [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    C_c(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ) →ₚ[ℝ] ℝ where
  toFun f := cfcPLM U hgrp hU0 hUinner hUbd hSC x f.toContinuousMap
  map_add' f g := by
    show cfcPLM U hgrp hU0 hUinner hUbd hSC x (f + g).toContinuousMap
      = cfcPLM U hgrp hU0 hUinner hUbd hSC x f.toContinuousMap
        + cfcPLM U hgrp hU0 hUinner hUbd hSC x g.toContinuousMap
    rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl]
    exact map_add (cfcPLM U hgrp hU0 hUinner hUbd hSC x) _ _
  map_smul' c f := by
    show cfcPLM U hgrp hU0 hUinner hUbd hSC x (c • f).toContinuousMap
      = c • cfcPLM U hgrp hU0 hUinner hUbd hSC x f.toContinuousMap
    rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl]
    exact map_smul (cfcPLM U hgrp hU0 hUinner hUbd hSC x) _ _
  monotone' f g hfg := (cfcPLM U hgrp hU0 hUinner hUbd hSC x).monotone'
    (ContinuousMap.le_def.mpr (CompactlySupportedContinuousMap.le_def.mp hfg))

/-- **★★★ The scalar spectral measure `μ_x` of the Cayley unitary `V`** — the finite Borel measure on `σ(V) ⊆ S¹`
    obtained by applying the **Riesz–Markov–Kakutani** representation theorem to the positive linear functional
    `cfcPLMcc x` (`f ↦ re⟪x, cfc f V x⟫`). By `RealRMK.integral_rieszMeasure`, `∫ f dμ_x = re⟪x, cfc f V x⟫` — in
    particular total mass `μ_x(σ(V)) = ‖x‖²` (from `cfc 1 V = 1`) and first moment `∫ z dμ_x = re⟪x, V x⟫` (from
    `cfc id V = V`). This is the scalar component of `V`'s (still-to-be-assembled) projection-valued measure. -/
noncomputable def cayleyScalarMeasure [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Measure (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  RealRMK.rieszMeasure (cfcPLMcc U hgrp hU0 hUinner hUbd hSC x)

/-- **★★★ The scalar spectral measure represents the functional:** `∫ f dμ_x = re⟪x, cfc f V x⟫` for every
    `f : C_c(σ(V), ℝ)` (the `↑∘f` here is the `ℝ↪ℂ` lift fed to the continuous functional calculus). This is the
    Riesz–Markov representation `RealRMK.integral_rieszMeasure` for the functional `cfcPLMcc x` — it pins `μ_x` to
    `V`: its moments are the expectations of the powers of `V` in the state `x`. -/
theorem cayleyScalarMeasure_integral [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (f : C_c(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)) :
    ∫ ω, f ω ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      = (inner ℂ x (cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)
          (ContinuousLinearMap.compLeftContinuous ℝ
            (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM
            f.toContinuousMap) x)).re := by
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  exact RealRMK.integral_rieszMeasure (cfcPLMcc U hgrp hU0 hUinner hUbd hSC x) f

/-- **★ The integral identity on `C(σ(V), ℝ)`** (compact-domain wrapper of `cayleyScalarMeasure_integral`):
    `∫ h dμ_x = re⟪x, cfcL ha (↑∘h) x⟫` for a *continuous* real `h : C(σ(V), ℝ)`.  Since `σ(V)` is compact, `h` is
    automatically compactly supported (`continuousMapEquiv`), so this is the `C_c` identity transported to `C`.
    This is the clean form the function-form CFC bridge (`re⟪x, cfc g V x⟫ = ∫ (g∘↑) dμ_x`) consumes — removing the
    `C_c` plumbing from the rest of the Stone/Parseval development (GPT-5.5-pro recipe, 2026-06-27). -/
theorem cayleyScalarMeasure_integral_C [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (h : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)) :
    ∫ ω, h ω ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      = (inner ℂ x (cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)
          (ContinuousLinearMap.compLeftContinuous ℝ
            (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM h) x)).re := by
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  exact cayleyScalarMeasure_integral U hgrp hU0 hUinner hUbd hSC x (continuousMapEquiv h)

/-- **★★ The function-form CFC ↔ measure bridge:** `re⟪x, cfc (↑∘r) V x⟫ = ∫ ω, r ω.1 dμ_x` for a *function*
    `r : ℂ → ℝ` continuous on `σ(V)`.  Bridges the function-form `cfc (g : ℂ → ℂ) V` (used by the operator-side
    identities like `cayley_cfc_norm_sq`) to the `μ_x`-integral (the measure side).  Proof: `cfc (↑∘r) V =
    cfcL ha (restrict (↑∘r)) = cfcL ha (↑∘(r∘↑))` (`cfc_eq_cfcL`), then `cayleyScalarMeasure_integral_C`.  This is
    the recurring dictionary entry the Stone/Parseval development needs (GPT-5.5-pro recipe, 2026-06-27) — e.g. it
    turns `cayley_cfc_sub_norm_sq` into the genuine L² identity `‖cfc f V x − cfc g V x‖² = ∫ |f−g|² dμ_x`. -/
theorem integral_re_cfc_ofReal [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (r : ℂ → ℝ) (hr : ContinuousOn r (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H) :
    (inner ℂ x (cfc (fun z => (r z : ℂ)) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re
      = ∫ ω, r ω.1 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  set hR : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ) :=
    ⟨fun ω => r ω.1, hr.comp_continuous continuous_subtype_val (fun ω => ω.2)⟩ with hRdef
  have hrC : ContinuousOn (fun z => (r z : ℂ))
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    Complex.continuous_ofReal.comp_continuousOn hr
  have hcfc : cfc (fun z => (r z : ℂ)) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)
          (ContinuousLinearMap.compLeftContinuous ℝ
            (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM hR) :=
    cfc_eq_cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC) hrC
  rw [hcfc]
  exact (cayleyScalarMeasure_integral_C U hgrp hU0 hUinner hUbd hSC x hR).symm

/-- **★ The scalar spectral measure is finite:** `IsFiniteMeasure μ_x`. Since `σ(V)` is compact, the Riesz–Markov
    measure of a positive functional on `C_c(σ(V), ℝ)` is finite (`RealRMK`'s `CompactSpace` instance). So `μ_x` is
    a genuine *finite* spectral distribution of the state `x` (total mass `‖x‖²`), and `∫ g dμ_x` is defined for
    every *bounded Borel* `g` — the extension beyond continuous functions that underlies the Borel functional
    calculus / the projection-valued measure `E(S) = ∫ 1_S dE`. -/
theorem cayleyScalarMeasure_isFiniteMeasure [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  exact inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (cfcPLMcc U hgrp hU0 hUinner hUbd hSC x)))

/-- **★★ Total mass of the scalar spectral measure: `μ_x(σ(V)) = ‖x‖²`.** Apply the integral identity at the
    constant function `1` (transported to `C_c` via `continuousMapEquiv` on the compact spectrum):
    `(μ_x univ).toReal = ∫ 1 dμ_x = re⟪x, cfc 1 V x⟫ = re⟪x, x⟫ = ‖x‖²` (using `cfc 1 V = 1`, `inner_self_eq_norm_sq`).
    So `μ_x` is the (Born-like) **spectral distribution of the state `x`**, of total mass `‖x‖²`. -/
theorem cayleyScalarMeasure_univ [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x Set.univ).toReal = ‖x‖ ^ 2 := by
  haveI : CompactSpace (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact _)
  have h := cayleyScalarMeasure_integral U hgrp hU0 hUinner hUbd hSC x
    (continuousMapEquiv (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ)))
  have hL : ∫ ω, (continuousMapEquiv (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ))) ω
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      = (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x Set.univ).toReal := by
    have hint : (∫ ω, (continuousMapEquiv (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ))) ω
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        = ∫ _, (1 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := rfl
    rw [hint, integral_const]; simp [measureReal_def]
  have hcomp : ContinuousLinearMap.compLeftContinuous ℝ
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) Complex.ofRealCLM
      (continuousMapEquiv (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ))).toContinuousMap
      = (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ)) := by
    ext ω
    show (Complex.ofRealCLM
        ((continuousMapEquiv (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℝ))).toContinuousMap ω)
      : ℂ) = (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ)) ω
    simp
  have hcfc : cfcL (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC)
      (1 : C(spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ℂ)) = 1 := by
    rw [cfcL_apply]; exact map_one (cfcHom (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC))
  rw [hL, hcomp, hcfc, ContinuousLinearMap.one_apply] at h
  rw [h]; simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- **★★ For a unit vector, the scalar spectral measure is a probability measure.** Since `μ_x(σ(V)) = ‖x‖²`
    (`cayleyScalarMeasure_univ`), a normalized state `‖x‖ = 1` gives `μ_x(σ(V)) = 1`: `μ_x` is the **Born/spectral
    probability distribution** of the outcome of measuring (a function of) `V` in the state `x`. This is the
    spectral-measure realization of the Born rule for the Cayley unitary of the self-adjoint generator. -/
theorem cayleyScalarMeasure_isProbabilityMeasure [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (x : H) (hx : ‖x‖ = 1) :
    IsProbabilityMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  have hmass := cayleyScalarMeasure_univ U hgrp hU0 hUinner hUbd hSC x
  rw [hx, one_pow] at hmass
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp hmass⟩

/-- **★★ The functional calculus of `V` is norm-bounded by the sup-norm:** `‖cfc f V‖ ≤ c` whenever `‖f z‖ ≤ c`
    on `σ(V)`. (The ℂ-normal continuous functional calculus on the C\*-algebra `H →L[ℂ] H` is isometric:
    `IsStarNormal.instIsometricContinuousFunctionalCalculus`.) This is the **boundedness of `f ↦ cfc f V`** that
    lets the functional calculus extend from continuous functions to *bounded Borel* functions (by approximation /
    the dominated-convergence over `μ_x`) — the analytic input to the Borel functional calculus and the
    projection-valued measure `E(S)`. -/
theorem cayley_norm_cfc_le [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ z ∈ spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ‖f z‖ ≤ c) :
    ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)‖ ≤ c :=
  norm_cfc_le hc h

/-- **★★ The functional calculus of a real function is a self-adjoint observable:** if `f` is real-valued on
    `σ(V)` (`(f z).im = 0`), then `IsSelfAdjoint (cfc f V)`. Since `star (cfc f V) = cfc (conj ∘ f) V = cfc f V`
    (`cfc_star` + `cfc_congr`, as `conj (f z) = f z` on `σ(V)`). So the spectral operators of real observables of
    `V` are self-adjoint — the bridge that makes `⟪x, cfc f V x⟫` *real* (`= ∫ f dμ_x`) and underlies the
    polarization `μ_{x,y}` toward the projection-valued measure. -/
theorem cayley_cfc_isSelfAdjoint [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (hf : ∀ z ∈ spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), (f z).im = 0) :
    IsSelfAdjoint (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
  rw [isSelfAdjoint_iff, ← cfc_star]
  refine cfc_congr ?_
  intro z hz
  show star (f z) = f z
  apply Complex.ext
  · simp
  · simp [hf z hz]

/-- **★ The expectation of a real spectral observable is real:** `(⟪x, cfc f V x⟫).im = 0` for `f` real on `σ(V)`.
    Immediate from `cayley_cfc_isSelfAdjoint` (`cfc f V` self-adjoint ⟹ `conj⟪x, cfc f V x⟫ = ⟪cfc f V x, x⟫ =
    ⟪x, cfc f V x⟫`, so the value is real). Hence `⟪x, cfc f V x⟫ = ↑(∫ f dμ_x)` — the **real** scalar spectral
    diagonal that the complex polarization `μ_{x,y}` extends to the off-diagonal toward the PVM. -/
theorem cayley_cfc_inner_self_im_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (hf : ∀ z ∈ spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), (f z).im = 0)
    (x : H) :
    (inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).im = 0 := by
  have hsa := cayley_cfc_isSelfAdjoint U hgrp hU0 hUinner hUbd hSC f hf
  have hadj : ContinuousLinearMap.adjoint (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
      = cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) := hsa
  have key : (starRingEnd ℂ) (inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
      = inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left, hadj]
  exact Complex.conj_eq_iff_im.mp key

/-- **★★ The spectral sesquilinear form is bounded:** `‖⟪x, cfc f V y⟫‖ ≤ c · ‖x‖ · ‖y‖` whenever `‖f z‖ ≤ c` on
    `σ(V)`. (Cauchy–Schwarz `‖⟪x, w⟫‖ ≤ ‖x‖‖w‖`, the operator-norm estimate `‖cfc f V y‖ ≤ ‖cfc f V‖‖y‖`, and the
    sup-norm bound `cayley_norm_cfc_le`.) This is the **boundedness of the sesquilinear form** `(x,y) ↦ ⟪x, cfc f V y⟫`
    — the analytic input that lets the form, extended to *bounded Borel* `f` (via `μ_{x,y}`), be **Riesz-represented
    by an operator** `f(V)`; for `f = 1_S` this is the projection `E(S)` of the projection-valued measure. -/
theorem cayley_norm_inner_cfc_le [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ z ∈ spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H), ‖f z‖ ≤ c) (x y : H) :
    ‖inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y)‖ ≤ c * ‖x‖ * ‖y‖ := by
  calc ‖(inner ℂ x (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) : ℂ)‖
      ≤ ‖x‖ * ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y‖ := norm_inner_le_norm x _
    _ ≤ ‖x‖ * (c * ‖y‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
        calc ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y‖
            ≤ ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)‖ * ‖y‖ :=
              ContinuousLinearMap.le_opNorm _ y
          _ ≤ c * ‖y‖ :=
              mul_le_mul_of_nonneg_right (cayley_norm_cfc_le U hgrp hU0 hUinner hUbd hSC f hc h) (norm_nonneg y)
    _ = c * ‖x‖ * ‖y‖ := by ring

/-- **★★ The spectral polarization identity:** the off-diagonal matrix element `⟪cfc f V y, x⟫` is the complex
    polarization combination of the four diagonals `⟪cfc f V z, z⟫` at `z = x ± y, x ± i y`. (Mathlib's
    `inner_map_polarization` for `(cfc f V).toLinearMap`.) Combined with the real diagonal
    (`cayley_cfc_inner_self_im_zero`, `⟪cfc f V z, z⟫ = ↑(∫ f dμ_z)` for real `f`), this expresses the **full
    sesquilinear form via the scalar spectral measures** `μ_z` — the formula that *defines* the bounded-Borel
    operator `f(V)` (and `E(S) = 1_S(V)`) once `f` is only bounded Borel: the heart of the PVM construction. -/
theorem cayley_cfc_inner_polarization [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (x y : H) :
    (inner ℂ (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) x : ℂ)
      = (inner ℂ (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (x + y)) (x + y)
          - inner ℂ (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (x - y)) (x - y)
          + Complex.I * inner ℂ (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
              (x + Complex.I • y)) (x + Complex.I • y)
          - Complex.I * inner ℂ (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
              (x - Complex.I • y)) (x - Complex.I • y)) / 4 :=
  inner_map_polarization (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)).toLinearMap x y

/-- **★ The diagonal spectral content is bounded by `‖x‖²`:** `μ_x(S) ≤ ‖x‖²` for every set `S` (`μ_x` is a finite
    measure of total mass `‖x‖²`, monotone in `S`). This is the bound the diagonal `⟪x, E(S) x⟫ = μ_x(S)` of the
    (still-to-be-assembled) spectral projection `E(S)` must satisfy — `0 ≤ E(S) ≤ 1` on the state `x` — and the
    boundedness that controls the Riesz representation of `(x,y) ↦ ∫ 1_S dμ_{x,y}` into `E(S)`. -/
theorem cayleyScalarMeasure_le_norm_sq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    (S : Set (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) :
    (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x S).toReal ≤ ‖x‖ ^ 2 := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  rw [← cayleyScalarMeasure_univ U hgrp hU0 hUinner hUbd hSC x]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ S))

/-- **★ Finite additivity of the spectral distribution over disjoint regions:**
    `μ_x(S ∪ T) = μ_x(S) + μ_x(T)` for disjoint measurable `S, T`. This is the diagonal shadow of the
    projection-valued measure's additivity `E(S ∪ T) = E(S) + E(T)` (and, normalized, the additivity of the
    **Born probabilities** over disjoint spectral outcomes) — a property the eventual PVM `E` refines to full
    σ-additivity. -/
theorem cayleyScalarMeasure_union [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H)
    {S T : Set (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))}
    (hT : MeasurableSet T) (hd : Disjoint S T) :
    (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x (S ∪ T)).toReal
      = (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x S).toReal
        + (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x T).toReal := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  rw [measure_union hd hT, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- **★★ The L²-isometry of the functional calculus (operator side):** `‖cfc f V x‖² = re⟪x, cfc (|f|²) V x⟫` for
    `f` continuous on `σ(V)` (`|f|² = conj f · f`).  Since `(cfc f V)⋆(cfc f V) = cfc (conj f · f) V` (`cfc_star` +
    `cfc_mul`) and `⟪x, (cfc f V)⋆(cfc f V) x⟫ = ⟪cfc f V x, cfc f V x⟫ = ‖cfc f V x‖²` (adjoint).  Combined with the
    integral identity (`re⟪x, cfc(|f|²) V x⟫ = ∫ |f|² dμ_x`) this is **Parseval/`‖cfc f V x‖² = ∫ |f|² dμ_x`** — the
    L² estimate behind the dominated-convergence / Cauchy argument that builds the Stone exponential
    `U_t = exp(it A)` as a strong limit of `cfc (e^{it·φₙ}) V x` (GPT-5.5-pro 2026-06-27). -/
theorem cayley_cfc_norm_sq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H) :
    ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = (inner ℂ x (cfc (fun z => star (f z) * f z)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  rw [cfc_mul (fun z => star (f z)) f _ hf.star hf, cfc_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simpa using (inner_self_eq_norm_sq
    (𝕜 := ℂ) (cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).symm

/-- **★★ The L²-distance estimate of the functional calculus:** `‖cfc f V x − cfc g V x‖² = re⟪x, cfc(|f−g|²) V x⟫`
    for `f, g` continuous on `σ(V)`.  Since `cfc f V − cfc g V = cfc (f − g) V` (`cfc_sub`), this is
    `cayley_cfc_norm_sq` at `f − g`.  Combined with the integral identity it is `‖cfc f V x − cfc g V x‖² =
    ∫ |f−g|² dμ_x` — **exactly the Cauchy / dominated-convergence estimate** that makes `n ↦ cfc (e^{it·φₙ}) V x`
    a Cauchy sequence (when `∫|φₙ−φₘ|²‑type quantities → 0`), defining the Stone exponential `U_t = exp(it A)` as a
    strong limit without a projection-valued measure (GPT-5.5-pro's endorsed route, 2026-06-27). -/
theorem cayley_cfc_sub_norm_sq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f g : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hg : ContinuousOn g (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (x : H) :
    ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
        - cfc g (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = (inner ℂ x (cfc (fun z => star (f z - g z) * (f z - g z))
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := by
  have hsub : cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
        - cfc g (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      = cfc (fun z => f z - g z) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x := by
    rw [cfc_sub (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) (f := f) (g := g)
      (hf := hf) (hg := hg), ContinuousLinearMap.sub_apply]
  rw [hsub]
  exact cayley_cfc_norm_sq U hgrp hU0 hUinner hUbd hSC (fun z => f z - g z) (hf.sub hg) x

/-- **★★★ The full Parseval / L²-distance identity in honest integral form:**
    `‖cfc f V x − cfc g V x‖² = ∫ ω, ‖f ω.1 − g ω.1‖² dμ_x` for `f, g` continuous on `σ(V)`.  This is the
    capstone of the CFC↔measure dictionary: it composes the operator-side L²-distance estimate
    (`cayley_cfc_sub_norm_sq`, giving `re⟪x, cfc(star(f−g)·(f−g)) V x⟫`) with the function-form bridge
    (`integral_re_cfc_ofReal`) at `r z = ‖f z − g z‖²`, using the pointwise ℂ-identity `star w · w = ↑‖w‖²`
    (`RCLike.conj_mul`).  The result is the genuine **Parseval/Cauchy estimate** in measure form: the strong
    limit `n ↦ cfc (e^{it·φₙ}) V x` is Cauchy **iff** `∫ ‖e^{itφₙ} − e^{itφₘ}‖² dμ_x → 0`, which is what defines
    the Stone exponential `U_t = exp(it A)` without a projection-valued measure (GPT-5.5-pro's endorsed route,
    2026-06-27).  Axiom-free; free scalar; no UV datum touched. -/
theorem cayley_cfc_sub_norm_sq_integral [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f g : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hg : ContinuousOn g (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (x : H) :
    ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
        - cfc g (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = ∫ ω, ‖f ω.1 - g ω.1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  have hfun : (fun z => star (f z - g z) * (f z - g z))
      = (fun z => ((‖f z - g z‖ ^ 2 : ℝ) : ℂ)) := by
    funext z
    rw [← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [cayley_cfc_sub_norm_sq U hgrp hU0 hUinner hUbd hSC f g hf hg x, hfun]
  exact integral_re_cfc_ofReal U hgrp hU0 hUinner hUbd hSC (fun z => ‖f z - g z‖ ^ 2)
    ((hf.sub hg).norm.pow 2) x

/-- **★★ The Parseval / L²-isometry identity in honest integral form:** `‖cfc f V x‖² = ∫ ω, ‖f ω.1‖² dμ_x`
    for `f` continuous on `σ(V)`.  The `f`-form companion of `cayley_cfc_sub_norm_sq_integral` (the `g = 0` case,
    proved directly): composes the operator-side L²-isometry `cayley_cfc_norm_sq` with the function-form bridge
    `integral_re_cfc_ofReal` at `r z = ‖f z‖²`, via the pointwise ℂ-identity `star w · w = ↑‖w‖²`
    (`RCLike.conj_mul`).  This is *the* Parseval identity the Stone/Borel-FC development repeatedly targets: the
    functional calculus `f ↦ cfc f V x` is an **L²(μ_x) → H isometry** on continuous functions — the core of the
    strong-limit Stone exponential `U_t = exp(it A)` (GPT-5.5-pro's endorsed route, 2026-06-27).  Axiom-free. -/
theorem cayley_cfc_norm_sq_integral [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (f : ℂ → ℂ) (hf : ContinuousOn f (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H) :
    ‖cfc f (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = ∫ ω, ‖f ω.1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  have hfun : (fun z => star (f z) * f z) = (fun z => ((‖f z‖ ^ 2 : ℝ) : ℂ)) := by
    funext z
    rw [← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [cayley_cfc_norm_sq U hgrp hU0 hUinner hUbd hSC f hf x, hfun]
  exact integral_re_cfc_ofReal U hgrp hU0 hUinner hUbd hSC (fun z => ‖f z‖ ^ 2) (hf.norm.pow 2) x

/-- **★★ The L² convergence engine for the strong-limit Stone exponential:** if a sequence of functions `F n`
    (each continuous on `σ(V)`) has `∫ ‖F n ω.1‖² dμ_x → 0`, then `cfc (F n) V x → 0` strongly in `H`.  Immediate
    from the Parseval identity `‖cfc (F n) V x‖² = ∫ ‖F n ω.1‖² dμ_x` (`cayley_cfc_norm_sq_integral`):
    `‖cfc(F n)V x‖² → 0` ⟹ `‖cfc(F n)V x‖ = √(‖·‖²) → 0` ⟹ `cfc(F n)V x → 0`.  This is the convergence half of the
    Cauchy/dominated-convergence machine that turns `L²(μ_x)`-limits of continuous functions into **strong limits
    of operators** — the device that (with rational cutoffs) kills the Cayley atom `μ_x({1}) = 0` and assembles
    `U_t = exp(it A)` as a strong limit, with NO projection-valued measure (GPT-5.5-pro route).  Axiom-free. -/
theorem cayley_cfc_tendsto_zero_of_integral [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, ContinuousOn (F n) (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H)
    (hint : Filter.Tendsto
      (fun n => ∫ ω, ‖F n ω.1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => cfc (F n) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      Filter.atTop (nhds 0) := by
  have heq : (fun n => ∫ ω, ‖F n ω.1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      = (fun n => ‖cfc (F n) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2) := by
    funext n
    exact (cayley_cfc_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (F n) (hF n) x).symm
  rw [heq] at hint
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hint
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  exact hsqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))

/-- **★★ The existence half of the operator-limit toolkit:** if a sequence of functions `F n` (each continuous on
    `σ(V)`) is **Cauchy in `L²(μ_x)`** — `∀ ε>0, ∃ N, ∀ m,n ≥ N, ∫ ‖F m ω.1 − F n ω.1‖² dμ_x < ε` — then the
    operator-vectors `cfc (F n) V x` form a **`CauchySeq` in `H`** (hence converge, `H` complete).  Immediate from
    the L²-distance Parseval identity `‖cfc (F m) V x − cfc (F n) V x‖² = ∫ ‖F m ω.1 − F n ω.1‖² dμ_x`
    (`cayley_cfc_sub_norm_sq_integral`): an `L²(μ_x)`-Cauchy condition at `ε²` gives `‖·‖² < ε²`, so `‖·‖ < ε`.
    Together with `cayley_cfc_tendsto_zero_of_integral` (the convergence half) this is the **full bridge**
    `L²(μ_x)` continuous-function limits ⟶ strong operator limits — the device that makes the rational-cutoff
    sequence `cfc (ψ_N) V x` converge (killing the Cayley atom `μ_x({1}) = 0`) and assembles the Stone exponential
    `U_t = exp(it A)` as a strong limit, with NO projection-valued measure (GPT-5.5-pro route).  Axiom-free. -/
theorem cayley_cfc_cauchySeq_of_integral [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, ContinuousOn (F n) (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (x : H)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ ω, ‖F m ω.1 - F n ω.1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε) :
    CauchySeq (fun n => cfc (F n) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have hpars := cayley_cfc_sub_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (F m) (F n) (hF m) (hF n) x
  have hlt : ‖cfc (F m) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      - cfc (F n) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2 < ε ^ 2 := by
    rw [hpars]; exact hN m hm n hn
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- **★★ The Cayley defect-energy identity:** `‖V x − x‖² = ∫ ω, ‖(ω : ℂ) − 1‖² dμ_x`.  The `f = z − 1`
    specialization of the Parseval f-isometry `cayley_cfc_norm_sq_integral`, using `cfc (z ↦ z − 1) V = V − 1`
    (`cfc_sub` + the keystones `cayley_cfc_id` `cfc id V = V` and `cayley_cfc_one` `cfc 1 V = 1`).  Quantitatively:
    the spectral mass weighted by the squared distance-to-`1` equals the **Cayley defect** `‖(V − 1) x‖²` — the
    integral that witnesses `ker(1 − V) = 0` (`cayley_one_sub_injective`).  The inverse-Cayley generator
    `A = i(1 + V)(1 − V)⁻¹` (whose spectral symbol is finite exactly off `ω = 1`) is obstructed only by the spectral
    **atom** `μ_x({1})` — whose vanishing (the next brick, via the L²→strong bridge + the rational cutoffs) makes the
    Stone exponential symbol `exp(it·invCayley(ω))` `μ_x`-a.e. defined.  Axiom-free; free scalar; no UV datum. -/
theorem cayley_defect_energy [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    ‖(cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x - x‖ ^ 2
      = ∫ ω, ‖(ω : ℂ) - 1‖ ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  have hcoord : cfc (fun z : ℂ => z - 1) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1 := by
    rw [show (fun z : ℂ => z - 1) = (fun z => (id : ℂ → ℂ) z - (1 : ℂ → ℂ) z) from by funext z; simp]
    rw [cfc_sub (f := (id : ℂ → ℂ)) (g := (1 : ℂ → ℂ))
      (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)),
      cayley_cfc_id U hgrp hU0 hUinner hUbd hSC, cayley_cfc_one U hgrp hU0 hUinner hUbd hSC]
  have hpars := cayley_cfc_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (fun z : ℂ => z - 1)
    ((continuous_id.sub continuous_const).continuousOn) x
  rw [hcoord, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hpars
  exact hpars

/-- **The rational cutoff sequence** `ψ_N(z) = (1 + (N+1)‖z − 1‖²)⁻¹` on `ℂ`.  As `N → ∞` it descends to the
    indicator of `{1}`: `ψ_N(1) = 1` for all `N`, while `ψ_N(z) → 0` for `z ≠ 1`.  Each `ψ_N` is continuous and
    valued in `(0, 1]`.  This is the approximation device that, fed through the L²(μ_x) → strong-operator bridge
    (`cayley_cfc_cauchySeq_of_integral` + `cayley_cfc_tendsto_zero_of_integral`), kills the Cayley spectral atom
    `μ_x({1}) = 0` (and so makes the inverse-Cayley / Stone exponential symbol `μ_x`-a.e. defined).  Pure analysis,
    independent of the operator `U`. -/
noncomputable def cayleyCutoff (N : ℕ) (z : ℂ) : ℝ := (1 + ((N : ℝ) + 1) * ‖z - 1‖ ^ 2)⁻¹

/-- The cutoff is strictly positive (its denominator is `≥ 1 > 0`). -/
theorem cayleyCutoff_pos (N : ℕ) (z : ℂ) : 0 < cayleyCutoff N z :=
  inv_pos.mpr (by positivity)

/-- The cutoff is bounded by `1` (its denominator is `≥ 1`); so `‖ψ_N‖ ≤ 1`, the integrable dominator for DCT. -/
theorem cayleyCutoff_le_one (N : ℕ) (z : ℂ) : cayleyCutoff N z ≤ 1 :=
  inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))

/-- Each cutoff `ψ_N` is continuous on `ℂ` (continuous denominator, bounded below by `1`). -/
theorem cayleyCutoff_continuous (N : ℕ) : Continuous (cayleyCutoff N) := by
  refine Continuous.inv₀ ?_ (fun z => by positivity)
  exact continuous_const.add
    (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))

/-- For `z ≠ 1` the cutoff vanishes in the limit: `ψ_N(z) → 0` (the denominator `→ ∞`). -/
theorem cayleyCutoff_tendsto_zero_of_ne {z : ℂ} (h : z ≠ 1) :
    Filter.Tendsto (fun N => cayleyCutoff N z) Filter.atTop (nhds 0) := by
  have hc : 0 < ‖z - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)) 2
  have hdiv : Filter.Tendsto (fun N : ℕ => 1 + ((N : ℝ) + 1) * ‖z - 1‖ ^ 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun N => ?_) (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
    nlinarith [hc.le, Nat.cast_nonneg (α := ℝ) N]
  exact hdiv.inv_tendsto_atTop

/-- **The pointwise limit of the cutoff sequence is the indicator of `{1}`:**
    `ψ_N(z) → (if z = 1 then 1 else 0)`.  At `z = 1` it is constantly `1`; off `1` it tends to `0`
    (`cayleyCutoff_tendsto_zero_of_ne`).  This is the convergence DCT consumes to evaluate `∫ ψ_N dμ_x → μ_x({1})`. -/
theorem cayleyCutoff_tendsto_indicator (z : ℂ) :
    Filter.Tendsto (fun N => cayleyCutoff N z) Filter.atTop (nhds (if z = 1 then (1 : ℝ) else 0)) := by
  by_cases h : z = 1
  · rw [if_pos h]
    have : (fun N : ℕ => cayleyCutoff N z) = (fun _ => (1 : ℝ)) := by
      funext N; simp [cayleyCutoff, h]
    rw [this]; exact tendsto_const_nhds
  · rw [if_neg h]; exact cayleyCutoff_tendsto_zero_of_ne h

/-- **The `(z − 1)`-weighted square of the cutoff vanishes pointwise:** `‖z − 1‖² · ψ_N(z)² → 0`.  At `z = 1` the
    factor `‖z − 1‖² = 0`; off `1`, `ψ_N(z) → 0`.  This is the integrand convergence DCT consumes to show
    `∫ ‖(ω − 1) ψ_N‖² dμ_x → 0` (dominated by the defect-energy integrand `‖ω − 1‖²`, `cayley_defect_energy`),
    which forces `(V − 1) w = 0` (hence `w = 0`) for the strong limit `w` of `cfc(ψ_N) V x`. -/
theorem cayleyCutoff_sq_mul_tendsto_zero (z : ℂ) :
    Filter.Tendsto (fun N => ‖z - 1‖ ^ 2 * (cayleyCutoff N z) ^ 2) Filter.atTop (nhds 0) := by
  by_cases h : z = 1
  · have : (fun N : ℕ => ‖z - 1‖ ^ 2 * (cayleyCutoff N z) ^ 2) = (fun _ => (0 : ℝ)) := by
      funext N; simp [h]
    rw [this]; exact tendsto_const_nhds
  · have ht := (cayleyCutoff_tendsto_zero_of_ne h).pow 2
    rw [show (0 : ℝ) = ‖z - 1‖ ^ 2 * (0 : ℝ) ^ 2 by ring]
    exact ht.const_mul (‖z - 1‖ ^ 2)

/-- **★★ The first dominated-convergence step of the atom-killing:** `∫ ψ_N(ω) dμ_x → μ_x({1})`, where `{1}` is
    the singleton `{ω ∈ σ(V) | (ω : ℂ) = 1}` (the Cayley exceptional point).  Dominated convergence
    (`tendsto_integral_of_dominated_convergence`) with the cutoff scaffolding: each `ψ_N ∘ ↑` is continuous (hence
    measurable), bounded by the integrable constant `1` (`cayleyCutoff_le_one`, `μ_x` finite), and converges
    pointwise to the indicator of `{1}` (`cayleyCutoff_tendsto_indicator`); the limit integral
    `∫ 𝟙_{{1}} dμ_x = μ_x({1})` is `integral_indicator_one`.  Combined with the integral identity
    `∫ ψ_N dμ_x = re⟪x, cfc(ψ_N) V x⟫`, this evaluates the diagonal limit of the spectral projection toward `1` —
    the value the strong limit `w = lim cfc(ψ_N) V x` must reproduce (and which `ker(1 − V) = 0` forces to `0`).
    Axiom-free; free scalar; no UV datum. -/
theorem cayleyCutoff_integral_tendsto_atom [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop
      (nhds ((cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x
        {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}).toReal)) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  set μ := cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x with hμ
  have hSmeas : MeasurableSet
      {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1} :=
    (isClosed_eq continuous_subtype_val continuous_const).measurableSet
  rw [show (μ {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}).toReal
      = ∫ ω, ({ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}).indicator
          (fun _ => (1 : ℝ)) ω ∂μ from (integral_indicator_one hSmeas).symm]
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
  · intro N
    exact ((cayleyCutoff_continuous N).comp continuous_subtype_val).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards with ω
    rw [Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
    exact cayleyCutoff_le_one N _
  · filter_upwards with ω
    have heq : ({ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}).indicator
        (fun _ => (1 : ℝ)) ω = if (ω : ℂ) = 1 then (1 : ℝ) else 0 := by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [heq]
    exact cayleyCutoff_tendsto_indicator (ω : ℂ)

/-- **★★ The third dominated-convergence step of the atom-killing:** `∫ ‖(ω − 1)·ψ_N(ω)‖² dμ_x → 0`.  Dominated
    convergence with the `(z−1)`-weighted cutoff: the integrand `‖(ω−1)·ψ_N‖² = ‖ω−1‖²·ψ_N²` is bounded by the
    integrable constant `4` (since `σ(V) ⊆ S¹` gives `‖(ω:ℂ)‖ = 1`, so `‖ω−1‖ ≤ 2`, and `ψ_N ≤ 1`), continuous
    (hence measurable), and tends pointwise to `0` (`cayleyCutoff_sq_mul_tendsto_zero`).  In the form
    `∫ ‖F_N ω.1‖² dμ_x → 0` with `F_N(z) = (z−1)·ψ_N(z)`, this feeds `cayley_cfc_tendsto_zero_of_integral` to give
    `(V−1)·cfc(ψ_N) V x = cfc((z−1)ψ_N) V x → 0` — which forces `(V−1) w = 0` (hence `w = 0` by
    `cayley_one_sub_injective`) for the strong limit `w = lim cfc(ψ_N) V x`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyCutoff_defect_integral_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, ‖((ω : ℂ) - 1) * ((cayleyCutoff N (ω : ℂ) : ℂ))‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  set μ := cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x with hμ
  rw [show (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂μ by simp]
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => (4 : ℝ))
  · intro N
    refine Continuous.aestronglyMeasurable ?_
    exact (((continuous_subtype_val.sub continuous_const).mul
      (Complex.continuous_ofReal.comp ((cayleyCutoff_continuous N).comp continuous_subtype_val))).norm.pow 2)
  · exact integrable_const 4
  · intro N
    filter_upwards with ω
    have hcirc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    have hsub : ‖(ω : ℂ) - 1‖ ≤ 2 := by
      calc ‖(ω : ℂ) - 1‖ ≤ ‖(ω : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hcirc]; norm_num
    have hpsi : ‖((cayleyCutoff N (ω : ℂ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
      exact cayleyCutoff_le_one N _
    rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
    have h1 : ‖(ω : ℂ) - 1‖ ^ 2 ≤ 4 := by nlinarith [hsub, norm_nonneg ((ω : ℂ) - 1)]
    have h2 : ‖((cayleyCutoff N (ω : ℂ) : ℂ))‖ ^ 2 ≤ 1 := by
      nlinarith [hpsi, norm_nonneg ((cayleyCutoff N (ω : ℂ) : ℂ))]
    calc ‖(ω : ℂ) - 1‖ ^ 2 * ‖((cayleyCutoff N (ω : ℂ) : ℂ))‖ ^ 2
        ≤ 4 * 1 := mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  · filter_upwards with ω
    have hfe : (fun N => ‖((ω : ℂ) - 1) * ((cayleyCutoff N (ω : ℂ) : ℂ))‖ ^ 2)
        = (fun N => ‖(ω : ℂ) - 1‖ ^ 2 * (cayleyCutoff N (ω : ℂ)) ^ 2) := by
      funext N
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
    rw [hfe]
    exact cayleyCutoff_sq_mul_tendsto_zero (ω : ℂ)

/-- **The cutoff approaches the indicator of `{1}` in pointwise `L²`:** `‖(ψ_N z : ℂ) − 1_{z=1}‖² → 0`.  At `z = 1`
    the cutoff is constantly `1` (= the indicator), so the difference is `0`; off `1`, `ψ_N(z) → 0` and the indicator
    is `0`.  The pointwise integrand convergence DCT-2 consumes to show `∫ ‖ψ_N − 1_{{1}}‖² dμ_x → 0` (the L²-Cauchy
    input). -/
theorem cayleyCutoff_sub_indicator_sq_tendsto_zero (z : ℂ) :
    Filter.Tendsto
      (fun N => ‖(cayleyCutoff N z : ℂ) - (if z = 1 then (1 : ℂ) else 0)‖ ^ 2) Filter.atTop (nhds 0) := by
  by_cases h : z = 1
  · simp only [if_pos h]
    have hfe : (fun N => ‖(cayleyCutoff N z : ℂ) - 1‖ ^ 2) = (fun _ => (0 : ℝ)) := by
      funext N
      have : (cayleyCutoff N z : ℂ) = 1 := by simp [cayleyCutoff, h]
      rw [this, sub_self, norm_zero]; norm_num
    rw [hfe]; exact tendsto_const_nhds
  · simp only [if_neg h]
    have hfe : (fun N => ‖(cayleyCutoff N z : ℂ) - 0‖ ^ 2) = (fun N => (cayleyCutoff N z) ^ 2) := by
      funext N
      rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
    rw [hfe]
    simpa using (cayleyCutoff_tendsto_zero_of_ne h).pow 2

/-- **★★ The second dominated-convergence step (the L²-Cauchy input):** `∫ ‖ψ_N(ω) − 1_{{1}}(ω)‖² dμ_x → 0`, i.e.
    the cutoff sequence converges to the indicator of `{1}` in `L²(μ_x)`.  Dominated convergence with the
    `(z − 1)`-free cutoff: the integrand `‖ψ_N − 1_{{1}}‖²` is bounded by the integrable constant `4`
    (`ψ_N ≤ 1`, `‖1_{{1}}‖ ≤ 1`), `AEStronglyMeasurable` (continuous cutoff minus the indicator of the measurable
    `{1}`), and `→ 0` pointwise (`cayleyCutoff_sub_indicator_sq_tendsto_zero`).  An `L²(μ_x)`-convergent sequence is
    `L²`-Cauchy, so this feeds `cayley_cfc_cauchySeq_of_integral` (via the triangle inequality) to give the **strong
    limit** `w = lim cfc(ψ_N) V x` (`H` complete) — the existence input the atom-killing needs.  Axiom-free. -/
theorem cayleyCutoff_L2_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, ‖(cayleyCutoff N (ω : ℂ) : ℂ)
          - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  set μ := cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x with hμ
  have hSmeas : MeasurableSet
      {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1} :=
    (isClosed_eq continuous_subtype_val continuous_const).measurableSet
  have hindeq : (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        if (ω : ℂ) = 1 then (1 : ℂ) else 0)
      = {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}.indicator
          (fun _ => (1 : ℂ)) := by
    funext ω; simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [show (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂μ by simp]
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => (4 : ℝ))
  · intro N
    have hg1 : AEStronglyMeasurable
        (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
          (cayleyCutoff N (ω : ℂ) : ℂ)) μ :=
      (Complex.continuous_ofReal.comp ((cayleyCutoff_continuous N).comp continuous_subtype_val)).aestronglyMeasurable
    have hg2 : AEStronglyMeasurable
        (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
          if (ω : ℂ) = 1 then (1 : ℂ) else 0) μ := by
      rw [hindeq]; exact (measurable_const.indicator hSmeas).aestronglyMeasurable
    exact (hg1.sub hg2).norm.pow 2
  · exact integrable_const 4
  · intro N
    filter_upwards with ω
    have hpsi : ‖(cayleyCutoff N (ω : ℂ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
      exact cayleyCutoff_le_one N _
    have hind : ‖(if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by
      by_cases hω : (ω : ℂ) = 1 <;> simp [hω]
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : ‖(cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ≤ 2 := by
      calc ‖(cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖
          ≤ ‖(cayleyCutoff N (ω : ℂ) : ℂ)‖ + ‖(if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    nlinarith [hb, norm_nonneg ((cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0))]
  · filter_upwards with ω
    exact cayleyCutoff_sub_indicator_sq_tendsto_zero (ω : ℂ)

/-- **★★★ The cutoff functional-calculus vectors form a Cauchy sequence:** `cfc(ψ_N) V x` is a `CauchySeq` in `H`
    (hence converges, `H` complete).  The existence input of the atom-killing.  Derivation: the cutoff sequence is
    `L²(μ_x)`-Cauchy — from DCT-2 (`cayleyCutoff_L2_tendsto_zero`, `∫ ‖ψ_N − 1_{{1}}‖² → 0`) and the pointwise
    quadratic triangle `‖a − b‖² ≤ 2‖a − c‖² + 2‖b − c‖²` (with `c = 1_{{1}}`) integrated via
    `integral_mono_of_nonneg`: `∫ ‖ψ_m − ψ_n‖² ≤ 2∫‖ψ_m − 1_{{1}}‖² + 2∫‖ψ_n − 1_{{1}}‖² < ε` for `m, n` large.
    Then `cayley_cfc_cauchySeq_of_integral` (the existence half of the L²→strong-operator bridge) turns the
    `L²(μ_x)`-Cauchy condition into a `CauchySeq` of operator-vectors.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyCutoff_cfc_cauchySeq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    CauchySeq (fun N => cfc (fun z => (cayleyCutoff N z : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- the indicator measurability / AESM
  have hSmeas : MeasurableSet
      {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1} :=
    (isClosed_eq continuous_subtype_val continuous_const).measurableSet
  have hindeq : (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        if (ω : ℂ) = 1 then (1 : ℂ) else 0)
      = {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}.indicator
          (fun _ => (1 : ℂ)) := by
    funext ω; simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hindm : AEStronglyMeasurable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        if (ω : ℂ) = 1 then (1 : ℂ) else 0) (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    rw [hindeq]; exact (measurable_const.indicator hSmeas).aestronglyMeasurable
  -- each ‖ψ_N − 1_{{1}}‖² is integrable (bounded by 4, finite measure)
  have hint : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        ‖(cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2)
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine (integrable_const (4 : ℝ)).mono' ?_ ?_
    · exact (((Complex.continuous_ofReal.comp
        ((cayleyCutoff_continuous N).comp continuous_subtype_val)).aestronglyMeasurable.sub hindm).norm.pow 2)
    · filter_upwards with ω
      have hpsi : ‖(cayleyCutoff N (ω : ℂ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
        exact cayleyCutoff_le_one N _
      have hind : ‖(if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases hω : (ω : ℂ) = 1 <;> simp [hω]
      have hb : ‖(cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ≤ 2 := by
        calc ‖(cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖
            ≤ ‖(cayleyCutoff N (ω : ℂ) : ℂ)‖ + ‖(if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [hb, norm_nonneg ((cayleyCutoff N (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0))]
  -- DCT-2: the L² norms tend to 0
  have hL2 := cayleyCutoff_L2_tendsto_zero U hgrp hU0 hUinner hUbd hSC x
  rw [Metric.tendsto_atTop] at hL2
  -- assemble the L²-Cauchy condition and invoke the existence half
  refine cayley_cfc_cauchySeq_of_integral U hgrp hU0 hUinner hUbd hSC
    (fun N z => (cayleyCutoff N z : ℂ))
    (fun N => (Complex.continuous_ofReal.comp (cayleyCutoff_continuous N)).continuousOn) x ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hL2 (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have key : ∀ k, N ≤ k → ∫ ω, ‖(cayleyCutoff k (ω : ℂ) : ℂ)
      - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε / 4 := by
    intro k hk
    have hd := hN k hk
    have hnn : 0 ≤ ∫ ω, ‖(cayleyCutoff k (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_nonneg (fun ω => sq_nonneg _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hd
  show ∫ ω, ‖(cayleyCutoff m (ω : ℂ) : ℂ) - (cayleyCutoff n (ω : ℂ) : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε
  calc ∫ ω, ‖(cayleyCutoff m (ω : ℂ) : ℂ) - (cayleyCutoff n (ω : ℂ) : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      ≤ ∫ ω, (2 * ‖(cayleyCutoff m (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
          + 2 * ‖(cayleyCutoff n (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2)
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
        · exact ((hint m).const_mul 2).add ((hint n).const_mul 2)
        refine Filter.Eventually.of_forall (fun ω => ?_)
        set a := (cayleyCutoff m (ω : ℂ) : ℂ)
        set b := (cayleyCutoff n (ω : ℂ) : ℂ)
        set c := (if (ω : ℂ) = 1 then (1 : ℂ) else 0)
        have h1 : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
          have he : a - b = (a - c) - (b - c) := by ring
          rw [he]; exact norm_sub_le _ _
        nlinarith [h1, norm_nonneg (a - b), norm_nonneg (a - c), norm_nonneg (b - c),
          sq_nonneg (‖a - c‖ - ‖b - c‖)]
    _ = 2 * (∫ ω, ‖(cayleyCutoff m (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        + 2 * (∫ ω, ‖(cayleyCutoff n (ω : ℂ) : ℂ) - (if (ω : ℂ) = 1 then (1 : ℂ) else 0)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) := by
        rw [integral_add ((hint m).const_mul 2) ((hint n).const_mul 2), integral_const_mul, integral_const_mul]
    _ < ε := by have hbm := key m hm; have hbn := key n hn; linarith

/-- **★★★ The cutoff functional-calculus vectors tend to `0`:** `cfc(ψ_N) V x → 0` strongly in `H`.  This is the
    operator heart of the atom-killing, assembling: (existence) the `CauchySeq` converges to some `w`
    (`cauchySeq_tendsto_of_complete` on `cayleyCutoff_cfc_cauchySeq`); (`(V−1)w = 0`) the defect
    `(V−1)·cfc(ψ_N) V x = cfc((z−1)ψ_N) V x → 0` (DCT-3 fed through `cayley_cfc_tendsto_zero_of_integral`, the
    convergence half) and also `→ (V−1)w` by continuity of `V−1`, so by uniqueness of limits `(V−1)w = 0`;
    (`w = 0`) `ker(1−V) = 0` (`cayley_one_sub_injective`).  Hence the limit is `0`.  Combined with
    `∫ ψ_N dμ_x = re⟪x, cfc(ψ_N) V x⟫ → re⟪x, 0⟫ = 0` and DCT-1, this kills the Cayley spectral atom `μ_x({1}) = 0`.
    Axiom-free; free scalar; no UV datum. -/
theorem cayleyCutoff_cfc_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto (fun N => cfc (fun z => (cayleyCutoff N z : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) Filter.atTop (nhds 0) := by
  -- (existence) the Cauchy sequence converges to some w
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cayleyCutoff_cfc_cauchySeq U hgrp hU0 hUinner hUbd hSC x)
  -- it suffices to show w = 0
  suffices hw0 : w = 0 by rwa [hw0] at hw
  -- cfc((z−1)ψ_N) V x = (V−1)(cfc(ψ_N) V x), the operator defect
  have hcoord : cfc (fun z : ℂ => z - 1) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1 := by
    rw [show (fun z : ℂ => z - 1) = (fun z => (id : ℂ → ℂ) z - (1 : ℂ → ℂ) z) from by funext z; simp]
    rw [cfc_sub (f := (id : ℂ → ℂ)) (g := (1 : ℂ → ℂ))
      (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)),
      cayley_cfc_id U hgrp hU0 hUinner hUbd hSC, cayley_cfc_one U hgrp hU0 hUinner hUbd hSC]
  have hid : ∀ N, cfc (fun z => (z - 1) * (cayleyCutoff N z : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      = ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1)
        (cfc (fun z => (cayleyCutoff N z : ℂ)) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
    intro N
    rw [cfc_mul (fun z => z - 1) (fun z => (cayleyCutoff N z : ℂ))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        ((continuous_id.sub continuous_const).continuousOn)
        (Complex.continuous_ofReal.comp (cayleyCutoff_continuous N)).continuousOn,
      ContinuousLinearMap.mul_apply, hcoord]
  -- the defect tends to 0 (DCT-3 through the convergence half)
  have hdefect := cayley_cfc_tendsto_zero_of_integral U hgrp hU0 hUinner hUbd hSC
    (fun N z => (z - 1) * (cayleyCutoff N z : ℂ))
    (fun N => ((continuous_id.sub continuous_const).mul
      (Complex.continuous_ofReal.comp (cayleyCutoff_continuous N))).continuousOn) x
    (cayleyCutoff_defect_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC x)
  simp only [hid] at hdefect
  -- the defect also tends to (V−1)w by continuity
  have hcont : Filter.Tendsto
      (fun N => ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1)
        (cfc (fun z => (cayleyCutoff N z : ℂ)) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
      Filter.atTop (nhds (((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1) w)) :=
    (((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1).continuous.tendsto w).comp hw
  -- uniqueness of limits ⟹ (V−1)w = 0
  have hVw : ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) - 1) w = 0 :=
    (tendsto_nhds_unique hdefect hcont).symm
  -- w = 0 via ker(1−V) = 0
  have hVwEq : (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) w = w := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hVw
    exact hVw
  apply cayley_one_sub_injective U hgrp hU0 hUinner hUbd hSC
  show w - cayley U hgrp hU0 hUinner hUbd hSC w = 0 - cayley U hgrp hU0 hUinner hUbd hSC 0
  rw [show cayley U hgrp hU0 hUinner hUbd hSC w
      = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) w from rfl, hVwEq, sub_self,
    show cayley U hgrp hU0 hUinner hUbd hSC 0
      = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) 0 from rfl, map_zero, sub_zero]

/-- **★★★ The Cayley spectral atom vanishes: `μ_x({1}) = 0`.**  The scalar spectral measure of the Cayley unitary
    `V = (A−i)(A+i)⁻¹` puts **no mass** on the exceptional point `1 ∈ S¹` (the image of `∞` under the inverse
    Cayley map).  Proof: DCT-1 (`cayleyCutoff_integral_tendsto_atom`) gives `∫ ψ_N dμ_x → μ_x({1})`; the integral
    identity `∫ ψ_N dμ_x = re⟪x, cfc(ψ_N) V x⟫` (`integral_re_cfc_ofReal`) and the strong limit
    `cfc(ψ_N) V x → 0` (`cayleyCutoff_cfc_tendsto_zero`, with inner-product and `re` continuity) give
    `∫ ψ_N dμ_x → re⟪x, 0⟫ = 0`; uniqueness of limits forces `μ_x({1}).toReal = 0`, hence `μ_x({1}) = 0` (`μ_x`
    finite).  **Consequence:** the inverse-Cayley / Stone-exponential symbol `exp(it·invCayley(ω))` — continuous and
    bounded off `ω = 1` — is now `μ_x`-a.e. defined, the precondition for building the strong-limit Stone exponential
    `U_t = exp(it A)`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyScalarMeasure_atom_eq_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x
      {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1} = 0 := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- ∫ ψ_N dμ_x = re⟪x, cfc(ψ_N) V x⟫
  have heq : ∀ N, ∫ ω, cayleyCutoff N (ω : ℂ)
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      = (inner ℂ x (cfc (fun z => (cayleyCutoff N z : ℂ))
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re := fun N =>
    (integral_re_cfc_ofReal U hgrp hU0 hUinner hUbd hSC (cayleyCutoff N)
      ((cayleyCutoff_continuous N).continuousOn) x).symm
  -- re⟪x, cfc(ψ_N) V x⟫ → 0  (from cfc(ψ_N) V x → 0, inner + re continuity)
  have htends : Filter.Tendsto (fun N => (inner ℂ x (cfc (fun z => (cayleyCutoff N z : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)).re) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun N => inner ℂ x (cfc (fun z => (cayleyCutoff N z : ℂ))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)) Filter.atTop (nhds (inner ℂ x (0 : H))) :=
      tendsto_const_nhds.inner (cayleyCutoff_cfc_tendsto_zero U hgrp hU0 hUinner hUbd hSC x)
    rw [inner_zero_right] at h2
    have h3 := (Complex.continuous_re.tendsto (0 : ℂ)).comp h2
    simpa using h3
  -- DCT-1: ∫ ψ_N dμ_x → μ_x({1}).toReal ; combined with heq it also → 0, so the atom's toReal is 0
  have hatom := cayleyCutoff_integral_tendsto_atom U hgrp hU0 hUinner hUbd hSC x
  rw [funext heq] at hatom
  have hreal : (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x
      {ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) | (ω : ℂ) = 1}).toReal = 0 :=
    tendsto_nhds_unique hatom htends
  rw [ENNReal.toReal_eq_zero_iff] at hreal
  rcases hreal with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- **The inverse Cayley map** `c(ω) = i(1 + ω)/(1 − ω)` on `ℂ \ {1}`.  It is the inverse of the Cayley transform
    `z ↦ (z − i)/(z + i)`: on the unit circle (minus the excluded point `1`, the image of `∞`) it returns the
    **real** spectral value of the self-adjoint generator `A = i(1 + V)(1 − V)⁻¹` whose Cayley transform is `V`.
    The Stone-exponential symbol is `ω ↦ exp(it · c(ω))`; since `c` is real on `σ(V) \ {1}` (`cayleyInv_im_eq_zero`)
    that symbol has modulus `1`, and since `μ_x({1}) = 0` (`cayleyScalarMeasure_atom_eq_zero`) it is `μ_x`-a.e.
    defined and bounded — the data the strong-limit Stone exponential `U_t = exp(it A)` consumes. -/
noncomputable def cayleyInv (ω : ℂ) : ℂ := Complex.I * (1 + ω) / (1 - ω)

/-- The inverse Cayley map is continuous off the excluded point `1` (the denominator `1 − ω` is nonzero there). -/
theorem cayleyInv_continuousOn : ContinuousOn cayleyInv {ω : ℂ | ω ≠ 1} :=
  (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn
    (fun _ hω => sub_ne_zero.mpr (Ne.symm hω))

/-- **The inverse Cayley map is real on the unit circle** (off `1`): `(c(ω)).im = 0` for `‖ω‖ = 1`, `ω ≠ 1`.
    This is the statement that the generator `A = i(1 + V)(1 − V)⁻¹` is **self-adjoint** (its spectral values are
    real), so the Stone-exponential symbol `exp(it · c(ω))` has modulus `1` (hence `U_t` is unitary).  Proof: on
    the circle `conj ω = ω⁻¹` (`RCLike.inv_eq_conj`), and a direct computation gives `conj(c(ω)) = c(ω)`
    (`field_simp`/`ring`), i.e. `c(ω)` is real. -/
theorem cayleyInv_im_eq_zero {ω : ℂ} (h1 : ‖ω‖ = 1) (hne : ω ≠ 1) : (cayleyInv ω).im = 0 := by
  have hcc : ω * (starRingEnd ℂ) ω = 1 := by rw [RCLike.mul_conj, h1]; norm_num
  have hd1 : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd2 : (1 : ℂ) - (starRingEnd ℂ) ω ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hne
    have : (starRingEnd ℂ) ((starRingEnd ℂ) ω) = (starRingEnd ℂ) 1 := congrArg _ h.symm
    simpa using this
  rw [← Complex.conj_eq_iff_im]
  simp only [cayleyInv, map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  rw [div_eq_div_iff hd2 hd1]
  linear_combination (2 * Complex.I) * hcc

/-- **The Stone-exponential symbol** `e_t(ω) = exp(i · t · c(ω))`, where `c = cayleyInv`.  This is the bounded Borel
    function whose functional calculus `cfc(e_t) V` *is* the Stone unitary `U_t = exp(it A)` of the self-adjoint
    generator `A = i(1 + V)(1 − V)⁻¹` (`A = cayleyInv(V)`).  It is continuous off the excluded point `1`
    (`cayleyExp_continuousOn`) and has **modulus `1`** on the unit circle off `1` (`cayleyExp_abs`, since `c` is real
    there) — so it is bounded.  Because `μ_x({1}) = 0` (`cayleyScalarMeasure_atom_eq_zero`) it is `μ_x`-a.e.
    continuous and bounded, hence approximable in `L²(μ_x)` by continuous functions, whose cfc-vectors converge
    (the L²→strong bridge) to define `U_t x` as a strong limit — the genuine continuum Stone exponential. -/
noncomputable def cayleyExp (t : ℝ) (ω : ℂ) : ℂ := Complex.exp (Complex.I * ((t : ℂ) * cayleyInv ω))

/-- The Stone-exponential symbol is continuous off the excluded point `1` (`exp` ∘ a function continuous there). -/
theorem cayleyExp_continuousOn (t : ℝ) : ContinuousOn (cayleyExp t) {ω : ℂ | ω ≠ 1} :=
  Complex.continuous_exp.comp_continuousOn
    ((cayleyInv_continuousOn.const_mul (t : ℂ)).const_mul Complex.I)

/-- **The Stone-exponential symbol has modulus `1` on the unit circle** (off `1`): `‖e_t(ω)‖ = 1` for `‖ω‖ = 1`,
    `ω ≠ 1`.  Since `c(ω)` is real there (`cayleyInv_im_eq_zero`), `i · t · c(ω)` is purely imaginary, so
    `‖exp(i t c(ω))‖ = exp((i t c(ω)).re) = exp(0) = 1` (`Complex.norm_exp`).  This is the unitarity of the Stone
    exponential `U_t = cfc(e_t) V` and the boundedness that makes `e_t ∈ L²(μ_x)`. -/
theorem cayleyExp_abs {t : ℝ} {ω : ℂ} (h1 : ‖ω‖ = 1) (hne : ω ≠ 1) : ‖cayleyExp t ω‖ = 1 := by
  have hc : (cayleyInv ω).im = 0 := cayleyInv_im_eq_zero h1 hne
  have him : (Complex.I * ((t : ℂ) * cayleyInv ω)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, hc]
  rw [cayleyExp, Complex.norm_exp, him, Real.exp_zero]

/-- **The Stone-exponential symbol at `t = 0` is the constant `1`:** `e_0(ω) = 1` (`exp 0 = 1`).  The symbol-level
    seed of `U_0 = cfc(e_0) V = cfc 1 V = 1` — the identity element of the one-parameter unitary group. -/
theorem cayleyExp_zero (ω : ℂ) : cayleyExp 0 ω = 1 := by
  simp [cayleyExp]

/-- **The one-parameter group law of the Stone-exponential symbol:** `e_s(ω) · e_t(ω) = e_{s+t}(ω)`.  Immediate
    from `exp` (`Complex.exp_add`): `exp(i s c)·exp(i t c) = exp(i(s+t)c)`.  This is the symbol-level seed of the
    **one-parameter unitary group law** `U_s U_t = U_{s+t}` (`cfc(e_s) V · cfc(e_t) V = cfc(e_s·e_t) V =
    cfc(e_{s+t}) V`, by multiplicativity of the functional calculus), one of the two Stone-group axioms (with
    `cayleyExp_zero`); strong continuity `t ↦ U_t x` is the third. -/
theorem cayleyExp_add (s t : ℝ) (ω : ℂ) : cayleyExp s ω * cayleyExp t ω = cayleyExp (s + t) ω := by
  rw [cayleyExp, cayleyExp, cayleyExp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The continuous bump cutoff** `η_N(ω) = 1 − ψ_N(ω)`, complementary to the rational cutoff `cayleyCutoff`.
    As `N → ∞` it rises to the indicator of `ℂ \ {1}`: `η_N(1) = 0` for all `N` (so it vanishes at the Cayley
    exceptional point, taming the symbol's discontinuity there), while `η_N(ω) → 1` for `ω ≠ 1`.  Each `η_N` is
    continuous and valued in `[0, 1]`.  The cutoff symbol `e_t · η_N` is then **continuous on `σ(V)`** (`η_N → 0`
    kills `e_t`'s discontinuity at `1`) and converges to `e_t` in `L²(μ_x)` (since `μ_x({1}) = 0`), so its
    cfc-vectors converge to define the Stone unitary `U_t x = lim cfc(e_t · η_N) V x`. -/
noncomputable def cayleyBump (N : ℕ) (ω : ℂ) : ℝ := 1 - cayleyCutoff N ω

/-- Each bump `η_N` is continuous on `ℂ` (`1 −` a continuous function). -/
theorem cayleyBump_continuous (N : ℕ) : Continuous (cayleyBump N) :=
  continuous_const.sub (cayleyCutoff_continuous N)

/-- The bump is nonnegative (`ψ_N ≤ 1`). -/
theorem cayleyBump_nonneg (N : ℕ) (ω : ℂ) : 0 ≤ cayleyBump N ω :=
  sub_nonneg.mpr (cayleyCutoff_le_one N ω)

/-- The bump is bounded by `1` (`0 < ψ_N`); so `η_N ∈ [0, 1]` is an integrable DCT dominator. -/
theorem cayleyBump_le_one (N : ℕ) (ω : ℂ) : cayleyBump N ω ≤ 1 := by
  have := (cayleyCutoff_pos N ω).le
  simp only [cayleyBump]; linarith

/-- **The pointwise limit of the bump sequence is the indicator of `ℂ \ {1}`:**
    `η_N(ω) → (if ω = 1 then 0 else 1)`.  Complementary to `cayleyCutoff_tendsto_indicator` (`ψ_N → 1_{ω=1}`):
    `η_N = 1 − ψ_N → 1 − 1_{ω=1}`.  This is the convergence DCT consumes to show `e_t · η_N → e_t` in `L²(μ_x)`. -/
theorem cayleyBump_tendsto_indicator (ω : ℂ) :
    Filter.Tendsto (fun N => cayleyBump N ω) Filter.atTop
      (nhds (if ω = 1 then (0 : ℝ) else 1)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (cayleyCutoff_tendsto_indicator ω)
  have heq : (1 : ℝ) - (if ω = 1 then (1 : ℝ) else 0) = (if ω = 1 then (0 : ℝ) else 1) := by
    by_cases hω : ω = 1 <;> simp [hω]
  rw [heq] at h
  exact h

/-- **The Stone-exponential symbol has modulus `1` on the *whole* unit circle**, including the excluded point `1`:
    `‖e_t(ω)‖ = 1` for `‖ω‖ = 1`.  At `ω ≠ 1` this is `cayleyExp_abs`; at `ω = 1` the junk value
    `cayleyInv 1 = i·2/0 = 0` gives `e_t(1) = exp 0 = 1`, of modulus `1`.  So `‖e_t‖ = 1` on all of `σ(V) ⊆ S¹` —
    the uniform bound that makes the cutoff symbol `e_t · η_N` an `L²(μ_x)` approximant of `e_t`. -/
theorem cayleyExp_abs_circle {t : ℝ} {ω : ℂ} (h1 : ‖ω‖ = 1) : ‖cayleyExp t ω‖ = 1 := by
  by_cases hne : ω = 1
  · subst hne; simp [cayleyExp, cayleyInv]
  · exact cayleyExp_abs h1 hne

/-- **The pointwise `L²`-defect of the cutoff symbol on the circle:** `‖e_t(ω)·η_N(ω) − e_t(ω)‖ = ψ_N(ω)` for
    `‖ω‖ = 1`.  Since `e_t·η_N − e_t = e_t·(η_N − 1)` and `‖e_t‖ = 1` on the circle (`cayleyExp_abs_circle`),
    `‖e_t·(η_N − 1)‖ = |η_N − 1| = |−ψ_N| = ψ_N` (`η_N = 1 − ψ_N`, `ψ_N ≥ 0`).  Hence `‖e_t·η_N − e_t‖² = ψ_N²`,
    which `→ 0` in `L²(μ_x)` (since `∫ ψ_N² dμ_x ≤ ∫ ψ_N dμ_x → μ_x({1}) = 0`): the cutoff symbol converges to the
    symbol in `L²(μ_x)`, the input to the strong-limit definition of `U_t`. -/
theorem cayleyExpBump_sub_norm (t : ℝ) (N : ℕ) {ω : ℂ} (h1 : ‖ω‖ = 1) :
    ‖cayleyExp t ω * (cayleyBump N ω : ℂ) - cayleyExp t ω‖ = cayleyCutoff N ω := by
  have habs : ‖cayleyExp t ω‖ = 1 := cayleyExp_abs_circle h1
  have hfac : cayleyExp t ω * (cayleyBump N ω : ℂ) - cayleyExp t ω
      = cayleyExp t ω * (((cayleyBump N ω - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hfac, norm_mul, habs, one_mul, Complex.norm_real, cayleyBump,
    show (1 - cayleyCutoff N ω - 1 : ℝ) = -cayleyCutoff N ω by ring,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (cayleyCutoff_pos N ω).le]

/-- **`∫ ψ_N² dμ_x → 0`** — the squeeze closing the atom-killing into an `L²` statement.  Since `0 ≤ ψ_N ≤ 1`,
    `ψ_N² ≤ ψ_N`, so `0 ≤ ∫ ψ_N² ≤ ∫ ψ_N` (`integral_mono_of_nonneg`); and `∫ ψ_N dμ_x → μ_x({1}) = 0` (DCT-1
    `cayleyCutoff_integral_tendsto_atom` + the atom-killing `cayleyScalarMeasure_atom_eq_zero`).  By the squeeze
    `∫ ψ_N² dμ_x → 0`.  This is the `L²(μ_x)`-defect of the cutoff symbol (`cayleyExpBump_sub_norm`: `‖g−e_t‖² = ψ_N²`),
    so it gives the `L²` convergence `g_{t,N} → e_t`. -/
theorem cayleyCutoff_sq_integral_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  have hint : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) => cayleyCutoff N (ω : ℂ))
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact ((cayleyCutoff_continuous N).comp continuous_subtype_val).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (cayleyCutoff_pos N _).le]; exact cayleyCutoff_le_one N _
  have hatom := cayleyCutoff_integral_tendsto_atom U hgrp hU0 hUinner hUbd hSC x
  rw [cayleyScalarMeasure_atom_eq_zero U hgrp hU0 hUinner hUbd hSC x, ENNReal.toReal_zero] at hatom
  refine squeeze_zero (fun N => integral_nonneg (fun ω => sq_nonneg _)) (fun N => ?_) hatom
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  · exact hint N
  · filter_upwards with ω
    nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]

/-- **★★ The cutoff symbol converges to the symbol in `L²(μ_x)`:**
    `∫ ‖e_t·η_N − e_t‖² dμ_x → 0`.  By `cayleyExpBump_sub_norm` the integrand is `ψ_N(ω.1)²` on `σ(V) ⊆ S¹`
    (`integral_congr_ae`), so this is `cayleyCutoff_sq_integral_tendsto_zero` (`∫ ψ_N² → 0`).  Combined with the
    `L²`-distance Parseval, it gives the `L²(μ_x)`-Cauchy condition for `cfc(e_t·η_N) V x`, whose strong limit is
    the Stone unitary `U_t x = lim cfc(e_t·η_N) V x`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_L2_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  have heq : ∀ N, (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      = ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    have hcirc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    show ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
      = (cayleyCutoff N (ω : ℂ)) ^ 2
    rw [cayleyExpBump_sub_norm t N hcirc]
  simp only [heq]
  exact cayleyCutoff_sq_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC x

/-- **The cutoff Stone-exponential symbol** `g_{t,N}(ω) = e_t(ω) · η_N(ω)` — the continuous approximant of the symbol
    `e_t`, with the bump `η_N` taming `e_t`'s discontinuity at the excluded point `1` (`η_N(1) = 0`).  Its cfc
    `cfc(g_{t,N}) V x` is a continuous-function functional-calculus vector; as `N → ∞` these converge (the L²→strong
    bridge, since `g_{t,N} → e_t` in `L²(μ_x)`) to define the Stone unitary `U_t x = lim cfc(g_{t,N}) V x`. -/
noncomputable def cayleyExpBump (t : ℝ) (N : ℕ) (ω : ℂ) : ℂ := cayleyExp t ω * (cayleyBump N ω : ℂ)

/-- The cutoff symbol has norm `η_N` on the unit circle: `‖g_{t,N}(ω)‖ = η_N(ω)` for `‖ω‖ = 1` (`‖e_t‖ = 1`,
    `η_N ≥ 0`).  This is the squeeze that gives `g_{t,N}` continuity at the excluded point `1` (`‖g‖ = η_N → 0`). -/
theorem cayleyExpBump_norm (t : ℝ) (N : ℕ) {ω : ℂ} (h1 : ‖ω‖ = 1) :
    ‖cayleyExpBump t N ω‖ = cayleyBump N ω := by
  rw [cayleyExpBump, norm_mul, cayleyExp_abs_circle h1, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (cayleyBump_nonneg N ω)]

/-- **★★ The cutoff symbol is continuous on `σ(V)`:** `ContinuousOn (g_{t,N}) (spectrum ℂ V)`.  Off the excluded
    point `1` it is a product of continuous functions (`cayleyExp_continuousOn`, `cayleyBump_continuous`); at `1`
    (if `1 ∈ σ(V)`) the value is `g_{t,N}(1) = e_t(1)·0 = 0`, and `‖g_{t,N}(ω)‖ = η_N(ω) → η_N(1) = 0`
    (`cayleyExpBump_norm` on `σ(V) ⊆ S¹` + `η_N` continuous) — the squeeze giving `ContinuousWithinAt` at `1`.
    So `cfc(g_{t,N}) V` is well-defined (the cfc needs `ContinuousOn (σ(V))`), the operator whose strong limit is
    `U_t`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_continuousOn [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (N : ℕ) :
    ContinuousOn (cayleyExpBump t N)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
  intro ω hω
  by_cases hne : ω = 1
  · -- at the excluded point: the norm squeeze ‖g‖ = η_N → 0
    subst hne
    have hg1 : cayleyExpBump t N 1 = 0 := by simp [cayleyExpBump, cayleyBump, cayleyCutoff]
    rw [ContinuousWithinAt, hg1, tendsto_zero_iff_norm_tendsto_zero]
    have heqon : Set.EqOn (fun ω => ‖cayleyExpBump t N ω‖) (cayleyBump N)
        (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
      intro ω hωs
      have hc : ‖ω‖ = 1 := by
        have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC hωs
        rwa [mem_sphere_zero_iff_norm] at hmem
      exact cayleyExpBump_norm t N hc
    refine Filter.Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn heqon.symm) ?_
    have hb1 : cayleyBump N 1 = 0 := by simp [cayleyBump, cayleyCutoff]
    rw [← hb1]
    exact (cayleyBump_continuous N).continuousWithinAt
  · -- off the excluded point: product of continuous-at functions
    have he : ContinuousAt (cayleyExp t) ω :=
      (cayleyExp_continuousOn t).continuousAt (isOpen_ne.mem_nhds hne)
    have hb : ContinuousAt (fun z => (cayleyBump N z : ℂ)) ω :=
      (Complex.continuous_ofReal.comp (cayleyBump_continuous N)).continuousAt
    exact (he.mul hb).continuousWithinAt

/-- **★★★ The cutoff Stone-exponential cfc vectors form a Cauchy sequence:** `cfc(g_{t,N}) V x` is a `CauchySeq`
    in `H` (hence converges, `H` complete) — whose **strong limit is the Stone unitary `U_t x`**.  The cutoff
    symbol `g_{t,N} = e_t·η_N` is `ContinuousOn σ(V)` (`cayleyExpBump_continuousOn`, so the cfc applies) and converges
    to `e_t` in `L²(μ_x)` (`cayleyExpBump_L2_tendsto_zero`); an `L²(μ_x)`-convergent sequence is `L²`-Cauchy (the
    quadratic triangle `‖g_m − g_n‖² ≤ 2‖g_m − e_t‖² + 2‖g_n − e_t‖²` with `c = e_t`, integrated via
    `integral_mono_of_nonneg`), so `cayley_cfc_cauchySeq_of_integral` (the existence half of the L²→strong bridge)
    yields the `CauchySeq`.  This is the construction of the continuum Stone exponential `U_t = exp(it A)` as a strong
    limit of continuous functional calculi, with NO projection-valued measure.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_cfc_cauchySeq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    CauchySeq (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- each ‖g_N − e_t‖² is integrable (a.e. equal to ψ_N², which is continuous and bounded)
  have hint : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2)
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    have hψint : Integrable
        (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
          (cayleyCutoff N (ω : ℂ)) ^ 2) (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (((cayleyCutoff_continuous N).comp continuous_subtype_val).pow 2).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]
    refine hψint.congr ?_
    filter_upwards with ω
    have hc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    rw [cayleyExpBump_sub_norm t N hc]
  -- the L² norms tend to 0
  have hL2 := cayleyExpBump_L2_tendsto_zero U hgrp hU0 hUinner hUbd hSC t x
  rw [Metric.tendsto_atTop] at hL2
  -- assemble the L²-Cauchy condition and invoke the existence half
  refine cayley_cfc_cauchySeq_of_integral U hgrp hU0 hUinner hUbd hSC
    (fun N z => cayleyExpBump t N z) (fun N => cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N) x ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hL2 (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have key : ∀ k, N ≤ k → ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump k (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε / 4 := by
    intro k hk
    have hd := hN k hk
    have hnn : 0 ≤ ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump k (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_nonneg (fun ω => sq_nonneg _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hd
  show ∫ ω, ‖cayleyExpBump t m (ω : ℂ) - cayleyExpBump t n (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε
  calc ∫ ω, ‖cayleyExpBump t m (ω : ℂ) - cayleyExpBump t n (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      ≤ ∫ ω, (2 * ‖cayleyExp t (ω : ℂ) * (cayleyBump m (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          + 2 * ‖cayleyExp t (ω : ℂ) * (cayleyBump n (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2)
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
        · exact ((hint m).const_mul 2).add ((hint n).const_mul 2)
        refine Filter.Eventually.of_forall (fun ω => ?_)
        simp only [cayleyExpBump]
        set c := cayleyExp t (ω : ℂ) with hcdef
        set a := c * (cayleyBump m (ω : ℂ) : ℂ) with ha
        set b := c * (cayleyBump n (ω : ℂ) : ℂ) with hb
        have h1 : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
          have he : a - b = (a - c) - (b - c) := by ring
          rw [he]; exact norm_sub_le _ _
        nlinarith [h1, norm_nonneg (a - b), norm_nonneg (a - c), norm_nonneg (b - c),
          sq_nonneg (‖a - c‖ - ‖b - c‖)]
    _ = 2 * (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump m (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        + 2 * (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump n (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) := by
        rw [integral_add ((hint m).const_mul 2) ((hint n).const_mul 2), integral_const_mul, integral_const_mul]
    _ < ε := by have hbm := key m hm; have hbn := key n hn; linarith

/-- **★★★ The continuum Stone exponential `U_t x = exp(it A) x`** — defined as the strong limit of the cutoff
    functional-calculus vectors `U_t x := lim_N cfc(g_{t,N}) V x` (which exists by `cayleyExpBump_cfc_cauchySeq` and
    completeness of `H`).  This is `cfc(e_t) V x` for the (bounded Borel, `μ_x`-a.e. continuous) Stone-exponential
    symbol `e_t(ω) = exp(it · invCayley(ω))`, the genuine continuum unitary group of the self-adjoint generator
    `A = i(1 + V)(1 − V)⁻¹` — built with NO projection-valued measure.  Axiom-free; free scalar; no UV datum. -/
noncomputable def cayleyStoneU [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (t : ℝ) (x : H) : H :=
  (cauchySeq_tendsto_of_complete (cayleyExpBump_cfc_cauchySeq U hgrp hU0 hUinner hUbd hSC t x)).choose

/-- **The defining property of `U_t`:** `cfc(g_{t,N}) V x → U_t x` strongly (`U_t` is the strong limit). -/
theorem cayleyStoneU_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    Filter.Tendsto (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      Filter.atTop (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)) :=
  (cauchySeq_tendsto_of_complete (cayleyExpBump_cfc_cauchySeq U hgrp hU0 hUinner hUbd hSC t x)).choose_spec

/-- **`U_t` is additive:** `U_t(x + y) = U_t x + U_t y`.  Each `cfc(g_{t,N}) V` is a (linear) bounded operator, so
    `cfc(g_{t,N}) V (x+y) = cfc(g_{t,N}) V x + cfc(g_{t,N}) V y`; pass to the strong limit (`Tendsto.add` + uniqueness).
    With `cayleyStoneU_smul`, `U_t` is a ℂ-linear operator (toward `U_t ∈ unitary(H)`). -/
theorem cayleyStoneU_add [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x y : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t (x + y)
      = cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x + cayleyStoneU U hgrp hU0 hUinner hUbd hSC t y := by
  have hxy := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t (x + y)
  have hsum := (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).add
    (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t y)
  have heq : (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (x + y))
      = (fun N => cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
          + cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) := by
    funext N; rw [map_add]
  rw [heq] at hxy
  exact tendsto_nhds_unique hxy hsum

/-- **`U_t` is ℂ-homogeneous:** `U_t(c • x) = c • U_t x`.  As `cayleyStoneU_add`, from the linearity of each
    `cfc(g_{t,N}) V` (`map_smul`) and `Tendsto.const_smul` + uniqueness. -/
theorem cayleyStoneU_smul [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (t : ℝ) (c : ℂ) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t (c • x)
      = c • cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x := by
  have hcx := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t (c • x)
  have hsm := (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).const_smul c
  have heq : (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (c • x))
      = (fun N => c • cfc (cayleyExpBump t N)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
    funext N; rw [map_smul]
  rw [heq] at hcx
  exact tendsto_nhds_unique hcx hsm

end SelfAdjoint

end QIQTH.Spectral
