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

end QIQTH.Spectral
