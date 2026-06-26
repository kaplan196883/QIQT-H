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

end QIQTH.Spectral
