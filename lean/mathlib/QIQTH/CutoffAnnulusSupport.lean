/-
  CutoffAnnulusSupport — the annulus-support of the smooth radial cutoff.

  The smooth radial cutoff `radialCutoff a b` (from `QIQTH.SmoothCutoff`) is LOCALLY CONSTANT off the
  annulus `[a², b²]`: it is `≡ 1` on the open near region `{rncRadialSq < a²}` and `≡ 0` on the open far
  region `{rncRadialSq > b²}`.  Consequently ALL of its partial derivatives vanish there.

  This file proves, for `0 < a < b`:
    * `radialCutoff_eventuallyEq_one/zero` — the cutoff equals `1` (resp. `0`) on a neighbourhood of any
      point strictly inside the near (resp. strictly outside the far) region;
    * `pd_radialCutoff_eq_zero_of_near/far` — the first partials `∂ᵢ χ` vanish there;
    * `pd_pd_radialCutoff_eq_zero_of_near/far` — the second partials `∂ⱼ∂ᵢ χ` (feeding `Δ_g χ`) vanish
      there — because `∂ᵢ χ` is itself identically `0` on the whole open region, so its `pd` is `0`.

  Purpose: this CONFINES the cutoff-derivative terms of the C4c cutoff-parametrix residual to the
  annulus `[a², b²]`, where the exponential-smallness bound of the base Gaussian kernel applies — a step
  toward the far-field residual bound (`residual_global_baseKernelW_of_gaussianCofactor`) and the
  unconditional `a₁ = R/6` heat-kernel coefficient.  It is NOT itself `a₁ = R/6`.
-/

import Mathlib
import QIQTH.Curvature
import QIQTH.RadialDistance
import QIQTH.SmoothCutoff

set_option maxHeartbeats 1200000

open QIQTH.Curvature QIQTH.RadialDistance
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ### `pd` germ-congruence (self-contained copy)

`pd f i x` reads `f` only through the germ of `t ↦ f (update x i t)` at `t = x i`, so two fields
agreeing on a neighbourhood of `x` have equal partial derivatives at `x`. -/

/-- **Local `pd` congruence.** If `f =ᶠ[𝓝 x] h` then `∂ᵢ f (x) = ∂ᵢ h (x)`: the coordinate-update map
`t ↦ update x i t` is continuous with value `x` at `t = x i`, so it pulls the germ of `f` at `x` back
to the germ of `t ↦ f (update x i t)` at `x i`, where the `deriv` reads it. -/
theorem pd_congr_eventuallyEq {f h : Point n → ℝ} (i : Fin n) (x : Point n)
    (hfh : f =ᶠ[nhds x] h) : pd f i x = pd h i x := by
  simp only [pd]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcont : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
    have h1 : ContinuousAt (Function.update x i) (x i) :=
      (hasDerivAt_update x i (x i)).continuousAt
    have h2 : (Function.update x i) (x i) = x := Function.update_eq_self i x
    rw [ContinuousAt, h2] at h1
    exact h1
  exact hcont.eventually hfh

/-! ### Open near / far regions -/

/-- The strict near region `{rncRadialSq < a²}` is open (continuity of the polynomial `rncRadialSq`). -/
theorem isOpen_rncRadialSq_lt (c : ℝ) :
    IsOpen {w : Point n | rncRadialSq w < c} :=
  isOpen_lt rncRadialSq_contDiff.continuous continuous_const

/-- The strict far region `{rncRadialSq > c}` is open. -/
theorem isOpen_rncRadialSq_gt (c : ℝ) :
    IsOpen {w : Point n | c < rncRadialSq w} :=
  isOpen_lt continuous_const rncRadialSq_contDiff.continuous

/-! ### The cutoff is locally constant off the annulus -/

/-- On a neighbourhood of any point strictly inside the near ball (`rncRadialSq v < a²`) the cutoff is
identically `1`: the open set `{rncRadialSq < a²}` is a neighbourhood of `v` on which
`radialCutoff a b ≡ 1` (`radialCutoff_eq_one`, since `< a² ⟹ ≤ a²`). -/
theorem radialCutoff_eventuallyEq_one {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : rncRadialSq v < a ^ 2) :
    radialCutoff a b =ᶠ[nhds v] (fun _ : Point n => (1 : ℝ)) := by
  have hmem : {w : Point n | rncRadialSq w < a ^ 2} ∈ nhds v :=
    (isOpen_rncRadialSq_lt (a ^ 2)).mem_nhds hv
  exact Filter.eventuallyEq_of_mem hmem
    (fun w hw => radialCutoff_eq_one ha hab (le_of_lt hw))

/-- On a neighbourhood of any point strictly outside the far ball (`b² < rncRadialSq v`) the cutoff is
identically `0`: the open set `{rncRadialSq > b²}` is a neighbourhood of `v` on which
`radialCutoff a b ≡ 0` (`radialCutoff_eq_zero`, since `> b² ⟹ ≥ b²`). -/
theorem radialCutoff_eventuallyEq_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : b ^ 2 < rncRadialSq v) :
    radialCutoff a b =ᶠ[nhds v] (fun _ : Point n => (0 : ℝ)) := by
  have hmem : {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds v :=
    (isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hv
  exact Filter.eventuallyEq_of_mem hmem
    (fun w hw => radialCutoff_eq_zero ha hab (le_of_lt hw))

/-! ### First-order partials vanish off the annulus -/

/-- Near the center (`rncRadialSq v < a²`) every first partial of the cutoff vanishes: `radialCutoff` is
identically `1` on a neighbourhood, so `∂ᵢ (radialCutoff a b) v = ∂ᵢ (const 1) v = 0`. -/
theorem pd_radialCutoff_eq_zero_of_near {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : rncRadialSq v < a ^ 2) (i : Fin n) :
    pd (radialCutoff a b) i v = 0 := by
  rw [pd_congr_eventuallyEq i v (radialCutoff_eventuallyEq_one ha hab hv)]
  exact pd_const 1 i v

/-- Far from the center (`b² < rncRadialSq v`) every first partial of the cutoff vanishes: `radialCutoff`
is identically `0` on a neighbourhood, so `∂ᵢ (radialCutoff a b) v = ∂ᵢ (const 0) v = 0`. -/
theorem pd_radialCutoff_eq_zero_of_far {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : b ^ 2 < rncRadialSq v) (i : Fin n) :
    pd (radialCutoff a b) i v = 0 := by
  rw [pd_congr_eventuallyEq i v (radialCutoff_eventuallyEq_zero ha hab hv)]
  exact pd_const 0 i v

/-! ### Second-order partials vanish off the annulus

`∂ᵢ (radialCutoff a b)` is itself identically `0` on the WHOLE open near (resp. far) region — apply the
first-order vanishing at every point of the open set — so it is `=ᶠ[𝓝 v] 0`, and `pd`-congruence gives
`∂ⱼ∂ᵢ (radialCutoff a b) v = 0`.  This kills the `Δ_g χ`-type second-derivative cutoff terms. -/

/-- The first partial `∂ᵢ (radialCutoff a b)` vanishes on a neighbourhood of any near-center point. -/
theorem pd_radialCutoff_eventuallyEq_zero_of_near {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : rncRadialSq v < a ^ 2) (i : Fin n) :
    (fun y => pd (radialCutoff a b) i y) =ᶠ[nhds v] (fun _ : Point n => (0 : ℝ)) := by
  have hmem : {w : Point n | rncRadialSq w < a ^ 2} ∈ nhds v :=
    (isOpen_rncRadialSq_lt (a ^ 2)).mem_nhds hv
  exact Filter.eventuallyEq_of_mem hmem
    (fun w hw => pd_radialCutoff_eq_zero_of_near ha hab hw i)

/-- The first partial `∂ᵢ (radialCutoff a b)` vanishes on a neighbourhood of any far point. -/
theorem pd_radialCutoff_eventuallyEq_zero_of_far {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : b ^ 2 < rncRadialSq v) (i : Fin n) :
    (fun y => pd (radialCutoff a b) i y) =ᶠ[nhds v] (fun _ : Point n => (0 : ℝ)) := by
  have hmem : {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds v :=
    (isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hv
  exact Filter.eventuallyEq_of_mem hmem
    (fun w hw => pd_radialCutoff_eq_zero_of_far ha hab hw i)

/-- Near the center (`rncRadialSq v < a²`) every second partial of the cutoff vanishes:
`∂ᵢ (radialCutoff a b)` is `≡ 0` on a neighbourhood, so `∂ⱼ∂ᵢ (radialCutoff a b) v = 0`. -/
theorem pd_pd_radialCutoff_eq_zero_of_near {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : rncRadialSq v < a ^ 2) (i j : Fin n) :
    pd (fun y => pd (radialCutoff a b) i y) j v = 0 := by
  rw [pd_congr_eventuallyEq j v (pd_radialCutoff_eventuallyEq_zero_of_near ha hab hv i)]
  exact pd_const 0 j v

/-- Far from the center (`b² < rncRadialSq v`) every second partial of the cutoff vanishes:
`∂ᵢ (radialCutoff a b)` is `≡ 0` on a neighbourhood, so `∂ⱼ∂ᵢ (radialCutoff a b) v = 0`. -/
theorem pd_pd_radialCutoff_eq_zero_of_far {a b : ℝ} (ha : 0 < a) (hab : a < b) {v : Point n}
    (hv : b ^ 2 < rncRadialSq v) (i j : Fin n) :
    pd (fun y => pd (radialCutoff a b) i y) j v = 0 := by
  rw [pd_congr_eventuallyEq j v (pd_radialCutoff_eventuallyEq_zero_of_far ha hab hv i)]
  exact pd_const 0 j v

end QIQTH.HeatResidualBound
