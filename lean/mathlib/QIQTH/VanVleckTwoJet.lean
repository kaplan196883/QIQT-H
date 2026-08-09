import Mathlib
import QIQTH.RNCExpansion
import QIQTH.Curvature

/-!
# The van-Vleck AMPLITUDE 2-jet — the `J^{-1/2}` power flip (`D²u₀(0) = +(1/6) Ric`)

This file lands the **algebraic reduction** isolating the one irreducible geometric input of the
DeWitt `a₁ = R/6` transport coefficient.  The already-banked directional van-Vleck result
(`QIQTH.VanVleckRadial.sqrtdet_directional_hessian_ricci`, and the diagonal
`QIQTH.RNCExpansion.sqrtdet_pd_pd`) computes the 2-jet of the **volume density** `J = √det g`:
`D²(√det g)(0) = −(1/3) Ric`.  The van-Vleck **amplitude** is `u₀ = J^{−1/2}`, and the
`J^{−1/2}` power **flips the sign** to `D²u₀(0) = +(1/6) Ric`, `tr D²u₀(0) = (1/6) Scal`.

## The SIGN chain (the trap)

* `√det g` alone: `D²(√det g)(0) = −(1/3) Ric`  (the `√`, banked).
* the power `x ↦ x^{−1/2}` has derivative `−½` at `x = 1`, and since the inner gradient
  `D(√det g)(0) = 0` vanishes, the composition Hessian is `f'(1)·D²(√det g)(0) = (−½)·(−⅓ Ric)`.
* arithmetic: `−(1/2) · (−(1/3)) = +1/6`.  Hence `D²u₀(0) = +(1/6) Ric`.

The `+(1/6)` (NOT `−(1/3)`, NOT `+(1/12)` as a coefficient) is the load-bearing output.

## What lands (all GENERIC in a smooth positive scalar field `J`, the abstract volume density)

* `pd_comp_invSqrt` — the first-order chain rule for `x ↦ (√x)⁻¹ = x^{−1/2}` at a positive point.
* `invSqrt_pd_pd` — **the power flip**: for `J` smooth with `J(0)=1`, `∂J(0)=0` (critical point),
  `∂_c∂_d (J^{−1/2})(0) = −(1/2) ∂_c∂_d J(0)`.  The `−½` is the derivative of `x^{−1/2}` at `1`; the
  cross term drops because `∂J(0)=0`.  This is the sign-critical `J^{−1/2}` algebra.
* `invSqrt_directional_hessian_ricci` — carrying the single geometric input
  `hJhess : D²J(0) = −(1/3) Ric` (the banked `√det g` 2-jet), the amplitude directional Hessian is
  `∑_{cd} v^c v^d ∂_c∂_d u₀(0) = +(1/6) Ric(v,v)`.
* `invSqrt_trace_hessian_scal` — the trace: `∑_i ∂_i² u₀(0) = (1/6) ∑_i Ric_{ii} = (1/6) Scal`.

## What this is NOT

⚠ This is the **algebraic reduction only**.  It reduces the amplitude 2-jet to the SINGLE carried
geometric hypothesis `hJhess : D²(√det g)(0) = −(1/3) Ric` (equivalently the RNC metric 2-jet
`tr ∂∂g(0) = −⅔ Ric`, the honest irreducible geometric theorem discharged elsewhere from the normal
gauge).  It does **not** derive that metric 2-jet, and it is **not** `a₁ = R/6` for the true heat
kernel.  `J` is kept abstract (the volume density need not be globally smooth as `√det g`; the
reduction carries its 2-jet).
-/

set_option maxHeartbeats 1000000

namespace QIQTH.VanVleckTwoJet

open QIQTH.Curvature
open QIQTH.RNCExpansion
open scoped BigOperators

variable {n : ℕ}

/-- **First-order chain rule for `x ↦ (√x)⁻¹ = x^{−1/2}` at a positive point.**
    `∂_i (√J)⁻¹ = −(1/2)·(√J(x))⁻³ · ∂_i J`.  (`(√x)⁻¹` has derivative `−½ x^{−3/2} = −½ (√x)⁻³`.) -/
theorem pd_comp_invSqrt (J : Point n → ℝ) (i : Fin n) (x : Point n)
    (hJ : PdiffAt J i x) (hpos : 0 < J x) :
    pd (fun y => (Real.sqrt (J y))⁻¹) i x
      = (-(1 / 2) * (Real.sqrt (J x))⁻¹ ^ 3) * pd J i x := by
  simp only [pd]
  have hval : J (Function.update x i (x i)) = J x := by rw [Function.update_eq_self]
  have hne : J x ≠ 0 := ne_of_gt hpos
  have hsne : Real.sqrt (J x) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hinv : HasDerivAt (fun z => (Real.sqrt z)⁻¹)
      (-(1 / 2) * (Real.sqrt (J x))⁻¹ ^ 3) (J (Function.update x i (x i))) := by
    rw [hval]
    have h := (Real.hasDerivAt_sqrt hne).inv hsne
    have heq : -(1 / (2 * Real.sqrt (J x))) / Real.sqrt (J x) ^ 2
        = -(1 / 2) * (Real.sqrt (J x))⁻¹ ^ 3 := by
      field_simp
    rwa [heq] at h
  have hcomp := hinv.comp (x i) hJ.hasDerivAt
  exact hcomp.deriv

/-- **The `J^{−1/2}` power flip (critical-point 2-jet).**  For `J` smooth with `J(x)=1` and vanishing
    gradient `∂J(x)=0`, the second partial of the van-Vleck amplitude `u₀ = (√J)⁻¹ = J^{−1/2}` is
    `∂_c∂_d (J^{−1/2})(x) = −(1/2) ∂_c∂_d J(x)`.  The multiplier is `f'(1) = −½` for `f(x)=x^{−1/2}`;
    the cross `(∂J)²` term drops because `∂J(x)=0`.  This is the SIGN-critical step: it turns the
    `√det g` datum `−(1/3) Ric` into the amplitude `+(1/6) Ric`. -/
theorem invSqrt_pd_pd (J : Point n → ℝ) (c d : Fin n) (x : Point n)
    (hJ : ContDiff ℝ ⊤ J) (hJval : J x = 1) (hcrit : ∀ e, pd J e x = 0) :
    pd (fun y => pd (fun w => (Real.sqrt (J w))⁻¹) d y) c x
      = -(1 / 2) * pd (fun y => pd J d y) c x := by
  have hpos0 : 0 < J x := by rw [hJval]; norm_num
  have hne : J x ≠ 0 := ne_of_gt hpos0
  have hsne : Real.sqrt (J x) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos0
  have hcont : Continuous J := hJ.continuous
  have hposnhds : ∀ᶠ y in nhds x, 0 < J y :=
    (isOpen_lt continuous_const hcont).mem_nhds hpos0
  -- the first-order chain rule holds on a neighbourhood of `x` (where `J > 0`)
  have hchain : (fun y => pd (fun w => (Real.sqrt (J w))⁻¹) d y)
      =ᶠ[nhds x] (fun y => (-(1 / 2) * (Real.sqrt (J y))⁻¹ ^ 3) * pd J d y) := by
    filter_upwards [hposnhds] with y hy
    exact pd_comp_invSqrt J d y (PdiffAt_of_contDiff J hJ d y) hy
  rw [pd_congr c x hchain]
  -- differentiability of the two factors at `x`
  have hB : PdiffAt (fun y => pd J d y) c x := PdiffAt_pd J hJ d c x
  have hA : PdiffAt (fun y => -(1 / 2) * (Real.sqrt (J y))⁻¹ ^ 3) c x := by
    show DifferentiableAt ℝ
      (fun t => -(1 / 2) * (Real.sqrt (J (Function.update x c t)))⁻¹ ^ 3) (x c)
    have hφ : DifferentiableAt ℝ (fun t => J (Function.update x c t)) (x c) :=
      PdiffAt_of_contDiff J hJ c x
    have hval2 : J (Function.update x c (x c)) = J x := by rw [Function.update_eq_self]
    have hsqrtd : DifferentiableAt ℝ Real.sqrt (J (Function.update x c (x c))) := by
      rw [hval2]; exact (Real.hasDerivAt_sqrt hne).differentiableAt
    have hsφ : DifferentiableAt ℝ (fun t => Real.sqrt (J (Function.update x c t))) (x c) :=
      hsqrtd.comp (x c) hφ
    have hsne2 : Real.sqrt (J (Function.update x c (x c))) ≠ 0 := by rw [hval2]; exact hsne
    exact ((hsφ.inv hsne2).pow 3).const_mul (-(1 / 2))
  rw [pd_mul (fun y => -(1 / 2) * (Real.sqrt (J y))⁻¹ ^ 3) (fun y => pd J d y) c x hA hB]
  have hAx : (-(1 / 2) * (Real.sqrt (J x))⁻¹ ^ 3) = -(1 / 2 : ℝ) := by
    rw [hJval, Real.sqrt_one]; norm_num
  rw [hcrit d, mul_zero, zero_add, hAx]

/-! ### The Ricci / scalar-curvature corollaries — the single carried geometric input -/

/-- **The amplitude directional 2-jet = the Ricci quadratic form (the `+1/6` flip).**
    Carrying the SINGLE geometric input `hJhess : D²(√det g)(0) = −(1/3) Ric` (the banked volume-density
    2-jet), the van-Vleck amplitude `u₀ = J^{−1/2}` has directional Hessian
    `∑_{cd} v^c v^d ∂_c∂_d u₀(0) = +(1/6) Ric(v,v)`.  The `−(1/2)` power multiplier turns the volume
    density's `−(1/3) Ric` into `+(1/6) Ric`.  `hJhess` is the one irreducible geometric hypothesis;
    everything downstream of it is the algebra proved here. -/
theorem invSqrt_directional_hessian_ricci (J : Point n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hJ : ContDiff ℝ ⊤ J) (hJval : J 0 = 1) (hcrit : ∀ e, pd J e 0 = 0)
    (hJhess : ∀ c d, pd (fun y => pd J d y) c 0 = -(1 / 3) * Ric c d)
    (v : Point n) :
    ∑ c, ∑ d, v c * v d * pd (fun y => pd (fun w => (Real.sqrt (J w))⁻¹) d y) c 0
      = (1 / 6) * ∑ c, ∑ d, Ric c d * v c * v d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [invSqrt_pd_pd J c d 0 hJ hJval hcrit, hJhess c d]
  ring

/-- **The amplitude trace 2-jet = `(1/6) Scal`.**  Diagonal contraction of the amplitude Hessian:
    `∑_i ∂_i² u₀(0) = (1/6) ∑_i Ric_{ii} = (1/6) Scal` (with `Scal = ∑_i Ric_{ii}` at the RNC origin,
    matching `R = ∑ᵢ Ric_{ii}` in the heat-kernel capstone).  Same carried input `hJhess`. -/
theorem invSqrt_trace_hessian_scal (J : Point n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hJ : ContDiff ℝ ⊤ J) (hJval : J 0 = 1) (hcrit : ∀ e, pd J e 0 = 0)
    (hJhess : ∀ c d, pd (fun y => pd J d y) c 0 = -(1 / 3) * Ric c d) :
    ∑ i, pd (fun y => pd (fun w => (Real.sqrt (J w))⁻¹) i y) i 0
      = (1 / 6) * ∑ i, Ric i i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [invSqrt_pd_pd J i i 0 hJ hJval hcrit, hJhess i i]
  ring

end QIQTH.VanVleckTwoJet

#print axioms QIQTH.VanVleckTwoJet.invSqrt_pd_pd
#print axioms QIQTH.VanVleckTwoJet.invSqrt_directional_hessian_ricci
#print axioms QIQTH.VanVleckTwoJet.invSqrt_trace_hessian_scal
