/-
  RadialDistance — the Riemann-normal-coordinate (RNC) radial coordinate and the Euler radial field.

  Phase J2 of the Jacobi/van-Vleck campaign (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md): the setup for the
  radial transport ODE (J3) and the parametrix function (J4).

  In Riemann normal coordinates centered at `y`, the geodesic-normal radial coordinate is `r = ‖v‖` where
  `v : Point n` is the normal coordinate of the point.  This file builds:
    * `rncRadialSq v = ∑ i (vⁱ)²`  — the squared radial coordinate `r²` (argument of the flat Gaussian
      `e^{−r²/4t}`), a global polynomial, and its square-root `rncRadial v = ‖v‖`;
    * the gradient `∇r² = 2v` (`pd_rncRadialSq`);
    * the Euler / radial derivative operator `radialDeriv f = ∑ vⁱ ∂ᵢ f` (which acts as `r ∂_r`), and
      Euler's identity `radialDeriv r² = 2 r²` (`r²` is degree-2 homogeneous) — the operator the DeWitt
      transport recursion `(k + r∂_r)u_k = …` (J3) uses.

  ⚠ HONEST SCOPE.  This is the RNC radial COORDINATE `‖v‖`, which is the geodesic-normal radial coordinate
  BY DEFINITION of normal coordinates.  It is NOT the claim that `‖v‖` equals the true minimizing geodesic
  distance in a general metric (the Gauss lemma — a separate, deferred Riemannian-geometry statement we do
  NOT need for the parametrix construction), NOT the residual bound, NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.RadialDistance

open QIQTH.Curvature
open scoped BigOperators

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### The radial coordinate and its square -/

/-- The squared RNC radial coordinate `r² = ‖v‖² = ∑ i (vⁱ)²` — the argument of the flat heat Gaussian
    `e^{−r²/4t}`. -/
noncomputable def rncRadialSq (v : Point n) : ℝ := ∑ i, (v i) ^ 2

/-- The RNC radial coordinate `r = ‖v‖ = √(∑ i (vⁱ)²)`. -/
noncomputable def rncRadial (v : Point n) : ℝ := Real.sqrt (rncRadialSq v)

/-! ### Diagonal / basic values -/

@[simp] theorem rncRadialSq_zero : rncRadialSq (0 : Point n) = 0 := by
  simp [rncRadialSq]

theorem rncRadialSq_nonneg (v : Point n) : 0 ≤ rncRadialSq v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

@[simp] theorem rncRadial_zero : rncRadial (0 : Point n) = 0 := by
  simp [rncRadial]

theorem rncRadial_nonneg (v : Point n) : 0 ≤ rncRadial v :=
  Real.sqrt_nonneg _

/-- `r² = 0 ⇔ v = 0` — the radial coordinate vanishes only at the center of the normal-coordinate chart. -/
theorem rncRadialSq_eq_zero_iff (v : Point n) : rncRadialSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), (v i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h
    funext i
    have := h0 i (Finset.mem_univ i)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · rintro rfl; exact rncRadialSq_zero

/-- For `v ≠ 0` the squared radial coordinate is strictly positive. -/
theorem rncRadialSq_pos {v : Point n} (hv : v ≠ 0) : 0 < rncRadialSq v :=
  lt_of_le_of_ne (rncRadialSq_nonneg v) (fun h => hv ((rncRadialSq_eq_zero_iff v).1 h.symm))

/-- `r ≥ 0` and squaring recovers `r²`: `(rncRadial v)² = rncRadialSq v` (since `r² ≥ 0`). -/
theorem rncRadial_sq (v : Point n) : (rncRadial v) ^ 2 = rncRadialSq v := by
  rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg v)]

/-! ### Smoothness of `r²` (a polynomial) -/

/-- Each coordinate projection `v ↦ vⁱ` is `C∞` (it is a continuous linear map). -/
theorem coord_contDiff (i : Fin n) : ContDiff ℝ ⊤ (fun v : Point n => v i) :=
  (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff

/-- Each summand `v ↦ (vⁱ)²` is `C∞`. -/
theorem coord_sq_contDiff (i : Fin n) : ContDiff ℝ ⊤ (fun v : Point n => (v i) ^ 2) :=
  (coord_contDiff i).pow 2

/-- `r² = ∑ (vⁱ)²` is `C∞` (a polynomial: sum of squares of coordinate projections). -/
theorem rncRadialSq_contDiff : ContDiff ℝ ⊤ (rncRadialSq : Point n → ℝ) :=
  ContDiff.sum (fun i _ => coord_sq_contDiff i)

/-- `r = √(r²)` is `C∞` away from the center `v ≠ 0` (where `r² > 0`; `√` is smooth on the positives). -/
theorem rncRadial_contDiffAt {v : Point n} (hv : v ≠ 0) :
    ContDiffAt ℝ ⊤ (rncRadial : Point n → ℝ) v := by
  have hpos : rncRadialSq v ≠ 0 := (rncRadialSq_pos hv).ne'
  exact (Real.contDiffAt_sqrt hpos).comp v (rncRadialSq_contDiff.contDiffAt)

/-! ### The gradient of `r²`:  `∇r² = 2v` -/

/-- Partial derivative of a squared coordinate: `∂ⱼ (wⁱ)² = 2vⁱ` if `i = j`, else `0`. -/
theorem pd_coord_sq (i j : Fin n) (v : Point n) :
    pd (fun w => (w i) ^ 2) j v = if i = j then 2 * v i else 0 := by
  simp only [pd]
  have hupd : (fun t => (Function.update v j t i) ^ 2)
      = (fun t => (if i = j then t else v i) ^ 2) := by
    funext t; rw [Function.update_apply]
  rw [hupd]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **The gradient `∇r² = 2v`**: `∂ⱼ r² = 2 vⱼ`.  Euler's degree-2 gradient. -/
theorem pd_rncRadialSq (j : Fin n) (v : Point n) :
    pd rncRadialSq j v = 2 * v j := by
  have hF : ∀ k ∈ (Finset.univ : Finset (Fin n)), PdiffAt (fun w => (w k) ^ 2) j v :=
    fun k _ => PdiffAt_of_contDiff _ (coord_sq_contDiff k) j v
  calc pd rncRadialSq j v
      = ∑ k, pd (fun w => (w k) ^ 2) j v :=
        pd_sum Finset.univ (fun k w => (w k) ^ 2) j v hF
    _ = ∑ k, (if k = j then 2 * v k else 0) :=
        Finset.sum_congr rfl (fun k _ => pd_coord_sq k j v)
    _ = 2 * v j := by rw [Finset.sum_ite_eq']; simp

/-! ### The Euler / radial vector field  `r ∂_r = ∑ vⁱ ∂ᵢ` -/

/-- The **radial (Euler) derivative** operator `r ∂_r = ∑ i vⁱ ∂ᵢ`, acting on a scalar field. -/
noncomputable def radialDeriv (f : Point n → ℝ) (v : Point n) : ℝ := ∑ i, v i * pd f i v

/-- **Euler's identity for `r²`**: `(r ∂_r) r² = 2 r²`.  Since `r²` is degree-2 homogeneous,
    `∑ vⁱ · 2vⁱ = 2 ∑ (vⁱ)² = 2 r²`.  This is the operator the DeWitt transport recursion (J3) uses. -/
theorem radialDeriv_rncRadialSq (v : Point n) :
    radialDeriv rncRadialSq v = 2 * rncRadialSq v := by
  simp only [radialDeriv, rncRadialSq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pd_rncRadialSq i v]; ring
