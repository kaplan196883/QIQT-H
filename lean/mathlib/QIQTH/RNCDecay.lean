/-
  RNCDecay — the general "vanishing-to-order-m ⟹ O(‖v‖^m) on a ball" decay estimates.

  Phase J5-residue of the Jacobi/van-Vleck campaign (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md).
  J5-offdiag reduced the RNC off-diagonal residual to two decaying residues: the metric deviation
  `gⁱʲ(v) − δⁱʲ = O(‖v‖²)` and the Christoffel terms `Γ(v) = O(‖v‖)`.  This file provides the
  underlying vector-calculus DECAY estimates that control those residues:

    * `decay_order_one`  — a scalar field `f` with `f 0 = 0` and `‖fderiv f‖ ≤ M` on a ball obeys
      `|f v| ≤ M‖v‖` there (a direct mean-value inequality, `O(‖v‖)`);
    * `fderiv_decay`     — the gradient itself decays: `‖fderiv f w‖ ≤ M‖w‖` when `fderiv f 0 = 0`
      and `‖fderiv (fderiv f)‖ ≤ M` (the intermediate step of the 2nd-order bound);
    * `decay_order_two`  — a field vanishing to 2nd order (`f 0 = 0`, `fderiv f 0 = 0`) with a bounded
      2nd derivative obeys `|f v| ≤ M‖v‖²` (`O(‖v‖²)`), via `fderiv_decay` + the MVT with a fixed
      linear map.  ⚠ The constant is `M` (crude iterated-MVT), not the sharp Taylor `M/2`.
    * `norm_le_rncRadial`, `decay_order_one_radial`, `decay_order_two_radial` — restatements with the
      ambient sup-norm `‖v‖` replaced by the Euclidean RNC radial coordinate `rncRadial v = √∑(vⁱ)²`,
      using the clean half `‖v‖_sup ≤ rncRadial v`.

  ⚠ HONEST SCOPE.  These are the GENERAL decay estimates (a function vanishing to order `m` at `0`
  with a bounded `m`-th derivative on a ball is `O(‖v‖^m)`).  They are the tool for the residue
  reduction; they are NOT yet the residue bounds themselves (applying them to `Γ` / `gⁱʲ−δⁱʲ` and
  combining with the Jacobi/van-Vleck data is the next step), NOT the residual bound, NOT `a₁ = R/6`.
  The derivative bounds `M` and the radius `ρ > 0` are carried as EXPLICIT hypotheses — the decay
  FAILS without a derivative bound (not vacuous).
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.RadialDistance

namespace QIQTH.RNCDecay

open QIQTH.Curvature QIQTH.RadialDistance
open scoped BigOperators

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### #1 — the `O(‖v‖)` bound (mean-value inequality) -/

/-- **First-order decay `|f v| ≤ M‖v‖`.**  If a scalar field `f` on the coordinate chart vanishes at
    the center (`f 0 = 0`), is differentiable on the closed ball `B(0,ρ)` (`ρ > 0`), and has Fréchet
    derivative bounded by `M` there, then it decays linearly: `|f v| ≤ M‖v‖` for `‖v‖ ≤ ρ`.  A direct
    application of the convex-set mean-value inequality with base point `0`. -/
theorem decay_order_one (f : Point n → ℝ) (M ρ : ℝ) (hρ : 0 < ρ)
    (hf0 : f 0 = 0)
    (hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ f w)
    (hbound : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ f w‖ ≤ M)
    {v : Point n} (hv : ‖v‖ ≤ ρ) :
    |f v| ≤ M * ‖v‖ := by
  have hmem : v ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [mem_closedBall_zero_iff]; exact hv
  have h0 : (0 : Point n) ∈ Metric.closedBall (0 : Point n) ρ :=
    Metric.mem_closedBall_self hρ.le
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff hbound
    (convex_closedBall _ _) h0 hmem
  rw [hf0, sub_zero, sub_zero] at key
  rwa [Real.norm_eq_abs] at key

/-! ### intermediate — the gradient decays -/

/-- **Gradient decay `‖fderiv f w‖ ≤ M‖w‖`.**  If the derivative vanishes at the center
    (`fderiv f 0 = 0`), `fderiv f` is differentiable on `B(0,ρ)`, and the second derivative is bounded
    by `M` there, then the gradient decays linearly: `‖fderiv f w‖ ≤ M‖w‖` for `w ∈ B(0,ρ)`.  This is
    `decay_order_one` applied to the vector-valued field `fderiv f` (whose value at `0` is `0` and
    whose derivative — the second derivative of `f` — is bounded by `M`). -/
theorem fderiv_decay (f : Point n → ℝ) (M ρ : ℝ) (hρ : 0 < ρ)
    (hdf0 : fderiv ℝ f 0 = 0)
    (hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ (fderiv ℝ f) w)
    (hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M)
    {w : Point n} (hw : w ∈ Metric.closedBall (0 : Point n) ρ) :
    ‖fderiv ℝ f w‖ ≤ M * ‖w‖ := by
  have h0 : (0 : Point n) ∈ Metric.closedBall (0 : Point n) ρ :=
    Metric.mem_closedBall_self hρ.le
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    hdiff2 hbound2 (convex_closedBall _ _) h0 hw
  rw [hdf0, sub_zero, sub_zero] at key
  exact key

/-! ### #2 — the `O(‖v‖²)` bound (iterated MVT) -/

/-- **Second-order decay `|f v| ≤ M‖v‖²`.**  If a scalar field `f` vanishes to second order at the
    center (`f 0 = 0` and `fderiv f 0 = 0` — the RNC condition for `gⁱʲ − δⁱʲ`), is differentiable on
    `B(0,ρ)` (`ρ > 0`) with `fderiv f` also differentiable there, and has its second derivative bounded
    by `M`, then it decays quadratically: `|f v| ≤ M‖v‖²` for `‖v‖ ≤ ρ`.

    Route: `fderiv_decay` gives `‖fderiv f x‖ ≤ M‖x‖ ≤ M‖v‖` on the smaller ball `B(0,‖v‖)`, then the
    mean-value inequality with fixed linear map `φ = fderiv f 0 = 0` gives
    `|f v − f 0 − φ(v)| ≤ (M‖v‖)·‖v‖`.

    ⚠ The constant is `M` (crude iterated mean-value), not the sharp 2nd-order-Taylor `M/2`; the task
    explicitly allows the cruder constant. -/
theorem decay_order_two (f : Point n → ℝ) (M ρ : ℝ) (hρ : 0 < ρ)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ f w)
    (hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ (fderiv ℝ f) w)
    (hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M)
    {v : Point n} (hv : ‖v‖ ≤ ρ) :
    |f v| ≤ M * ‖v‖ ^ 2 := by
  -- `M ≥ 0` (a norm is bounded by it at the center).
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)) (hbound2 0 (Metric.mem_closedBall_self hρ.le))
  -- the smaller ball `B(0,‖v‖)` sits inside `B(0,ρ)`.
  have hsub : Metric.closedBall (0 : Point n) ‖v‖ ⊆ Metric.closedBall (0 : Point n) ρ :=
    Metric.closedBall_subset_closedBall hv
  -- gradient decay on `B(0,ρ)`.
  have hgrad : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ f w‖ ≤ M * ‖w‖ :=
    fun w hw => fderiv_decay f M ρ hρ hdf0 hdiff2 hbound2 hw
  -- on `B(0,‖v‖)`, `‖fderiv f x − φ‖ = ‖fderiv f x‖ ≤ M‖x‖ ≤ M‖v‖`.
  have hb : ∀ x ∈ Metric.closedBall (0 : Point n) ‖v‖, ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ M * ‖v‖ := by
    intro x hx
    have hxv : ‖x‖ ≤ ‖v‖ := by rw [mem_closedBall_zero_iff] at hx; exact hx
    rw [hdf0, sub_zero]
    calc ‖fderiv ℝ f x‖ ≤ M * ‖x‖ := hgrad x (hsub hx)
      _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_left hxv hM
  -- the mean-value inequality with fixed linear map `φ = fderiv f 0`.
  have h0 : (0 : Point n) ∈ Metric.closedBall (0 : Point n) ‖v‖ :=
    Metric.mem_closedBall_self (norm_nonneg v)
  have hvv : v ∈ Metric.closedBall (0 : Point n) ‖v‖ := by
    rw [mem_closedBall_zero_iff]
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := f) (φ := fderiv ℝ f 0)
    (fun x hx => hdiff x (hsub hx)) hb (convex_closedBall _ _) h0 hvv
  rw [hf0, hdf0] at key
  simp only [ContinuousLinearMap.zero_apply, sub_zero] at key
  rw [Real.norm_eq_abs] at key
  calc |f v| ≤ M * ‖v‖ * ‖v‖ := key
    _ = M * ‖v‖ ^ 2 := by ring

/-! ### #3 — restatement in the Euclidean RNC radial coordinate `rncRadial` -/

/-- **The ambient sup-norm is dominated by the Euclidean radial coordinate**: `‖v‖ ≤ rncRadial v`.
    On `Point n = Fin n → ℝ` the ambient norm is the sup norm `maxᵢ |vⁱ|`, while
    `rncRadial v = √∑(vⁱ)²`; each `|vⁱ| = √((vⁱ)²) ≤ √∑(vʲ)²`. -/
theorem norm_le_rncRadial (v : Point n) : ‖v‖ ≤ rncRadial v := by
  rw [pi_norm_le_iff_of_nonneg (rncRadial_nonneg v)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, rncRadial]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => (v j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- **First-order decay in the RNC radial coordinate**: `|f v| ≤ M · rncRadial v` when
    `rncRadial v ≤ ρ`.  Since `‖v‖ ≤ rncRadial v ≤ ρ`, `decay_order_one` applies and
    `M‖v‖ ≤ M · rncRadial v`. -/
theorem decay_order_one_radial (f : Point n → ℝ) (M ρ : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hf0 : f 0 = 0)
    (hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ f w)
    (hbound : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ f w‖ ≤ M)
    {v : Point n} (hv : rncRadial v ≤ ρ) :
    |f v| ≤ M * rncRadial v := by
  have hnv : ‖v‖ ≤ ρ := le_trans (norm_le_rncRadial v) hv
  calc |f v| ≤ M * ‖v‖ := decay_order_one f M ρ hρ hf0 hdiff hbound hnv
    _ ≤ M * rncRadial v := mul_le_mul_of_nonneg_left (norm_le_rncRadial v) hM

/-- **Second-order decay in the RNC radial coordinate**: `|f v| ≤ M · (rncRadial v)²` when
    `rncRadial v ≤ ρ`, for a field vanishing to second order.  Since `‖v‖ ≤ rncRadial v ≤ ρ`,
    `decay_order_two` applies and `M‖v‖² ≤ M · (rncRadial v)²`. -/
theorem decay_order_two_radial (f : Point n → ℝ) (M ρ : ℝ) (hρ : 0 < ρ)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0)
    (hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ f w)
    (hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, DifferentiableAt ℝ (fderiv ℝ f) w)
    (hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) ρ, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M)
    {v : Point n} (hv : rncRadial v ≤ ρ) :
    |f v| ≤ M * (rncRadial v) ^ 2 := by
  have hM : 0 ≤ M :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)) (hbound2 0 (Metric.mem_closedBall_self hρ.le))
  have hnv : ‖v‖ ≤ ρ := le_trans (norm_le_rncRadial v) hv
  calc |f v| ≤ M * ‖v‖ ^ 2 := decay_order_two f M ρ hρ hf0 hdf0 hdiff hdiff2 hbound2 hnv
    _ ≤ M * (rncRadial v) ^ 2 := by
        gcongr
        exact norm_le_rncRadial v

end QIQTH.RNCDecay
