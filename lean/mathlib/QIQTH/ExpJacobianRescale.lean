import Mathlib
import QIQTH.ExpMap
import QIQTH.ExpDiffVariation
import QIQTH.ExpJacobianFlow
import QIQTH.JacobianDet

/-!
# EXP-JET3-3a — the geodesic-rescaling (ray-vs-geodesic) step toward `W(τ) = expJacobianMat(τ•v)`

This brick lands the **S1 ray-vs-geodesic identity** that underlies the `Y = D exp`
identification (`docs/qg_roadmap/MATRIX_JACOBI_PLAN.md`), namely the exact statement that the
exp-map along the ray `s ↦ exp_p(s•v)` **is** the geodesic through `p` in direction `v`:

  `exp_p(s•v) = (expTube p v s).1`   (position at parameter `s` of the direction-`v` geodesic tube),

for `‖v‖ ≤ expRho` and `|s| ≤ 1`.  This is the geometric heart of the rescaling
`γ_{p,sv}(1) = γ_{p,v}(s)` (`geodesic_rescale` + geodesic local uniqueness): the confined tube
through `(p, s•v)` at parameter `1` equals the velocity-rescaled tube through `(p, v)` at
parameter `s`.  A short corollary differentiates it to expose the **ray velocity**
`∂_t exp_p(t•v)|_{t=s} = (expTube p v s).2` — the geodesic velocity along the whole ray, not just
at the centre.

## What LANDED (the floor)
* `expMap_smul_eq_expTube` — `exp_p(s•v) = (expTube p v s).1` for `‖v‖ ≤ expRho`, `|s| ≤ 1`.
  (The exact ray-vs-geodesic identity, extracted as a clean standalone lemma from the uniqueness
  argument previously buried inside `expMap_radial_accel`.)
* `hasDerivAt_expMap_smul_ray` — `HasDerivAt (fun t => exp_p(t•v)) ((expTube p v s).2) s` for
  `|s| < 1`: the radial derivative of `exp_p` along the ray equals the direction-`v` geodesic
  velocity at parameter `s`.

## What is CHECKPOINTED (the target — genuinely deep, NOT done here)
The `TARGET` of EXP-JET3-3 — connecting `expJacobianMat(τ•v)` (the differential `D exp_p` at the
*scaled* point `τ•v`) to the direction-`v` Jacobi flow `Φ` at parameter `τ`, hence the regularized
matrix Jacobi field `W(τ) = expJacobianMat(τ•v)` with `B(τ) = τ·W(τ)`, `det B(τ) = τⁿ·expJacobianDet(τ•v)`
— is NOT landed here.  What remains precisely:
  * the **`Φ`-flow rescaling**: relate the EXP-JET3-1/2 operator flow `Φ_{τv}` (differential at
    `τ•v`) to `Φ_v` at parameter `τ` — i.e. differentiate the ray identity above transversally to
    the ray.  This is the smooth-dependence-of-geodesics-on-IC (transverse) content, and the flow
    `Φ` lives only on `[0,1]` (`HasDerivWithinAt`), so the endpoint/within-interval Jacobi
    machinery does not apply off-the-shelf;
  * the **`τ`-scaling of the differential** `D exp_p(τ•v)[τ·w] = J_w(τ)` (Jacobi field with IC
    `J(0)=0, J'(0)=w`) and the resulting `det B(τ) = τⁿ · expJacobianDet(τ•v)`;
  * the change-of-basis / frame determinant tying `det W(τ)` to `expJacobianDet(τ•v)`.
These are the machinery flagged repo-absent in `MATRIX_JACOBI_PLAN.md` (no-conjugate-points +
`derivWithin` Jacobi equation + rescaling + frame det).  Consequently this brick does **NOT**
discharge `hYexp`, does **NOT** make the van-Vleck radial ODE unconditional, and is **NOT**
`a₁ = R/6`.
-/

set_option maxHeartbeats 2000000

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **EXP-JET3-3a (FLOOR) — the ray-vs-geodesic identity.**
`exp_p(s•v) = (expTube p v s).1` for `‖v‖ ≤ expRho g gi hC p` and `|s| ≤ 1`: the exp-map along
the ray in direction `v` traces the direction-`v` geodesic tube.  Proof: the velocity-rescaled
tube `τ ↦ L_s(expTube p v (s·τ))` (`geodesic_rescale`) and the confined tube through `(p, s•v)`
are both geodesic integral curves through `(p, s•v)`, hence agree by `geodesic_local_unique` on a
`0`-neighbourhood; evaluating the position component at `τ = 1` gives the identity. -/
theorem expMap_smul_eq_expTube
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) {s : ℝ} (hs : |s| ≤ 1) :
    expMap g gi hC p (s • v) = (expTube g gi hC p v s).1 := by
  -- The confined tube through `(p, v)`.
  obtain ⟨hY0, hYd, -⟩ := expTube_spec g gi hC p v hv
  -- `‖s • v‖ ≤ expRho` since `|s| ≤ 1`.
  have hsv : ‖s • v‖ ≤ expRho g gi hC p := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ ≤ expRho g gi hC p := hv
  -- The confined tube through `(p, s • v)`.
  obtain ⟨hZ0, hZd, -⟩ := expTube_spec g gi hC p (s • v) hsv
  -- The velocity-rescaled tube `R(τ) = L_s (expTube p v (s·τ))` is a geodesic integral curve.
  have hRd : ∀ τ : ℝ, s * τ ∈ Set.Ioo (-2 : ℝ) 2 →
      HasDerivAt (fun τ' => rescaleCLM s (expTube g gi hC p v (s * τ')))
        (geodesicField g gi (rescaleCLM s (expTube g gi hC p v (s * τ)))) τ :=
    fun τ hτ => geodesic_rescale g gi hYd s τ hτ
  -- Interval bookkeeping: the uniqueness window `(-1, 3/2)` sits inside `(-2, 2)`, and
  -- `|s·τ| ≤ 3/2 < 2` there (using `|s| ≤ 1`).
  have hIoosub : Set.Ioo (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIccsub : Set.Icc (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hRmem_arg : ∀ τ ∈ Set.Icc (-1 : ℝ) (3 / 2), s * τ ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro τ hτ
    have hτabs : |τ| ≤ 3 / 2 := by rw [abs_le]; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hlt : |s * τ| < 2 := by
      rw [abs_mul]
      calc |s| * |τ| ≤ 1 * (3 / 2) := mul_le_mul hs hτabs (abs_nonneg _) (by norm_num)
        _ = 3 / 2 := by norm_num
        _ < 2 := by norm_num
    exact Set.mem_Ioo.mpr (abs_lt.mp hlt)
  -- Bound both curves' images on the compact `[-1, 3/2]`, giving a common Lipschitz ball.
  have hZcont : ContinuousOn (expTube g gi hC p (s • v)) (Set.Icc (-1 : ℝ) (3 / 2)) :=
    fun τ hτ => ((hZd τ (hIccsub hτ)).continuousAt).continuousWithinAt
  obtain ⟨Mz, hMz⟩ :=
    (((isCompact_Icc).image_of_continuousOn hZcont).isBounded).subset_closedBall
      ((p, 0) : Point n × Point n)
  have hRcont : ContinuousOn (fun τ' => rescaleCLM s (expTube g gi hC p v (s * τ')))
      (Set.Icc (-1 : ℝ) (3 / 2)) :=
    fun τ hτ => ((hRd τ (hRmem_arg τ hτ)).continuousAt).continuousWithinAt
  obtain ⟨Mr, hMr⟩ :=
    (((isCompact_Icc).image_of_continuousOn hRcont).isBounded).subset_closedBall
      ((p, 0) : Point n × Point n)
  obtain ⟨Klip, hLip⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr))).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hZmem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      expTube g gi hC p (s • v) τ
        ∈ Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_left _ _)
      (hMz ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  have hRmem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      (fun τ' => rescaleCLM s (expTube g gi hC p v (s * τ'))) τ
        ∈ Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_right _ _)
      (hMr ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  -- Geodesic local uniqueness: the two integral curves agree on `(-1, 3/2)`.
  have hEqon := geodesic_local_unique g gi (a := -1) (b := 3 / 2) (t₀ := 0)
    ⟨by norm_num, by norm_num⟩ hLip
    (fun τ hτ => ⟨hZd τ (hIoosub hτ), hZmem τ hτ⟩)
    (fun τ hτ => ⟨hRd τ (hRmem_arg τ (Set.Ioo_subset_Icc_self hτ)), hRmem τ hτ⟩)
    (by rw [hZ0]; simp [mul_zero, hY0, rescaleCLM_apply])
  have hZR := hEqon (show (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) (3 / 2) from ⟨by norm_num, by norm_num⟩)
  -- Evaluate at `τ = 1`: position of `expTube p (s•v) 1` = position of `L_s (expTube p v s)`.
  simp only [expMap]
  rw [hZR]
  simp [rescaleCLM_apply, mul_one]

/-- **EXP-JET3-3a (FLOOR, corollary) — the ray velocity is the geodesic velocity.**
`∂_t exp_p(t•v)|_{t=s} = (expTube p v s).2` for `|s| < 1`: differentiating the ray-vs-geodesic
identity `exp_p(t•v) = (expTube p v t).1` (which holds on a neighbourhood of `s`) and using the
position-component of the geodesic ODE `d/dτ (expTube p v τ).1 = (expTube p v τ).2`. -/
theorem hasDerivAt_expMap_smul_ray
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun t : ℝ => expMap g gi hC p (t • v)) ((expTube g gi hC p v s).2) s := by
  -- Position-component of the geodesic ODE at parameter `s` (∈ (-2, 2) since |s| < 1).
  obtain ⟨-, hYd, -⟩ := expTube_spec g gi hC p v hv
  have hsmem : s ∈ Set.Ioo (-2 : ℝ) 2 := by
    have := abs_lt.mp hs; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hpos : HasDerivAt (fun u => (expTube g gi hC p v u).1) ((expTube g gi hC p v s).2) s := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt s
      (hYd s hsmem)
    simpa [geodesicField] using this
  -- The ray identity holds on the whole `|t| ≤ 1`, in particular a neighbourhood of `s`.
  have hEq : (fun t : ℝ => expMap g gi hC p (t • v))
      =ᶠ[𝓝 s] (fun u => (expTube g gi hC p v u).1) := by
    have hmem : Metric.ball s (1 - |s|) ∈ 𝓝 s := Metric.ball_mem_nhds s (by linarith)
    filter_upwards [hmem] with t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have htle : |t| ≤ 1 := by
      have : |t| < 1 :=
        calc |t| = |t - s + s| := by ring_nf
          _ ≤ |t - s| + |s| := abs_add_le _ _
          _ < (1 - |s|) + |s| := by linarith [ht]
          _ = 1 := by ring
      exact this.le
    exact expMap_smul_eq_expTube g gi hC p v hv htle
  exact hpos.congr_of_eventuallyEq hEq

end QIQTH.ExpMap
