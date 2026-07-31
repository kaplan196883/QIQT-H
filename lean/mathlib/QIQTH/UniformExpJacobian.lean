/-
  UniformExpJacobian — the COMPACT-UNIFORM near-identity estimate for the exp-Jacobian, and the
  common nondegeneracy radius it forces (J4-18, docs/qg_roadmap; toward compact-uniform a₁ = R/6).

  Setting.  `Point n = Fin n → ℝ`; `exp_q := expMap g gi hC q`; the exp-Jacobian at velocity `v` is
  the continuous-linear map `D_v exp_q = fderiv ℝ (expMap g gi hC q) v : Point n →L[ℝ] Point n`.
  At `v = 0` it is the identity (`QIQTH.PullbackMetric.fderiv_expMap_zero`).

  The compact-uniform obstruction toward a₁ = R/6 is a SINGLE nondegeneracy radius `ρ₀ > 0` working
  for ALL base points `q` in a fixed compact `K` at once: `exp_q` is a local diffeomorphism (its
  Jacobian is invertible) on the whole velocity ball `‖v‖ < ρ₀`, uniformly over `q ∈ K`.  The clean
  route (per a GPT-5.5 consult) is a uniform near-identity Lipschitz estimate
      `‖D_v exp_q − Id‖ ≤ M · ‖v‖`   (uniform in `q ∈ K`),
  NOT a `min` of pointwise inverse-function-theorem radii.

  ## What is DERIVED here (no firewall on the conclusion)
  * `expMap_jacobian_near_id_uniform` — the uniform near-identity estimate
    `‖D_v exp_q − Id‖ ≤ M · ‖v‖` for all `q ∈ K`, `‖v‖ < r`, obtained from the vector-valued mean
    value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`) applied to `y ↦ D_y exp_q` on
    the ball, whose value at `0` is `Id` (`fderiv_expMap_zero`) and whose derivative is bounded by
    `M`.
  * `expMap_common_nondeg_radius` — the COMMON nondegeneracy radius: a SINGLE `ρ₀ > 0` such that for
    all `q ∈ K`, `‖v‖ < ρ₀` ⟹ `IsUnit (D_v exp_q)`.  Take `ρ₀ = min r (1/(2(M+1)))`; then
    `‖Id − D_v exp_q‖ = ‖D_v exp_q − Id‖ ≤ M‖v‖ < 1/2 < 1`, so `D_v exp_q = 1 − (1 − D_v exp_q)` is a
    unit by `isUnit_one_sub_of_norm_lt_one`.

  ## HONEST FIREWALL — the carried uniform second-jet input `hjet`
  Both theorems take as an explicit hypothesis a UNIFORM SECOND-ORDER JET BOUND: a single `M ≥ 0`
  and radius `r > 0` such that for every `q ∈ K` and `‖x‖ < r`, the second jet `y ↦ D_y exp_q` is
  differentiable at `x` with `‖fderiv ℝ (fun y => D_y exp_q) x‖ ≤ M`.  This is a genuine INPUT — the
  uniform-over-`K` C²-control of the exponential map (the `sup_{q∈K} ‖D² exp_q‖` bound coming from
  the uniform confinement + uniform ambient Christoffel jet bounds of `BoundedGeometry` /
  `BoundedGeometryConfine` via the variational Jacobi ODE).  It is NOT the conclusion: the
  conclusions are the near-identity Lipschitz estimate `‖D − Id‖ ≤ M‖v‖` and the invertibility
  `IsUnit D`, neither of which is assumed.  Deriving the uniform second-jet bound `M` itself from
  `BoundedGeometry` is the remaining (large) step; it is firewalled here, clearly labelled.
-/
import Mathlib
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.ExpMap
import QIQTH.PullbackMetric

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.PullbackMetric

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **J4-18 (PRIMARY) — the compact-uniform near-identity estimate for the exp-Jacobian.**

    Given the uniform second-jet input `hjet` (a single `M ≥ 0` bounding `‖D² exp_q‖` over `q ∈ K`
    on the velocity ball `‖x‖ < r`, together with differentiability of the second jet there), the
    exp-Jacobian `D_v exp_q = fderiv ℝ (expMap g gi hC q) v` satisfies the uniform near-identity
    Lipschitz estimate
        `‖D_v exp_q − Id‖ ≤ M · ‖v‖`   for all `q ∈ K`, `‖v‖ < r`.

    DERIVED from the vector-valued mean value inequality on `y ↦ D_y exp_q`, whose value at `0` is
    `Id` (`fderiv_expMap_zero`) and whose derivative is `≤ M` on the ball.  The estimate itself is
    NOT assumed; only the uniform second-order jet bound is carried (an honest uniform-C² input). -/
theorem expMap_jacobian_near_id_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (_hK : IsCompact K)
    (r : ℝ) (_hr : 0 < r) (M : ℝ) (_hM0 : 0 ≤ M)
    (hjet : ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      DifferentiableAt ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x ∧
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M) :
    ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r →
      ‖fderiv ℝ (expMap g gi hC q) v - ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖v‖ := by
  intro q hq v hv
  -- The second jet `y ↦ D_y exp_q`, differentiable and derivative-bounded on the open ball.
  set f : Point n → (Point n →L[ℝ] Point n) := fun y => fderiv ℝ (expMap g gi hC q) y with hf
  have hdiff : ∀ x ∈ Metric.ball (0 : Point n) r, DifferentiableAt ℝ f x := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    exact (hjet q hq x hx).1
  have hbound : ∀ x ∈ Metric.ball (0 : Point n) r, ‖fderiv ℝ f x‖ ≤ M := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    exact (hjet q hq x hx).2
  have h0mem : (0 : Point n) ∈ Metric.ball (0 : Point n) r := Metric.mem_ball_self _hr
  have hvmem : v ∈ Metric.ball (0 : Point n) r := by
    rw [mem_ball_zero_iff]; exact hv
  -- Mean value inequality: `‖f v − f 0‖ ≤ M · ‖v − 0‖`.
  have hmv := (convex_ball (0 : Point n) r).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound h0mem hvmem
  -- `f 0 = Id` and `‖v − 0‖ = ‖v‖`.
  have hf0 : f 0 = ContinuousLinearMap.id ℝ (Point n) := by
    rw [hf]; exact fderiv_expMap_zero g gi hC q
  rw [hf0, sub_zero] at hmv
  exact hmv

/-- **J4-18 (SECONDARY) — the COMMON nondegeneracy radius over a compact base set.**

    From the uniform near-identity estimate (`expMap_jacobian_near_id_uniform`), there is a SINGLE
    radius `ρ₀ > 0` — the `q`-independent replacement for the per-point inverse-function-theorem
    radius — such that for every `q ∈ K` and every velocity `v` with `‖v‖ < ρ₀`, the exp-Jacobian
    `D_v exp_q` is invertible (`IsUnit`), i.e. `exp_q` is a local diffeomorphism on the whole
    velocity ball `‖v‖ < ρ₀`, uniformly over `q ∈ K`.

    `ρ₀ = min r (1/(2(M+1)))`.  Then `‖Id − D_v exp_q‖ = ‖D_v exp_q − Id‖ ≤ M‖v‖ ≤ M/(2(M+1)) <
    1/2 < 1`, and `D_v exp_q = 1 − (1 − D_v exp_q)` is a unit by `isUnit_one_sub_of_norm_lt_one`.
    Same honest firewall: the uniform second-jet bound `hjet` is the only carried input. -/
theorem expMap_common_nondeg_radius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (M : ℝ) (hM0 : 0 ≤ M)
    (hjet : ∀ q ∈ K, ∀ x : Point n, ‖x‖ < r →
      DifferentiableAt ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x ∧
      ‖fderiv ℝ (fun y => fderiv ℝ (expMap g gi hC q) y) x‖ ≤ M) :
    ∃ ρ₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
      IsUnit (fderiv ℝ (expMap g gi hC q) v) := by
  have hM1 : (0 : ℝ) < 2 * (M + 1) := by positivity
  set ρ₀ : ℝ := min r (1 / (2 * (M + 1))) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by
    rw [hρ₀]; exact lt_min hr (by positivity)
  refine ⟨ρ₀, hρ₀pos, ?_⟩
  intro q hq v hv
  -- `v` is inside the near-identity radius `r`.
  have hvr : ‖v‖ < r := lt_of_lt_of_le hv (by rw [hρ₀]; exact min_le_left _ _)
  -- Uniform near-identity estimate at `(q, v)`.
  have hne := expMap_jacobian_near_id_uniform g gi hC hK r hr M hM0 hjet q hq v hvr
  -- Abbreviate the Jacobian.
  set D : Point n →L[ℝ] Point n := fderiv ℝ (expMap g gi hC q) v with hD
  -- `‖v‖ ≤ 1/(2(M+1))`.
  have hvle : ‖v‖ ≤ 1 / (2 * (M + 1)) := le_of_lt (lt_of_lt_of_le hv (by rw [hρ₀]; exact min_le_right _ _))
  -- `M · ‖v‖ ≤ M / (2(M+1)) < 1`.
  have hMv : M * ‖v‖ < 1 := by
    have h1 : M * ‖v‖ ≤ M * (1 / (2 * (M + 1))) :=
      mul_le_mul_of_nonneg_left hvle hM0
    have h2 : M * (1 / (2 * (M + 1))) < 1 := by
      rw [mul_one_div, div_lt_one hM1]; nlinarith [hM0]
    exact lt_of_le_of_lt h1 h2
  -- `‖(1) − D‖ = ‖D − Id‖ ≤ M‖v‖ < 1`.
  have hnorm : ‖(1 : Point n →L[ℝ] Point n) - D‖ < 1 := by
    have hone : (1 : Point n →L[ℝ] Point n) = ContinuousLinearMap.id ℝ (Point n) :=
      ContinuousLinearMap.one_def
    rw [hone, norm_sub_rev]
    exact lt_of_le_of_lt hne hMv
  -- `D = 1 − (1 − D)` is a unit.
  have hu := isUnit_one_sub_of_norm_lt_one hnorm
  rwa [sub_sub_cancel] at hu

end QIQTH.ExpMap
