/-
  JacobianRadial — the exp-map Jacobian determinant `J(x) = det D(exp_p)_x`'s reachable structure
  (Phase K2 of the Jacobi-field campaign, docs/qg_roadmap/JACOBI_FIELD_PLAN.md).

  K1 (`QIQTH.JacobianDet.det_expPullback_eq`) landed the algebraic factorization
      `det g̃(x) = J(x)² · det (g ∘ exp_p)(x)`.
  This brick derives `J`'s basic analytic structure and the rearranged relation, and SETS UP the radial
  derivative `r∂_r log J`:

    * `J` is continuous near the centre (from `contDiffOn_fderiv_expMap_component` → `Matrix.det`
      continuity) and `J(0) = 1 > 0`, so `J > 0` (hence `≠ 0`) on a neighborhood of `0`
      (`expJacobianDet_pos_nhds`, `expJacobianDet_ne_zero_nhds`);
    * the rearranged K1 relation `J(x)² = det g̃(x) / det (g∘exp)(x)` where `det (g∘exp)(x) ≠ 0`
      (`jacobianDet_sq_eq`), with the centre form `J(0)²·det(g p) = det g̃(0)`
      (`jacobianDet_sq_at_zero`);
    * the additive radial-log split
        `r∂_r log(det g̃) = 2·r∂_r log J + r∂_r log(det (g∘exp))`
      (`radialDeriv_log_det_split`), the CLEAN algebraic setup that isolates `r∂_r log J` — the one
      unknown the Jacobi equation (K3) supplies.

  ⚠ HONEST SCOPE.  This is K2 = `J`'s reachable structure + the K4 setup.  It is NOT the Jacobi equation
  (K3, the VALUE of `r∂_r log J`, the congruence expansion), NOT the van-Vleck ODE (K4), NOT `a₁ = R/6`.
  The `radialDeriv_log_det_split` carries genuine positivity/regularity hypotheses (positivity of the
  three determinants near `v`; coordinate-differentiability of `J` and `det(g∘exp)` at `v`) — these are
  real regularity inputs, not the conclusion.
-/
import Mathlib
import QIQTH.JacobianDet
import QIQTH.RadialDistance

namespace QIQTH.JacobianRadial

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric
open QIQTH.JacobianDet QIQTH.RadialDistance
open Finset Matrix
open scoped Topology

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### #1 — `J` is continuous near `0`, hence positive / nonzero on a neighborhood. -/

/-- **The assembled exp-Jacobian matrix is continuous on the exp-ball.**  Each entry
    `x ↦ (D exp_p x · e_i)_a` is `ContDiffOn ℝ 2` there (`contDiffOn_fderiv_expMap_component`), hence
    continuous; reassemble entrywise. -/
theorem expJacobianMat_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContinuousOn (fun x => expJacobianMat g gi hC p x)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
  continuousOn_pi.2 (fun a => continuousOn_pi.2 (fun i =>
    (contDiffOn_fderiv_expMap_component g gi hC p i a).continuousOn))

/-- **`J = det (D exp_p)` is continuous at the centre `0`.**  `0` is interior to the exp-ball
    (`0 < expRho`), so the entrywise-continuous Jacobian matrix is `ContinuousAt 0`, and `Matrix.det`
    is continuous. -/
theorem expJacobianDet_continuousAt_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContinuousAt (expJacobianDet g gi hC p) 0 := by
  have hball : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ 𝓝 (0 : Point n) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (expRho_pos g gi hC p))
  have hM : ContinuousAt (fun x => expJacobianMat g gi hC p x) 0 :=
    (expJacobianMat_continuousOn g gi hC p).continuousAt hball
  exact (Continuous.matrix_det continuous_id).continuousAt.comp hM

/-- **`J(0) = 1 > 0`** — the Jacobian determinant is positive at the centre. -/
theorem expJacobianDet_pos_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    0 < expJacobianDet g gi hC p 0 := by
  rw [expJacobianDet_zero]; exact one_pos

/-- **`J > 0` on a neighborhood of the centre.**  `J` is continuous at `0` and `J(0) = 1 > 0`. -/
theorem expJacobianDet_pos_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∀ᶠ x in 𝓝 (0 : Point n), 0 < expJacobianDet g gi hC p x :=
  (expJacobianDet_continuousAt_zero g gi hC p).preimage_mem_nhds
    (Ioi_mem_nhds (expJacobianDet_pos_at_zero g gi hC p))

/-- **`J ≠ 0` on a neighborhood of the centre** — the exp-map is a local diffeomorphism near `p`. -/
theorem expJacobianDet_ne_zero_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∀ᶠ x in 𝓝 (0 : Point n), expJacobianDet g gi hC p x ≠ 0 := by
  filter_upwards [expJacobianDet_pos_nhds g gi hC p] with x hx using hx.ne'

/-! ### #2 — the rearranged K1 relation `J² = det g̃ / det(g∘exp)`. -/

/-- **The rearranged pullback-determinant bridge.**  Where `det (g∘exp_p)(x) ≠ 0`,
    `J(x)² = det g̃(x) / det (g∘exp_p)(x)`, from `det g̃ = J²·det(g∘exp)` (`det_expPullback_eq`). -/
theorem jacobianDet_sq_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n)
    (hD : Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b) ≠ 0) :
    (expJacobianDet g gi hC p x) ^ 2
      = Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)
        / Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b) := by
  rw [det_expPullback_eq g gi hC p x, mul_div_assoc, div_self hD, mul_one]

/-- **The centre form of the bridge.**  `J(0)²·det(g p) = det g̃(0)` — since `exp_p 0 = p` and
    `J(0) = 1`, this reads `det g̃(0) = det(g p)`, consistent with the RNC value jet `g̃(0) = g(p)`. -/
theorem jacobianDet_sq_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    (expJacobianDet g gi hC p 0) ^ 2 * Matrix.det (Matrix.of fun a b => g p a b)
      = Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p 0 i j) := by
  rw [det_expPullback_eq g gi hC p 0, expMap_apply_zero]

/-! ### #3 — the additive radial-log split (the K4 setup). -/

/-- **`pd` depends only on the germ.**  If `f =ᶠ[𝓝 x] h` then `∂ᵢ f (x) = ∂ᵢ h (x)`: the coordinate
    update map `t ↦ update x i t` is continuous with value `x` at `t = x i`, so it pulls the germ of
    `f` at `x` back to the germ of `t ↦ f (update x i t)` at `x i`, where the `deriv` reads it. -/
theorem pd_congr_of_eventuallyEq {f h : Point n → ℝ} {i : Fin n} {x : Point n}
    (hfh : f =ᶠ[𝓝 x] h) : pd f i x = pd h i x := by
  simp only [pd]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcont : Filter.Tendsto (fun t => Function.update x i t) (𝓝 (x i)) (𝓝 x) := by
    have h1 : ContinuousAt (Function.update x i) (x i) :=
      (hasDerivAt_update x i (x i)).continuousAt
    have h2 : (Function.update x i) (x i) = x := Function.update_eq_self i x
    rw [ContinuousAt, h2] at h1
    exact h1
  exact hcont.eventually hfh

/-- **`radialDeriv` depends only on the germ.**  `radialDeriv f v = ∑ vⁱ ∂ᵢf` reads `f` through the `pd`
    germs, so `f =ᶠ[𝓝 v] h ⟹ r∂_r f (v) = r∂_r h (v)`. -/
theorem radialDeriv_congr {f h : Point n → ℝ} {v : Point n} (hfh : f =ᶠ[𝓝 v] h) :
    radialDeriv f v = radialDeriv h v := by
  simp only [radialDeriv]
  exact Finset.sum_congr rfl (fun i _ => by rw [pd_congr_of_eventuallyEq hfh])

/-- **`radialDeriv` is linear on the `2•a + b` combination.**  `r∂_r (2a + b) = 2 r∂_r a + r∂_r b`
    where `a, b` are coordinate-differentiable at `v` (`pd_const_mul` + `pd_add` termwise). -/
theorem radialDeriv_two_mul_add (a b : Point n → ℝ) (v : Point n)
    (ha : ∀ i, PdiffAt a i v) (hb : ∀ i, PdiffAt b i v) :
    radialDeriv (fun x => 2 * a x + b x) v = 2 * radialDeriv a v + radialDeriv b v := by
  simp only [radialDeriv]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pd_add (fun y => 2 * a y) b i v ((ha i).const_mul 2) (hb i),
    pd_const_mul 2 a i v (ha i)]
  ring

/-- **THE ADDITIVE RADIAL-LOG SPLIT (the K4 setup).**
    `r∂_r log(det g̃) = 2·r∂_r log J + r∂_r log(det (g∘exp))`, from `det g̃ = J²·det(g∘exp)`
    (`det_expPullback_eq`), `log(J²·D) = 2 log J + log D`, and `radialDeriv` linearity/germ-locality.

    This expresses the van-Vleck radial-log-det (K4's target) in terms of `r∂_r log J` — the congruence
    expansion (K3, the genuine wall) — plus the metric-along-exp term.  The hypotheses are genuine
    regularity inputs (positivity of the two determinants on a neighborhood of `v`, giving both the
    nonvanishing needed for the log identity and `J v, det(g∘exp) v ≠ 0`; and coordinate-differentiability
    of `J` and of `det(g∘exp)` at `v`).  It is NOT the value of `r∂_r log J` (the Jacobi ODE, K3). -/
theorem radialDeriv_log_det_split (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (v : Point n)
    (hJ : ∀ᶠ x in 𝓝 v, 0 < expJacobianDet g gi hC p x)
    (hD : ∀ᶠ x in 𝓝 v, 0 < Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))
    (hJp : ∀ i, PdiffAt (expJacobianDet g gi hC p) i v)
    (hDp : ∀ i, PdiffAt (fun x => Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b)) i v) :
    radialDeriv (fun x => Real.log (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j))) v
      = 2 * radialDeriv (fun x => Real.log (expJacobianDet g gi hC p x)) v
        + radialDeriv
            (fun x => Real.log (Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))) v := by
  -- nonvanishing at `v` (from positivity at `v`).
  have hJv : expJacobianDet g gi hC p v ≠ 0 := hJ.self_of_nhds.ne'
  have hDv : Matrix.det (Matrix.of fun a b => g (expMap g gi hC p v) a b) ≠ 0 := hD.self_of_nhds.ne'
  -- coordinate-differentiability of `log J` and `log (det g∘exp)` at `v` (chain rule, `log` smooth at ≠0).
  have hlogJ : ∀ i, PdiffAt (fun x => Real.log (expJacobianDet g gi hC p x)) i v := by
    intro i
    have hbase : expJacobianDet g gi hC p (Function.update v i (v i)) ≠ 0 := by
      rw [Function.update_eq_self]; exact hJv
    exact (Real.differentiableAt_log hbase).comp (v i) (hJp i)
  have hlogD : ∀ i, PdiffAt
      (fun x => Real.log (Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))) i v := by
    intro i
    have hbase : Matrix.det (Matrix.of fun a b => g (expMap g gi hC p (Function.update v i (v i))) a b)
        ≠ 0 := by rw [Function.update_eq_self]; exact hDv
    exact (Real.differentiableAt_log hbase).comp (v i) (hDp i)
  -- the log-product identity, on a neighborhood of `v`.
  have hEq : (fun x => Real.log (Matrix.det (Matrix.of fun i j => expPullbackMetric g gi hC p x i j)))
      =ᶠ[𝓝 v] (fun x => 2 * Real.log (expJacobianDet g gi hC p x)
        + Real.log (Matrix.det (Matrix.of fun a b => g (expMap g gi hC p x) a b))) := by
    filter_upwards [hJ, hD] with x hJx hDx
    rw [det_expPullback_eq g gi hC p x, Real.log_mul (pow_ne_zero 2 hJx.ne') hDx.ne', Real.log_pow]
    push_cast; ring
  rw [radialDeriv_congr hEq, radialDeriv_two_mul_add _ _ v hlogJ hlogD]

end QIQTH.JacobianRadial
