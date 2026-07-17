/-
  VanVleck — the van-Vleck–Morette determinant `Θ = (det g̃)^{−1/2}` as a function of the
  Riemann-normal-coordinate metric field `g̃`.

  Phase J1 of the Jacobi/van-Vleck campaign (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md): the first,
  reachable brick of the off-diagonal parametrix (C4c).  `Θ` measures the volume distortion of the
  exponential map — the Jacobian factor of the geodesic parametrix — and rides directly on the built
  `det g̃` / `√det` machinery of `QIQTH/RNCExpansion.lean` and the pullback metric of
  `QIQTH/PullbackMetric.lean`.

  This file lands the OBJECT `Θ` and its elementary facts only:
    * `vanVleck`               — the definition `Θ = (√ det g̃)⁻¹`;
    * `vanVleck_zero`          — the diagonal value `Θ(0) = 1` (from `det g̃(0) = 1`);
    * `vanVleck_expPullback_zero` — the diagonal value sourced from `expPullbackMetric_at_zero`
                                    (RNC `g̃(0) = δ` in a `p`-orthonormal frame);
    * `vanVleck_pos`           — positivity `0 < Θ` where `det g̃ > 0`;
    * `vanVleck_contDiffAt`    — smoothness of `Θ` where `det g̃` is smooth and positive.

  HONEST CAPTION (binding): this is the van-Vleck determinant OBJECT.  It is NOT the residual bound,
  NOT the full off-diagonal parametrix (J4/J5), and NOT `a₁ = R/6` (J6).  The positivity / diagonal
  hypotheses (`det g̃ > 0`, `det g̃(0) = 1`, `g̃(0) = δ`) are carried EXACTLY as the source lemmas
  provide them — genuine, load-bearing, non-vacuous.
-/
import Mathlib
import QIQTH.RNCExpansion
import QIQTH.PullbackMetric

namespace QIQTH.VanVleck

open QIQTH.Curvature QIQTH.RNCExpansion QIQTH.PullbackMetric
open Real Matrix

variable {n : ℕ}

/-! ### #1 — the van-Vleck–Morette determinant as a function -/

/-- **The van-Vleck–Morette determinant** `Θ = (det g̃)^{−1/2} = (√ det g̃)⁻¹`.

    `G : Point n → Fin n → Fin n → ℝ` is the RNC metric-component field `g̃` (matching the
    `Matrix.det (G v)` convention of `QIQTH/RNCExpansion.lean`, where `G v : Fin n → Fin n → ℝ` is
    read as a `Matrix (Fin n) (Fin n) ℝ`).  `Θ v` is the volume distortion of the exp map at `v`. -/
noncomputable def vanVleck (G : Point n → Fin n → Fin n → ℝ) (v : Point n) : ℝ :=
  (Real.sqrt (Matrix.det (G v)))⁻¹

/-- Unfolding lemma / the `Θ = (√ det g̃)⁻¹` identity (deliverable #5, the link to
    `sqrtdet_taylor_coeff`: the van-Vleck side is the reciprocal of the `√det` whose 2-jet
    coefficient is `−⅙ Ric`). -/
theorem vanVleck_apply (G : Point n → Fin n → Fin n → ℝ) (v : Point n) :
    vanVleck G v = (Real.sqrt (Matrix.det (G v)))⁻¹ := rfl

/-- Restatement of #5 with an explicit name: `Θ = (√ det g̃)⁻¹`. -/
theorem vanVleck_eq_inv_sqrtdet (G : Point n → Fin n → Fin n → ℝ) (v : Point n) :
    vanVleck G v = (Real.sqrt (Matrix.det (G v)))⁻¹ := rfl

/-! ### #2 — the diagonal value `Θ(0) = 1` -/

/-- **`Θ(0) = 1` from `det g̃(0) = 1`.**  The diagonal value of the van-Vleck determinant: at the
    centre of the normal coordinates the exp map has unit Jacobian.  Carried as `det g̃(0) = 1`
    (`= √1 = 1` ⟹ `1⁻¹ = 1`). -/
theorem vanVleck_zero (G : Point n → Fin n → Fin n → ℝ) (hG0 : Matrix.det (G 0) = 1) :
    vanVleck G 0 = 1 := by
  simp only [vanVleck, hG0, Real.sqrt_one, inv_one]

/-- **`Θ(0) = 1` from the identity metric `g̃(0) = δ`.**  Variant sourcing the diagonal value from
    the RNC Kronecker condition `G 0 = (1 : Matrix …)` directly (via `Matrix.det_one`). -/
theorem vanVleck_zero_of_eq_one (G : Point n → Fin n → Fin n → ℝ)
    (hG0 : G 0 = (1 : Matrix (Fin n) (Fin n) ℝ)) : vanVleck G 0 = 1 :=
  vanVleck_zero G (by rw [hG0, Matrix.det_one])

/-- **`Θ(0) = 1` for the exp-pullback metric.**  Sourced from `expPullbackMetric_at_zero`
    (`g̃(0)_{ij} = g(p)_{ij}`) in a `p`-orthonormal frame (`hframe : g p = δ`), which gives the RNC
    Kronecker condition `g̃(0) = δ`, hence `det g̃(0) = 1` and `Θ(0) = 1`.  This is the honest
    instance of `vanVleck_zero` for the actual pullback metric `g̃ = exp_p^* g`. -/
theorem vanVleck_expPullback_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hframe : g p = (1 : Matrix (Fin n) (Fin n) ℝ)) :
    vanVleck (expPullbackMetric g gi hC p) 0 = 1 := by
  refine vanVleck_zero_of_eq_one _ ?_
  funext i j
  rw [expPullbackMetric_at_zero]
  exact congrFun (congrFun hframe i) j

/-! ### #3 — positivity `0 < Θ` -/

/-- **Positivity of the van-Vleck determinant** where `det g̃ > 0` (the pullback metric is
    positive-definite near `0`, so `det g̃ > 0` there — carried as `hdet`).  `√` of a positive is
    positive, and `⁻¹` preserves positivity. -/
theorem vanVleck_pos (G : Point n → Fin n → Fin n → ℝ) (v : Point n)
    (hdet : 0 < Matrix.det (G v)) : 0 < vanVleck G v := by
  simp only [vanVleck]
  exact inv_pos.mpr (Real.sqrt_pos.mpr hdet)

/-! ### #4 — smoothness of `Θ` -/

/-- **Smoothness of the van-Vleck determinant.**  Where the metric components are `C^∞`
    (`hg`, feeding `det_contDiff`) and `det g̃ > 0` at `v` (`hdet`), `Θ = (√ det g̃)⁻¹` is
    `ContDiffAt ℝ k` at `v` for every regularity `k`: `det g̃` is `C^∞` (`det_contDiff`), `√` is
    smooth away from `0` (`ContDiffAt.sqrt`, `det g̃ v ≠ 0`), and `⁻¹` is smooth away from `0`
    (`ContDiffAt.inv`, `√ det g̃ v ≠ 0`).  The positivity `hdet` is genuine and load-bearing (both
    `√` and `⁻¹` are singular at `0`). -/
theorem vanVleck_contDiffAt (G : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => G y a b)) (v : Point n)
    (hdet : 0 < Matrix.det (G v)) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (vanVleck G) v := by
  have hdetCDA : ContDiffAt ℝ k (fun y => Matrix.det (G y)) v :=
    ((det_contDiff G hg).of_le le_top).contDiffAt
  have hne : Matrix.det (G v) ≠ 0 := ne_of_gt hdet
  have hsqrtne : Real.sqrt (Matrix.det (G v)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdet)
  exact (hdetCDA.sqrt hne).inv hsqrtne

end QIQTH.VanVleck
