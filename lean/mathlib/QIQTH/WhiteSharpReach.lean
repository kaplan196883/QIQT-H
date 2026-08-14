/-
  WhiteSharpReach — J4-722: THE SHARP REACH LEMMA (the c-shrinking-constant reach).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` stays a
  labelled carrier, untouched).  It supplies the LAST exhibitable member of the `final8` joint witness
  (J4-721): the sharp reach `closedBall 0 R ⊆ flowExpₓ_0 '' ball 0 c` with `R > c/2` for small `c`.

  ── THE cp466 COUPLING (recap of J4-721).  The value supplier `white_witness_value_dom_at_radius`
  HARDCODES the collar `a = c/4`, `b = c/2`; then the reach side-condition `hbR : b·(1+C_D·c) < R`
  forces `R > c/2` (`white_final8_forcedCollar_reach_gt`).  The only banked reach machinery — the CRUDE
  `uniformFlowExp_approximatesLinearOn` (FIXED constant `c_lin = C_D·δ₀ < 1`) via `surjOn_closedBall` —
  delivers only `R ≤ (1 − c_lin)·(c/2) < c/2`.  So the reach was carried honestly.

  ── THE FIX.  The flow-exp is a PERTURBATION OF THE IDENTITY with a Jacobian near-identity bound that
  SHRINKS with the ball radius: `‖Dφ_q(v) − Id‖ ≤ C_L·‖v‖` (`uniformFlowExp_fderiv_near_id_quant`).  So
  on `ball 0 c` the mean-value inequality gives `ApproximatesLinearOn φ_q id (ball 0 c) (C_L·c)` with a
  constant `C_L·c → 0` as `c → 0` — the RADIUS-PARAMETRIC (shrinking) constant, not the fixed one.  Then
  `surjOn_closedBall_of_nonlinearRightInverse` at `b = 0`, `ε = 3c/4` gives
      `closedBall (φ_q 0) ((1 − C_L·c)·(3c/4)) ⊆ φ_q '' ball 0 c`.
  At `q = 0` (`φ_0 0 = 0`) this is `closedBall 0 R ⊆ φ_0 '' ball 0 c` with `R = (1 − C_L·c)·(3c/4)`.

  ── THE SMALL-`c` WINDOW (sympy-checked).  With the value-forced collar `b = c/2` and the sharp reach
  `R = (1 − C_L·c)·(3c/4)`, the reach side-condition `b·(1 + C_D·c) < R` reads
      `(c/2)(1 + C_D·c) < (3c/4)(1 − C_L·c)`  ⟺  `2·C_D·c + 3·C_L·c < 1`,
  satisfiable for every small `c` (`C_D` = displacement const, `C_L` = near-identity Jacobian const).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `uniformFlowExp_approximatesLinearOn_sharp` — ★★ the c-shrinking-constant ApproximatesLinearOn
      `φ_q id (ball 0 c) (C_L·c)`, uniform over `K`, for every `0 < c ≤ ρ₀`.
    * `uniformFlowExp_sharp_reach` — ★★ the sharp reach `closedBall (φ_q 0) ((1−C_L·c)·(3c/4)) ⊆
      φ_q '' ball 0 c` (subsingleton branch handled directly; nontrivial branch via `surjOn`).
    * `sharp_reach_window_arith` — the PROVED small-`c` arithmetic `2C_D c + 3C_L c < 1 ⟹
      (c/2)(1+C_D c) < (1−C_L c)(3c/4)` (the `hbR` discharge).
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.UniformChartRadius
import QIQTH.NearIsometryBudget

open MeasureTheory Filter Set Metric
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open scoped Topology NNReal BigOperators

namespace QIQTH.WhiteSharpReach

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1 — ★★ the c-shrinking-constant ApproximatesLinearOn. -/

/-- **★★ `uniformFlowExp_approximatesLinearOn_sharp`.**  The SHARP (radius-parametric) linear
    approximation.  There is a single radius `ρ₀ > 0` and constant `C_L ≥ 0` (both uniform over `K`)
    such that for every `q ∈ K` and every `0 < c ≤ ρ₀`, the recentring chart `φ_q` approximates the
    identity on `ball 0 c` with the SHRINKING constant `C_L·c`:
        `∀ x y ∈ ball 0 c, ‖φ_q x − φ_q y − (x − y)‖ ≤ (C_L·c)·‖x − y‖`.
    Route: the K-uniform near-identity Jacobian bound `‖Dφ_q(w) − Id‖ ≤ C_L·‖w‖` gives, on `ball 0 c`,
    `‖D(φ_q − id)(w)‖ ≤ C_L·‖w‖ ≤ C_L·c`; the mean value inequality integrates this.  UNLIKE the crude
    banked version, the constant `C_L·c → 0` as `c → 0`.  Hypotheses ONLY `hC` + `IsCompact K`.
    ⚠ NOT `a₁ = R/6`. -/
theorem uniformFlowExp_approximatesLinearOn_sharp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ q ∈ K, ∀ c : ℝ, 0 < c → c ≤ ρ₀ →
      ApproximatesLinearOn (uniformFlowExp g gi hC hK q)
        (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)
        (Metric.ball 0 c) (C_L * c).toNNReal := by
  obtain ⟨ρ₀near, hρ₀near, C_L, hCL0, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min ρ₀near (uniformFlowRadius g gi hC hK), lt_min hρ₀near hRpos, C_L, hCL0, ?_⟩
  intro q hq c hc hcρ
  have hcnear : c ≤ ρ₀near := le_trans hcρ (min_le_left _ _)
  have hcR : c ≤ uniformFlowRadius g gi hC hK := le_trans hcρ (min_le_right _ _)
  intro x hx y hy
  rw [mem_ball_zero_iff] at hx hy
  set f : Point n → Point n := fun w => uniformFlowExp g gi hC hK q w - w with hfdef
  have hdiff : ∀ w ∈ Metric.ball (0 : Point n) c, DifferentiableAt ℝ f w := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    have hφ : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q) w :=
      (contDiffAt2_uniformFlowExp g gi hC hK q hq w (lt_of_lt_of_le hw hcR)).differentiableAt
        (by norm_num)
    exact hφ.sub differentiableAt_id
  have hbound : ∀ w ∈ Metric.ball (0 : Point n) c, ‖fderiv ℝ f w‖ ≤ C_L * c := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    have hφ : DifferentiableAt ℝ (uniformFlowExp g gi hC hK q) w :=
      (contDiffAt2_uniformFlowExp g gi hC hK q hq w (lt_of_lt_of_le hw hcR)).differentiableAt
        (by norm_num)
    have hfd : fderiv ℝ f w
        = fderiv ℝ (uniformFlowExp g gi hC hK q) w - ContinuousLinearMap.id ℝ (Point n) := by
      rw [hfdef, fderiv_fun_sub hφ differentiableAt_fun_id, fderiv_fun_id]
    rw [hfd]
    calc ‖fderiv ℝ (uniformFlowExp g gi hC hK q) w - ContinuousLinearMap.id ℝ (Point n)‖
        ≤ C_L * ‖w‖ := hnear q hq w (lt_of_lt_of_le hw hcnear)
      _ ≤ C_L * c := by apply mul_le_mul_of_nonneg_left hw.le hCL0
  have hmvt := (convex_ball (0 : Point n) c).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (mem_ball_zero_iff.mpr hy) (mem_ball_zero_iff.mpr hx)
  have hfxy : uniformFlowExp g gi hC hK q x - uniformFlowExp g gi hC hK q y - (x - y)
      = f x - f y := by simp only [hfdef]; exact sub_sub_sub_comm _ _ _ _
  have hidapp : (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n) (x - y) = x - y := by
    simp
  rw [hidapp, hfxy, Real.coe_toNNReal (C_L * c) (mul_nonneg hCL0 hc.le)]
  exact hmvt

/-! ### §2 — the small-`c` window arithmetic (the `hbR` discharge). -/

/-- **`sharp_reach_window_arith`.**  With the value-forced collar `b = c/2` and the sharp reach
    `R = (1 − C_L·c)·(3c/4)`, the reach side-condition `b·(1 + C_D·c) < R` is EQUIVALENT to
    `2·C_D·c + 3·C_L·c < 1`.  Direction used: the small-`c` hypothesis `⟹ hbR`.  ⚠ NOT `a₁ = R/6`. -/
theorem sharp_reach_window_arith (c C_D C_L : ℝ) (hc : 0 < c)
    (hwin : 2 * C_D * c + 3 * C_L * c < 1) :
    (c / 2) * (1 + C_D * c) < (1 - C_L * c) * (3 * c / 4) := by
  nlinarith [hwin, hc, mul_pos hc hc]

/-! ### §3 — ★★ the sharp reach. -/

/-- **★★ `uniformFlowExp_sharp_reach`.**  The SHARP reach.  There is `ρ₀ > 0` and `C_L ≥ 0` such that
    for every `q ∈ K` and `0 < c ≤ ρ₀`,
        `closedBall (φ_q 0) ((1 − C_L·c)·(3c/4)) ⊆ φ_q '' ball 0 c`.
    Route: the sharp ApproximatesLinearOn (§1, shrinking constant `C_L·c`) plus
    `surjOn_closedBall_of_nonlinearRightInverse` (root of the identity approximant, `fri.nnnorm = 1`) at
    the sub-radius `ε = 3c/4 < c`.  Subsingleton spaces are handled directly.  ⚠ NOT `a₁ = R/6`. -/
theorem uniformFlowExp_sharp_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ q ∈ K, ∀ c : ℝ, 0 < c → c ≤ ρ₀ →
      Metric.closedBall (uniformFlowExp g gi hC hK q 0) ((1 - C_L * c) * (3 * c / 4))
        ⊆ uniformFlowExp g gi hC hK q '' Metric.ball 0 c := by
  classical
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hAL⟩ := uniformFlowExp_approximatesLinearOn_sharp g gi hC hK
  refine ⟨ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro q hq c hc hcρ
  rcases subsingleton_or_nontrivial (Point n) with hsub | hns
  · -- subsingleton: the whole space is `{0}`; `φ_q 0 = φ_q applied to 0 ∈ ball 0 c`.
    intro y _
    exact ⟨0, by rw [mem_ball_zero_iff, @Subsingleton.elim _ hsub 0 0, norm_zero]; exact hc,
      @Subsingleton.elim _ hsub _ _⟩
  · haveI := hns
    have hALq := hAL q hq c hc hcρ
    set fri := (ContinuousLinearEquiv.refl ℝ (Point n)).toNonlinearRightInverse with hfri
    have hnn : ((fri.nnnorm : ℝ)) = 1 := by
      have h1 : fri.nnnorm
          = ‖((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)‖₊ := rfl
      have h2 : ((ContinuousLinearEquiv.refl ℝ (Point n)).symm : Point n →L[ℝ] Point n)
          = ContinuousLinearMap.id ℝ (Point n) := by ext x; simp
      have h3 : ‖ContinuousLinearMap.id ℝ (Point n)‖₊ = 1 := by simp
      rw [h1, h2, h3]; norm_num
    have hε0 : (0 : ℝ) ≤ 3 * c / 4 := by linarith
    have hεsub : Metric.closedBall (0 : Point n) (3 * c / 4) ⊆ Metric.ball 0 c := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      calc ‖x‖ ≤ 3 * c / 4 := hx
        _ < c := by linarith
    have hsurj := hALq.surjOn_closedBall_of_nonlinearRightInverse fri hε0 hεsub
    -- the surjOn radius equals `(1 − C_L·c)·(3c/4)`.
    have hradeq : ((fri.nnnorm : ℝ)⁻¹ - ((C_L * c).toNNReal : ℝ)) * (3 * c / 4)
        = (1 - C_L * c) * (3 * c / 4) := by
      rw [hnn, inv_one, Real.coe_toNNReal (C_L * c) (mul_nonneg hCL0 hc.le)]
    -- chase the inclusions.
    have hmono : uniformFlowExp g gi hC hK q '' Metric.closedBall 0 (3 * c / 4)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.ball 0 c := Set.image_mono hεsub
    intro y hy
    rw [hradeq] at hsurj
    exact hmono (hsurj hy)

end QIQTH.WhiteSharpReach

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteSharpReach
#check @uniformFlowExp_approximatesLinearOn_sharp
#check @uniformFlowExp_sharp_reach
#print axioms uniformFlowExp_approximatesLinearOn_sharp
#print axioms uniformFlowExp_sharp_reach
#print axioms sharp_reach_window_arith
end AxiomChecks
