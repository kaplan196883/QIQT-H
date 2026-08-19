/-
  TerminalVelAtCubicRemainder — Plan v9 Task B (STEP 4a): the GENUINE quantitative CUBIC-REMAINDER
  (third-order Taylor) bound on the base-`x₀` terminal-velocity map `T_{x₀} := terminalVelAt`.

  ROLE.  `QIQTH.GeodesicReversalRouteAtPoint` (J4-858) built the generic-base reversal identity
      `U z x₀ =ᶠ[𝓝 x₀] − T_{x₀}(U x₀ z)`
  and proved `terminalVelAt_contDiffAt_two` (`C²` at `0`).  The `hcomp`-reversal-feasibility sympy
  gate (`docs/qg_roadmap/rnc_sympy/hcomp_reversal_feasibility.py`) established that the base↔eval swap
  becomes a `O(√ε)` CANCELLATION — rather than the log-divergent magnitude bound of the two ruled-out
  routes — PRECISELY WHEN `T_{x₀}` is a NEAR-IDENTITY whose deviation from the identity is genuinely
  CUBIC (a homogeneous quadratic second-order term plus an `O(‖v‖³)` remainder), so that the leading
  discrepancy of the EVEN van-Vleck Hessian scalar is an ODD `z`-moment that VANISHES, leaving only a
  genuine degree-4 even survivor at heat-time power `τ^{1/2}`.

  THIS FILE delivers exactly that near-identity CUBIC structure for the concrete `terminalVelAt`:
      `terminalVelAt x₀ v = v + (1/2)·B(v,v) + R(v)`,  `‖R(v)‖ ≤ C‖v‖³`  for `‖v‖ < r`,
  with `T_{x₀}(0) = 0`, `D T_{x₀}(0) = Id`, and `B := D²(terminalVelAt x₀)(0)` the SYMMETRIC Hessian
  (`∀ v w, B v w = B w v`, Clairaut).  The quadratic `(1/2)B(v,v)` is genuinely homogeneous of degree
  two, so its inner product with `v` is an odd degree-three form — exactly the parity the sympy gate
  needs.

  ── THE ROUTE.  One order higher than J4-857's `JointRNCRegularityInterfaceLocal` extraction (which read
     a SECOND-order `‖·‖²` displacement out of `C²`).  Here from `C³` (available for free from the same
     banked homogeneity route: `uniformFlowExp x₀` is `C⁴`, so `fderiv` is `C³`, so the diagonal
     `v ↦ fderiv(uniformFlowExp x₀) v [v] = terminalVelAt x₀` is `C³`), extract `F', F'', F'''`, bound
     `‖F'''‖ ≤ M` near `0` by continuity, and run THREE mean-value passes:
       (1) `‖F''(w) − F''(0)‖ ≤ M‖w‖`,
       (2) `‖F'(v) − Id − F''(0)(v)‖ ≤ M‖v‖²`,
       (3) `‖F(v) − v − (1/2)B(v,v)‖ ≤ M‖v‖³`,
     using `F(0)=0`, `F'(0)=Id`, and the Clairaut symmetry of `B := F''(0)` (which collapses the honest
     bilinear-diagonal derivative `(1/2)[B(·)(v)+B(v)(·)]` to `B(v)`).

  ⚠ HONESTY FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry` (prose only), no new
  axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  The only
  hypotheses are the standing geometry `(hC, hK)` plus `x₀ ∈ K`, all satisfiable at any concrete curved
  metric (`K := closedBall x₀ 1`, `x₀` arbitrary — genuinely curved, non-vacuous).  The bound is
  WINDOWED (`∀ v, ‖v‖ < r → …`, a bounded ball of radius `r`, NEVER a global `∀ v`).  `terminalVelAt` is
  a genuinely DIFFERENT function from the conclusion; the cubic remainder is a real third-order Taylor
  estimate, not a conclusion-in-disguise.  No existing file is edited.
-/
import Mathlib
import QIQTH.GeodesicReversalRouteAtPoint

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartThirdJet QIQTH.GeodesicReversalRoute QIQTH.TerminalVelC2 QIQTH.FrozenBaseWChain
open QIQTH.GeodesicReversalRouteAtPoint
open scoped Topology

namespace QIQTH.TerminalVelAtCubicRemainder

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### STEP 4a-0 — `terminalVelAt x₀` is `C³` at `0` (one order up from the banked `C²`). -/

/-- **`terminalVelAt x₀` is `C³` at `0`.**  Identical homogeneity route as `terminalVelAt_contDiffAt_two`
    (J4-858), but STOPPING at `C³` instead of downgrading to `C²`: the position endpoint
    `uniformFlowExp x₀` is `C⁴`, so `fderiv` is `C³`, and the diagonal evaluation
    `v ↦ fderiv(uniformFlowExp x₀) v [v] = terminalVelAt x₀` is `C³` (`ContDiffAt.clm_apply`).
    NOT `a₁ = R/6`. -/
theorem terminalVelAt_contDiffAt_three (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ContDiffAt ℝ 3 (terminalVelAt g gi hC hK x₀) 0 := by
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK x₀) 0 :=
    uniformFlowExp_contDiffAt_four g gi hC hK x₀ hx₀K 0
      (by simpa using expRho_pos g gi hC x₀)
      (by simpa using uniformFlowRadius_pos g gi hC hK)
  have hfd3 : ContDiffAt ℝ 3 (fderiv ℝ (uniformFlowExp g gi hC hK x₀)) 0 :=
    hcd4.fderiv_right (m := 3) (by norm_num)
  have hF3 : ContDiffAt ℝ 3
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) 0 :=
    hfd3.clm_apply contDiffAt_id
  have hEq : terminalVelAt g gi hC hK x₀
      =ᶠ[𝓝 (0 : Point n)] (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) := by
    have hball : Metric.ball (0 : Point n)
        (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK)) ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ (lt_min (expRho_pos g gi hC x₀) (uniformFlowRadius_pos g gi hC hK))
    filter_upwards [hball] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hvexp : ‖v‖ < expRho g gi hC x₀ := lt_of_lt_of_le hv (min_le_left _ _)
    have hvuf : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
    exact terminalVelAt_apply_eq_fderiv_diag g gi hC hK hx₀K v hvexp hvuf
  exact hF3.congr_of_eventuallyEq hEq

/-! ### STEP 4a-1 — `T_{x₀}(0) = 0`. -/

/-- **`terminalVelAt x₀ 0 = 0`.**  Via the diagonal identity at `v = 0`:
    `terminalVelAt x₀ 0 = fderiv(uniformFlowExp x₀) 0 [0] = 0`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_value_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    terminalVelAt g gi hC hK x₀ 0 = 0 := by
  have h := terminalVelAt_apply_eq_fderiv_diag g gi hC hK hx₀K 0
    (by simpa using expRho_pos g gi hC x₀)
    (by simpa using uniformFlowRadius_pos g gi hC hK)
  simpa [terminalVelAt] using h

/-! ### STEP 4a-2 — `D T_{x₀}(0) = Id`. -/

/-- **`fderiv (terminalVelAt x₀) 0 = Id`.**  `terminalVelAt x₀ =ᶠ[𝓝 0] (v ↦ fderiv(exp) v [v])`, whose
    Fréchet derivative at `0` is `(A 0).comp id + (DA 0).flip 0 = Id + 0 = Id`, since `A 0 = fderiv(exp) 0
    = Id` (`uniformFlowExp_fderiv_near_id_quant` at `v = 0`).  NOT `a₁ = R/6`. -/
theorem terminalVelAt_fderiv_id (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    fderiv ℝ (terminalVelAt g gi hC hK x₀) 0 = ContinuousLinearMap.id ℝ (Point n) := by
  set E := uniformFlowExp g gi hC hK x₀ with hEdef
  set A := fderiv ℝ E with hAdef
  -- `A 0 = Id`.
  have hA0 : A 0 = ContinuousLinearMap.id ℝ (Point n) := by
    obtain ⟨ρ₀, hρ₀, C_D, _, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
    have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀
    have hb := hnear x₀ hx₀K 0 h0ρ
    rw [norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  -- `E` is `C⁴` at `0`, so `A = fderiv E` is `C³` (hence differentiable) at `0`.
  have hcd4 : ContDiffAt ℝ 4 E 0 :=
    uniformFlowExp_contDiffAt_four g gi hC hK x₀ hx₀K 0
      (by simpa using expRho_pos g gi hC x₀)
      (by simpa using uniformFlowRadius_pos g gi hC hK)
  have hAc3 : ContDiffAt ℝ 3 A 0 := hcd4.fderiv_right (m := 3) (by norm_num)
  have hAfd : HasFDerivAt A (fderiv ℝ A 0) 0 :=
    (hAc3.differentiableAt (by norm_num)).hasFDerivAt
  -- the diagonal `g v = (A v)(v)` has `HasFDerivAt g Id 0`.
  have hclm : HasFDerivAt (fun v => (A v) v)
      ((A 0).comp (ContinuousLinearMap.id ℝ (Point n))
        + (fderiv ℝ A 0).flip ((fun v : Point n => v) 0)) 0 :=
    hAfd.clm_apply (hasFDerivAt_id 0)
  have hflip : (fderiv ℝ A 0).flip ((fun v : Point n => v) 0) = 0 := by
    simp
  have hderiv : (A 0).comp (ContinuousLinearMap.id ℝ (Point n))
      + (fderiv ℝ A 0).flip ((fun v : Point n => v) 0) = ContinuousLinearMap.id ℝ (Point n) := by
    rw [hflip, add_zero, hA0, ContinuousLinearMap.comp_id]
  rw [hderiv] at hclm
  -- transfer to `terminalVelAt` via eventual equality.
  have hEq : terminalVelAt g gi hC hK x₀
      =ᶠ[𝓝 (0 : Point n)] (fun v => (A v) v) := by
    have hball : Metric.ball (0 : Point n)
        (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK)) ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ (lt_min (expRho_pos g gi hC x₀) (uniformFlowRadius_pos g gi hC hK))
    filter_upwards [hball] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hvexp : ‖v‖ < expRho g gi hC x₀ := lt_of_lt_of_le hv (min_le_left _ _)
    have hvuf : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
    exact terminalVelAt_apply_eq_fderiv_diag g gi hC hK hx₀K v hvexp hvuf
  rw [hEq.fderiv_eq, hclm.fderiv]

/-! ### STEP 4a — the CUBIC-REMAINDER (third-order Taylor) bound. -/

/-- **★★ `terminalVelAt_cubic_remainder` — the near-identity CUBIC structure of `T_{x₀}`.**
    There are a radius `r > 0`, a finite constant `C ≥ 0`, and a SYMMETRIC Hessian bilinear map
    `B := D²(terminalVelAt x₀)(0)` such that, on the windowed ball `‖v‖ < r`,
        `terminalVelAt x₀ v = v + (1/2)·B(v,v) + R(v)`,  `‖R(v)‖ ≤ C‖v‖³`,
    with `terminalVelAt x₀ 0 = 0` and `D(terminalVelAt x₀)(0) = Id`.  This is the exact
    `T_{x₀}(v) = v + (curvature quadratic) + O(‖v‖³)` near-identity shape the `hcomp`-reversal
    feasibility gate requires (the quadratic `(1/2)B(v,v)` is homogeneous degree two, so its inner
    product with `v` is an odd degree-three form that vanishes in the `z`-moment; the surviving even part
    is genuine degree four).  Extracted by THREE mean-value passes from the `C³` regularity
    (`terminalVelAt_contDiffAt_three`), one order higher than J4-857.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_cubic_remainder (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ∃ (r C : ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] Point n),
      0 < r ∧ 0 ≤ C
      ∧ terminalVelAt g gi hC hK x₀ 0 = 0
      ∧ fderiv ℝ (terminalVelAt g gi hC hK x₀) 0 = ContinuousLinearMap.id ℝ (Point n)
      ∧ (∀ v w, B v w = B w v)
      ∧ ∀ v : Point n, ‖v‖ < r →
          ‖terminalVelAt g gi hC hK x₀ v - v - (1/2 : ℝ) • B v v‖ ≤ C * ‖v‖ ^ 3 := by
  classical
  set F := terminalVelAt g gi hC hK x₀ with hFdef
  have hF3 : ContDiffAt ℝ 3 F 0 := terminalVelAt_contDiffAt_three g gi hC hK hx₀K
  have hval : F 0 = 0 := terminalVelAt_value_zero g gi hC hK hx₀K
  have hFid : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ (Point n) :=
    terminalVelAt_fderiv_id g gi hC hK hx₀K
  -- extract F', F'', F''' as local derivative functions.
  obtain ⟨F', ⟨u, hu, hFderiv⟩, hF'c2⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (2 + 1 : ℕ) F 0 by exact_mod_cast hF3)
  obtain ⟨F'', ⟨u2, hu2, hF'deriv⟩, hF''c1⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (1 + 1 : ℕ) F' 0 by exact_mod_cast hF'c2)
  obtain ⟨F''', ⟨u3, hu3, hF''deriv⟩, hF'''c0⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (0 + 1 : ℕ) F'' 0 by exact_mod_cast hF''c1)
  -- `F' 0 = Id`.
  have hF'0 : F' 0 = ContinuousLinearMap.id ℝ (Point n) := by
    have h := (hFderiv 0 (mem_of_mem_nhds hu)).fderiv
    rw [← h]; exact hFid
  -- symmetry of `B := F'' 0` (Clairaut, local version).
  set B : Point n →L[ℝ] Point n →L[ℝ] Point n := F'' 0 with hBdef
  have hsymm : ∀ v w, B v w = B w v := by
    intro v w
    refine second_derivative_symmetric_of_eventually (f := F) (f' := F') (f'' := B)
      (x := (0 : Point n)) ?_ ?_ v w
    · filter_upwards [hu] with y hy using hFderiv y hy
    · exact hF'deriv 0 (mem_of_mem_nhds hu2)
  -- bound `M` on `F'''` near `0`.
  set M : ℝ := ‖F''' 0‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hbound_ev : ∀ᶠ z in 𝓝 (0 : Point n), ‖F''' z‖ ≤ M := by
    have hmem : Set.Iio M ∈ 𝓝 ‖F''' 0‖ := Iio_mem_nhds (by rw [hMdef]; linarith)
    have h := (hF'''c0.continuousAt.norm) hmem
    filter_upwards [h] with z hz
    exact le_of_lt hz
  -- gate ball `Metric.ball 0 r ⊆ u ∩ u2 ∩ u3 ∩ {‖F''' ·‖ ≤ M}`.
  have hset : u ∩ u2 ∩ u3 ∩ {z | ‖F''' z‖ ≤ M} ∈ 𝓝 (0 : Point n) :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hu hu2) hu3) hbound_ev
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hset
  have hz_u : ∀ z ∈ Metric.ball (0 : Point n) r, z ∈ u := fun z hz => (((hsub hz).1).1).1
  have hz_u2 : ∀ z ∈ Metric.ball (0 : Point n) r, z ∈ u2 := fun z hz => (((hsub hz).1).1).2
  have hz_u3 : ∀ z ∈ Metric.ball (0 : Point n) r, z ∈ u3 := fun z hz => ((hsub hz).1).2
  have hz_bd : ∀ z ∈ Metric.ball (0 : Point n) r, ‖F''' z‖ ≤ M := fun z hz => (hsub hz).2
  have h0ball : (0 : Point n) ∈ Metric.ball (0 : Point n) r := Metric.mem_ball_self hr0
  -- PASS 1: `‖F'' w − B‖ ≤ M‖w‖`.
  have hPass1 : ∀ w ∈ Metric.ball (0 : Point n) r, ‖F'' w - B‖ ≤ M * ‖w‖ := by
    intro w hw
    have hseg : segment ℝ (0 : Point n) w ⊆ Metric.ball (0 : Point n) r :=
      (convex_ball (0 : Point n) r).segment_subset h0ball hw
    have hderiv : ∀ y ∈ segment ℝ (0 : Point n) w,
        HasFDerivWithinAt F'' (F''' y) (segment ℝ (0 : Point n) w) y :=
      fun y hy => (hF''deriv y (hz_u3 y (hseg hy))).hasFDerivWithinAt
    have hbd : ∀ y ∈ segment ℝ (0 : Point n) w, ‖F''' y‖ ≤ M :=
      fun y hy => hz_bd y (hseg hy)
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbd
      (convex_segment (0 : Point n) w) (left_mem_segment ℝ (0 : Point n) w)
      (right_mem_segment ℝ (0 : Point n) w)
    rw [← hBdef] at hmv
    simpa using hmv
  -- PASS 2: `‖F' v − Id − B(v)‖ ≤ M‖v‖²`.  (`B(v)` is the CLM `w ↦ B v w`.)
  have hPass2 : ∀ v ∈ Metric.ball (0 : Point n) r,
      ‖F' v - ContinuousLinearMap.id ℝ (Point n) - B v‖ ≤ M * ‖v‖ ^ 2 := by
    intro v hv
    set G : Point n → (Point n →L[ℝ] Point n) :=
      fun w => F' w - ContinuousLinearMap.id ℝ (Point n) - B w with hGdef
    have hseg : segment ℝ (0 : Point n) v ⊆ Metric.ball (0 : Point n) r :=
      (convex_ball (0 : Point n) r).segment_subset h0ball hv
    have hseg_cb : segment ℝ (0 : Point n) v ⊆ Metric.closedBall (0 : Point n) ‖v‖ :=
      (convex_closedBall (0 : Point n) ‖v‖).segment_subset
        (by simp) (by rw [Metric.mem_closedBall, dist_zero_right])
    -- `G` has derivative `F'' w − B` on the segment.
    have hGderiv : ∀ w ∈ segment ℝ (0 : Point n) v,
        HasFDerivWithinAt G (F'' w - B) (segment ℝ (0 : Point n) v) w := by
      intro w hw
      have h1 : HasFDerivAt F' (F'' w) w := hF'deriv w (hz_u2 w (hseg hw))
      have h2 : HasFDerivAt (fun _ : Point n => ContinuousLinearMap.id ℝ (Point n))
          (0 : Point n →L[ℝ] (Point n →L[ℝ] Point n)) w := hasFDerivAt_const _ _
      have h3 : HasFDerivAt (fun w : Point n => B w) B w := B.hasFDerivAt
      have := (h1.sub h2).sub h3
      simpa using this.hasFDerivWithinAt
    have hGbd : ∀ w ∈ segment ℝ (0 : Point n) v, ‖F'' w - B‖ ≤ M * ‖v‖ := by
      intro w hw
      have hwr : ‖w‖ ≤ ‖v‖ := by
        have := hseg_cb hw; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
      exact le_trans (hPass1 w (hseg hw)) (mul_le_mul_of_nonneg_left hwr hM0)
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hGderiv hGbd
      (convex_segment (0 : Point n) v) (left_mem_segment ℝ (0 : Point n) v)
      (right_mem_segment ℝ (0 : Point n) v)
    -- `G 0 = 0`.
    have hG0 : G 0 = 0 := by
      rw [hGdef]; simp only [map_zero, sub_zero]; rw [hF'0, sub_self]
    rw [hG0] at hmv
    simp only [sub_zero] at hmv
    calc ‖F' v - ContinuousLinearMap.id ℝ (Point n) - B v‖
        = ‖G v‖ := by rw [hGdef]
      _ ≤ M * ‖v‖ * ‖v‖ := hmv
      _ = M * ‖v‖ ^ 2 := by ring
  -- The honest derivative of the quadratic `Q v = (1/2)·(B v) v` collapses to `B v` via symmetry.
  have hQderiv : ∀ v : Point n,
      HasFDerivAt (fun w : Point n => (1/2 : ℝ) • ((B w) w)) (B v) v := by
    intro v
    -- diagonal derivative of `w ↦ (B w) w` is `(B v).comp id + B.flip (v)`.
    have hclm : HasFDerivAt (fun w : Point n => (B w) w)
        ((B v).comp (ContinuousLinearMap.id ℝ (Point n)) + B.flip v) v :=
      B.hasFDerivAt.clm_apply (hasFDerivAt_id v)
    have hsmul := hclm.const_smul (1/2 : ℝ)
    -- `(1/2)•[(B v) + B.flip v] = B v` by symmetry (`B.flip v = B v`).
    have hflip_eq : B.flip v = B v := by
      refine ContinuousLinearMap.ext (fun w => ?_)
      rw [ContinuousLinearMap.flip_apply, hsymm w v]
    have hcollapse : (1/2 : ℝ) • ((B v).comp (ContinuousLinearMap.id ℝ (Point n)) + B.flip v)
        = B v := by
      rw [ContinuousLinearMap.comp_id, hflip_eq, ← two_smul ℝ (B v), smul_smul,
        show (1/2 * 2 : ℝ) = 1 by norm_num, one_smul]
    rw [hcollapse] at hsmul
    exact hsmul
  -- PASS 3: `‖F v − v − (1/2)B(v,v)‖ ≤ M‖v‖³`.
  refine ⟨r, M, B, hr0, hM0, hval, hFid, hsymm, ?_⟩
  intro v hv
  have hvball : v ∈ Metric.ball (0 : Point n) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv
  set R : Point n → Point n :=
    fun w => F w - w - (1/2 : ℝ) • ((B w) w) with hRdef
  have hseg : segment ℝ (0 : Point n) v ⊆ Metric.ball (0 : Point n) r :=
    (convex_ball (0 : Point n) r).segment_subset h0ball hvball
  have hseg_cb : segment ℝ (0 : Point n) v ⊆ Metric.closedBall (0 : Point n) ‖v‖ :=
    (convex_closedBall (0 : Point n) ‖v‖).segment_subset
      (by simp) (by rw [Metric.mem_closedBall, dist_zero_right])
  -- `R` has derivative `F' w − Id − B w` on the segment.
  have hRderiv : ∀ w ∈ segment ℝ (0 : Point n) v,
      HasFDerivWithinAt R (F' w - ContinuousLinearMap.id ℝ (Point n) - B w)
        (segment ℝ (0 : Point n) v) w := by
    intro w hw
    have h1 : HasFDerivAt F (F' w) w := hFderiv w (hz_u w (hseg hw))
    have h2 : HasFDerivAt (fun w : Point n => w) (ContinuousLinearMap.id ℝ (Point n)) w :=
      hasFDerivAt_id w
    have h3 : HasFDerivAt (fun w : Point n => (1/2 : ℝ) • ((B w) w)) (B w) w := hQderiv w
    have := (h1.sub h2).sub h3
    exact this.hasFDerivWithinAt
  have hRbd : ∀ w ∈ segment ℝ (0 : Point n) v,
      ‖F' w - ContinuousLinearMap.id ℝ (Point n) - B w‖ ≤ M * ‖v‖ ^ 2 := by
    intro w hw
    have hwr : ‖w‖ ≤ ‖v‖ := by
      have := hseg_cb hw; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
    calc ‖F' w - ContinuousLinearMap.id ℝ (Point n) - B w‖
        ≤ M * ‖w‖ ^ 2 := hPass2 w (hseg hw)
      _ ≤ M * ‖v‖ ^ 2 := by gcongr
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hRderiv hRbd
    (convex_segment (0 : Point n) v) (left_mem_segment ℝ (0 : Point n) v)
    (right_mem_segment ℝ (0 : Point n) v)
  -- `R 0 = 0`.
  have hR0 : R 0 = 0 := by
    simp only [hRdef, map_zero, smul_zero, sub_zero, hval]
  rw [hR0] at hmv
  simp only [sub_zero] at hmv
  calc ‖F v - v - (1/2 : ℝ) • (B v) v‖
      = ‖R v‖ := by rw [hRdef]
    _ ≤ M * ‖v‖ ^ 2 * ‖v‖ := hmv
    _ = M * ‖v‖ ^ 3 := by ring

end QIQTH.TerminalVelAtCubicRemainder

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.TerminalVelAtCubicRemainder
#print axioms terminalVelAt_contDiffAt_three
#print axioms terminalVelAt_value_zero
#print axioms terminalVelAt_fderiv_id
#print axioms terminalVelAt_cubic_remainder
end AxiomChecks
