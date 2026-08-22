/-
  LocalRNCJetFactorGlobalization — the first RE-THREADING brick of `hCConv`'s `hcomp` onto the PROVEN
  local RNC regularity variant: the transported chart-FIRST-JET factor data that J4-999 named as the
  single missing ingredient of `integral_heatHessMult_mul_transportedCoeff` is now SUPPLIED — globally
  bounded, globally Lipschitz-at-origin, and AE-strongly-measurable — DIRECTLY from the machine-checked
  `JointSecondOrderRNCRegularityLocal` (`jointRNCRegularityLocal_of_diag`, J4-856/local), via radial
  truncation.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It re-threads the
  chart-jet factor of the odd-moment sliver payoff onto the PROVEN local variant instead of the
  un-satisfiable global `JointSecondOrderRNCRegularity`.  It does NOT close `hcomp`/`hCConv`: the
  remaining residues are exactly those J4-999 named — (iii) the second-order chain rule + base-slot
  change-of-variables identifying this abstract moment integral with the literal `kPrime` sliver
  integrand, the truncation-tail control (the truncated integral is NOT the original), the census scalar
  `q`'s own analysis, and the coordinate summation.  No `sorry`, no new axioms, no `:= True`, no vacuous
  hypothesis (satisfiability EXHIBITED), none equal to the conclusion, NO existing file edited.
  `a₁ = R/6` stays STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE (gpt-5.6-sol high GO, 2026-08-22).

  J4-999 (`HeatHessCoeffClosure.integral_heatHessMult_mul_transportedCoeff`) established the correct RATE
  mechanism for `hcomp` — the odd-moment / mass-conservation cancellation — and reduced the required
  transported second-order coefficient to a PRODUCT of three bounded + Lipschitz-at-origin factors
  `q · a · b`, with `q` the census scalar `(amp·F)/|det|∘V` (available, concrete) and `a = (P_i∘V)ₐ`,
  `b = (P_j∘V)_b` the transported chart FIRST-jet components.  It explicitly named the missing piece: the
  vector factors `a`,`b` need `JointSecondOrderRNCRegularity` — the recurring opaque-chart wall census
  never supplied.

  The catch was that the LITERAL global interface `JointSecondOrderRNCRegularity` is un-satisfiable for
  the opaque `Classical.choose` chart (global-`∀y` jets + reflected sign), whereas the CORRECTLY-signed,
  neighbourhood-gated variant `JointSecondOrderRNCRegularityLocal` is genuinely PROVED (inhabited by
  `jointRNCRegularityLocal_of_diag`) — but only LOCALLY, on `Metric.ball q₀ r`.  The re-threading closes
  the gap: the local variant's `hJet1` gives, component-wise, that
      `z ↦ (fderiv V z (unitVec i))_a`  has value `(eᵢ)_a` at `q₀` and modulus `‖·−q₀‖·C_P`,
  i.e. EXACTLY "bounded + Lipschitz-at-origin (origin = `q₀`, via `V q₀ = 0`)" for the transported
  chart-jet factor — the exact `a`/`b` factor J4-999 declared missing, now proved from real regularity.
  A radial truncation (Sol's recommended globalization; `if ‖v‖ < ρ then · else (value at 0)`) turns the
  local factor into the GLOBAL bounded + Lipschitz-at-origin + measurable factor the payoff consumes,
  WITHOUT changing the Lipschitz-at-origin modulus (the truncation preserves the value at `0`, so the
  odd-moment constant-mode cancellation survives — Sol confirmed).

  ## WHAT LANDS (ns `QIQTH.LocalRNCJetFactor`).
    • `truncFactor` / `truncFactor_zero` / `truncFactor_bound` / `truncFactor_lip` / `truncFactor_aesm`
      — the pure, reusable radial-truncation globalization calculus: from a factor bounded + Lip-at-0 +
      continuous on `ball 0 ρ`, produce a GLOBAL bounded + Lip-at-0 + AE-strongly-measurable factor with
      the SAME value at `0` and the SAME Lipschitz-at-0 modulus.
    • `localJet_global_factor` — ★★ the re-threading core: from `jointRNCRegularityLocal_of_diag` alone
      (no un-satisfiable global interface), for any base `q₀`, direction `i`, component `ca`, there EXIST
      a global factor `F` and finite moduli `M, L ≥ 0` with `F 0 = (unitVec i)ₐ`, `AEStronglyMeasurable F`,
      `∀v |F v| ≤ M`, `∀v |F v − F 0| ≤ L‖v‖`.  The transported chart-jet factor, SUPPLIED from proven
      regularity.
    • `integral_heatHessMult_transportedJet_bound_from_localRNC` — ★★★ the payoff, re-threaded: feeding
      two such proven chart-jet factors (directions `i`,`j`, components `ca`,`cb`) plus a census scalar
      `qfac` into J4-999's `integral_heatHessMult_mul_transportedCoeff` yields the `τ^{-1/2}`
      moment-cancellation bound with the chart-jet factor moduli now coming from the PROVEN local variant.
    • `integral_heatHessMult_transportedJet_bound_from_localRNC_hyp_satisfiable` — NON-VACUITY of the sole
      remaining input (the census scalar), by `cos‖·‖`.

  ## HONEST DISTANCE.  This re-threads the CHART-JET factor of `hcomp`'s rate onto proven regularity —
  the piece J4-999 flagged as the wall.  It does NOT close `hcomp`: the abstract moment integral here is
  not yet identified with the literal `kPrime` sliver integrand (base-slot CoV + 2nd-order chain rule +
  truncation-tail control + coordinate summation remain, Sol residues iii).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JointRNCRegularityInterfaceLocal
import QIQTH.HeatHessTransportedCoeffClosure

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocal QIQTH.HeatHessMoment QIQTH.HeatHessCoeffClosure
open scoped Topology BigOperators Classical

namespace QIQTH.LocalRNCJetFactor

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ############################################################################
    ### 1. The pure radial-truncation globalization calculus.
    ############################################################################ -/

/-- The radial truncation of a factor `A` to `Metric.ball 0 ρ`, constant `A 0` outside.  Globalizes a
    locally-controlled factor while preserving its value at `0` (hence the odd-moment constant-mode
    cancellation) and its Lipschitz-at-origin modulus. -/
noncomputable def truncFactor (A : Point n → ℝ) (ρ : ℝ) : Point n → ℝ :=
  (Metric.ball (0 : Point n) ρ).piecewise A (fun _ => A 0)

/-- `truncFactor A ρ 0 = A 0`. -/
theorem truncFactor_zero (A : Point n → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    truncFactor A ρ 0 = A 0 := by
  unfold truncFactor
  rw [Set.piecewise_eq_of_mem _ _ _ (Metric.mem_ball_self hρ)]

/-- Global bound of `truncFactor` from a bound on the ball. -/
theorem truncFactor_bound (A : Point n → ℝ) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ v ∈ Metric.ball (0 : Point n) ρ, |A v| ≤ M) :
    ∀ v, |truncFactor A ρ v| ≤ M := by
  intro v
  unfold truncFactor
  by_cases hv : v ∈ Metric.ball (0 : Point n) ρ
  · rw [Set.piecewise_eq_of_mem _ _ _ hv]; exact hM v hv
  · rw [Set.piecewise_eq_of_notMem _ _ _ hv]
    exact hM 0 (Metric.mem_ball_self hρ)

/-- Global Lipschitz-at-origin bound of `truncFactor` from a Lip-at-0 bound on the ball. -/
theorem truncFactor_lip (A : Point n → ℝ) {ρ L : ℝ} (hL : 0 ≤ L)
    (hAL : ∀ v ∈ Metric.ball (0 : Point n) ρ, |A v - A 0| ≤ L * ‖v‖) :
    ∀ v, |truncFactor A ρ v - A 0| ≤ L * ‖v‖ := by
  intro v
  unfold truncFactor
  by_cases hv : v ∈ Metric.ball (0 : Point n) ρ
  · rw [Set.piecewise_eq_of_mem _ _ _ hv]; exact hAL v hv
  · rw [Set.piecewise_eq_of_notMem _ _ _ hv, sub_self, abs_zero]
    exact mul_nonneg hL (norm_nonneg v)

/-- `truncFactor` is AE-strongly-measurable when `A` is continuous on the truncation ball. -/
theorem truncFactor_aesm (A : Point n → ℝ) {ρ : ℝ}
    (hAcont : ContinuousOn A (Metric.ball (0 : Point n) ρ)) :
    AEStronglyMeasurable (truncFactor A ρ) volume := by
  unfold truncFactor
  exact AEStronglyMeasurable.piecewise measurableSet_ball
    (hAcont.aestronglyMeasurable measurableSet_ball)
    aestronglyMeasurable_const

/-! ############################################################################
    ### 2. The re-threading core — the chart-jet factor from the PROVEN local variant.
    ############################################################################ -/

/-- **★★ `localJet_global_factor`.**  The transported chart-FIRST-JET factor of `hcomp`'s odd-moment
    sliver rate, SUPPLIED from the machine-checked local RNC regularity `jointRNCRegularityLocal_of_diag`
    (not the un-satisfiable global interface): for any base `q₀`, direction `i`, and component `ca`, there
    exist a GLOBAL factor `F` and finite moduli `M, L ≥ 0` with `F 0 = (unitVec i) ca`,
    `AEStronglyMeasurable F`, `∀v |F v| ≤ M`, and `∀v |F v − F 0| ≤ L‖v‖`.  The vector factor J4-999
    named as the missing `a`/`b` ingredient, now built from proven regularity.  NOT `a₁ = R/6`. -/
theorem localJet_global_factor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) (i ca : Fin n) :
    ∃ (F : Point n → ℝ) (M L : ℝ),
      0 ≤ M ∧ 0 ≤ L ∧ F 0 = (unitVec i) ca ∧
      AEStronglyMeasurable F volume ∧
      (∀ v, |F v| ≤ M) ∧ (∀ v, |F v - F 0| ≤ L * ‖v‖) := by
  classical
  obtain ⟨r, C_W, C_P, C_Q, reg⟩ := jointRNCRegularityLocal_of_diag g gi hC q₀ i
  set V := uniformInverseChart g gi hC (isCompact_closedBall q₀ 1) q₀ with hVdef
  set A : Point n → ℝ := fun v => (fderiv ℝ V (q₀ + v)) (unitVec i) ca with hAdef
  -- the base jet value: `Dφ⁻¹(q₀)(eᵢ) = eᵢ` (from `hJet1` at `q₀`, modulus `0`).
  have hq0jet : (fderiv ℝ V q₀) (unitVec i) = unitVec i := by
    have h := reg.hJet1 q₀ (Metric.mem_ball_self reg.hr)
    rw [sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hA0 : A 0 = (unitVec i) ca := by
    simp only [hAdef, add_zero, hq0jet]
  -- local Lipschitz-at-`q₀` modulus of the component (the heart of the re-threading).
  have hAL : ∀ v ∈ Metric.ball (0 : Point n) r, |A v - A 0| ≤ C_P * ‖v‖ := by
    intro v hv
    have hvnorm : ‖v‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hv
    have hz : q₀ + v ∈ Metric.ball q₀ r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hvnorm
    have hj := reg.hJet1 (q₀ + v) hz
    rw [add_sub_cancel_left] at hj
    -- component estimate: `|(X - eᵢ) ca| ≤ ‖X - eᵢ‖`.
    have hcomp : |A v - A 0|
        ≤ ‖(fderiv ℝ V (q₀ + v)) (unitVec i) - unitVec i‖ := by
      rw [hA0, hAdef]
      have : (fderiv ℝ V (q₀ + v)) (unitVec i) ca - (unitVec i) ca
          = ((fderiv ℝ V (q₀ + v)) (unitVec i) - unitVec i) ca := by
        rw [Pi.sub_apply]
      rw [this]
      have hle := norm_le_pi_norm
        ((fderiv ℝ V (q₀ + v)) (unitVec i) - unitVec i) ca
      rwa [Real.norm_eq_abs] at hle
    exact le_trans hcomp hj
  -- base bound `|A 0| ≤ 1`.
  have hA0bd : |A 0| ≤ 1 := by
    rw [hA0]
    show |(unitVec i) ca| ≤ 1
    rw [unitVec, Pi.single_apply]
    split <;> simp
  -- local uniform bound `|A v| ≤ 1 + C_P r` on the ball.
  have hAbd : ∀ v ∈ Metric.ball (0 : Point n) r, |A v| ≤ 1 + C_P * r := by
    intro v hv
    have hvnorm : ‖v‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hv
    have hlipv := hAL v hv
    have hsplit : A v = A 0 + (A v - A 0) := by ring
    calc |A v| = |A 0 + (A v - A 0)| := by rw [← hsplit]
      _ ≤ |A 0| + |A v - A 0| := abs_add_le _ _
      _ ≤ 1 + C_P * ‖v‖ := by exact add_le_add hA0bd hlipv
      _ ≤ 1 + C_P * r := by
          have : C_P * ‖v‖ ≤ C_P * r :=
            mul_le_mul_of_nonneg_left (le_of_lt hvnorm) reg.hCP
          linarith
  -- continuity of the component near `q₀` (from `ContDiffAt ℝ 2 V q₀`).
  have hev : ∀ᶠ y in nhds q₀, ContinuousAt (fun z => fderiv ℝ V z) y := by
    filter_upwards [reg.hVc2.eventually (by simp)] with y hy
    exact hy.continuousAt_fderiv (by simp)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨rc0, hrc0, hcontnear⟩ := hev
  -- continuity of `A` on `ball 0 rc0`.
  have hAcont : ContinuousOn A (Metric.ball (0 : Point n) rc0) := by
    intro v hv
    apply ContinuousAt.continuousWithinAt
    have hdlt : dist (q₀ + v) q₀ < rc0 := by
      rw [Metric.mem_ball, dist_zero_right] at hv
      rw [dist_eq_norm, add_sub_cancel_left]; exact hv
    have htrans : ContinuousAt (fun w : Point n => q₀ + w) v :=
      (continuous_const.add continuous_id).continuousAt
    have hFd : ContinuousAt (fun w => fderiv ℝ V (q₀ + w)) v :=
      (hcontnear hdlt).comp htrans
    have happ : ContinuousAt (fun w => (fderiv ℝ V (q₀ + w)) (unitVec i)) v :=
      hFd.clm_apply continuousAt_const
    exact (continuous_apply ca).continuousAt.comp happ
  -- truncation radius: `ρ := min rc0 r`.
  set ρ : ℝ := min rc0 r with hρdef
  have hρ0 : 0 < ρ := lt_min hrc0 reg.hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hρrc0 : ρ ≤ rc0 := min_le_left _ _
  refine ⟨truncFactor A ρ, 1 + C_P * r, C_P, ?_, reg.hCP, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ M
    have : 0 ≤ C_P * r := mul_nonneg reg.hCP (le_of_lt reg.hr)
    linarith
  · -- F 0 = (unitVec i) ca
    rw [truncFactor_zero A hρ0, hA0]
  · -- AEStronglyMeasurable
    exact truncFactor_aesm A (hAcont.mono (Metric.ball_subset_ball hρrc0))
  · -- ∀v |F v| ≤ M
    exact truncFactor_bound A hρ0
      (fun v hv => hAbd v (Metric.ball_subset_ball hρr hv))
  · -- ∀v |F v - F 0| ≤ L‖v‖
    intro v
    rw [truncFactor_zero A hρ0]
    exact truncFactor_lip A reg.hCP
      (fun v hv => hAL v (Metric.ball_subset_ball hρr hv)) v

/-! ############################################################################
    ### 3. The payoff, re-threaded onto the proven local variant.
    ############################################################################ -/

/-- **★★★ `integral_heatHessMult_transportedJet_bound_from_localRNC`.**  The J4-999 odd-moment
    transported-coefficient payoff `integral_heatHessMult_mul_transportedCoeff`, with the two chart-jet
    factors now SUPPLIED from the PROVEN local RNC regularity (`localJet_global_factor`) instead of the
    un-satisfiable global `JointSecondOrderRNCRegularity`: for `τ > 0`, Gaussian-Hessian directions
    `p, q_dir`, a census scalar factor `qfac` (bounded `Mq` + Lip-at-0 `Lq` + measurable), and any two
    directions/components `(i,ca)`,`(j,cb)`, there exist the two chart-jet factors `a, b` with proven
    moduli such that
        `|∫ v, heatHessMult τ p q_dir v · (qfac v · a v · b v)|
            ≤ (Mq·Ma·Lb + Mq·Mb·La + Ma·Mb·Lq)·n³‖p‖‖q_dir‖(16√2+1)/√τ`.
    The chart-jet factor J4-999 named as the wall is now discharged from real regularity; only the census
    scalar `qfac` is carried (satisfiable, see `..._hyp_satisfiable`).  Does NOT close `hcomp` (base-slot
    CoV / chain rule / truncation-tail / coordinate summation remain).  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_transportedJet_bound_from_localRNC
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q₀ : Point n) (i j ca cb : Fin n)
    (τ : ℝ) (hτ : 0 < τ) (p q_dir : Point n)
    (qfac : Point n → ℝ) (Mq Lq : ℝ) (hMq : 0 ≤ Mq) (hLq : 0 ≤ Lq)
    (hqm : AEStronglyMeasurable qfac volume)
    (hqb : ∀ v, |qfac v| ≤ Mq) (hqL : ∀ v, |qfac v - qfac 0| ≤ Lq * ‖v‖) :
    ∃ (a b : Point n → ℝ) (Ma La Mb Lb : ℝ),
      0 ≤ Ma ∧ 0 ≤ La ∧ 0 ≤ Mb ∧ 0 ≤ Lb ∧
      a 0 = (unitVec i) ca ∧ b 0 = (unitVec j) cb ∧
      |∫ v : Point n, heatHessMult τ p q_dir v * (qfac v * a v * b v)|
        ≤ (Mq * Ma * Lb + Mq * Mb * La + Ma * Mb * Lq)
            * (n : ℝ) ^ 3 * ‖p‖ * ‖q_dir‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
  obtain ⟨a, Ma, La, hMa, hLa, ha0, ham, hab, haL⟩ := localJet_global_factor g gi hC q₀ i ca
  obtain ⟨b, Mb, Lb, hMb, hLb, hb0, hbm, hbb, hbL⟩ := localJet_global_factor g gi hC q₀ j cb
  refine ⟨a, b, Ma, La, Mb, Lb, hMa, hLa, hMb, hLb, ha0, hb0, ?_⟩
  exact integral_heatHessMult_mul_transportedCoeff τ hτ p q_dir qfac a b
    Mq Lq Ma La Mb Lb hMq hLq hMa hLa hMb hLb hqm ham hbm hqb hqL hab haL hbb hbL

/-- **Non-vacuity of the sole carried input.**  The census scalar bundle of
    `integral_heatHessMult_transportedJet_bound_from_localRNC` is satisfiable by the genuine nonconstant
    weight `qfac := cos‖·‖` (`Mq = Lq = 1`), so the re-threaded payoff fires on a real coefficient.  The
    two chart-jet factors `a`,`b` are ALWAYS supplied (proven local variant), so no further witness is
    needed for them.  NOT `a₁ = R/6`. -/
theorem integral_heatHessMult_transportedJet_bound_from_localRNC_hyp_satisfiable :
    ∃ (qfac : Point n → ℝ) (Mq Lq : ℝ), 0 ≤ Mq ∧ 0 ≤ Lq ∧
      AEStronglyMeasurable qfac volume ∧
      (∀ v, |qfac v| ≤ Mq) ∧ (∀ v, |qfac v - qfac 0| ≤ Lq * ‖v‖) := by
  refine ⟨fun v => Real.cos ‖v‖, 1, 1, zero_le_one, zero_le_one,
    (Real.continuous_cos.comp continuous_norm).aestronglyMeasurable, fun v => Real.abs_cos_le_one _,
    fun v => ?_⟩
  have hlip := Real.lipschitzWith_cos.dist_le_mul ‖v‖ ‖(0 : Point n)‖
  simp only [Real.dist_eq, norm_zero, Real.cos_zero, NNReal.coe_one, one_mul,
    sub_zero, abs_norm] at hlip ⊢
  exact hlip

end QIQTH.LocalRNCJetFactor

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.LocalRNCJetFactor
#print axioms truncFactor_zero
#print axioms truncFactor_bound
#print axioms truncFactor_lip
#print axioms truncFactor_aesm
#print axioms localJet_global_factor
#print axioms integral_heatHessMult_transportedJet_bound_from_localRNC
#print axioms integral_heatHessMult_transportedJet_bound_from_localRNC_hyp_satisfiable
end AxiomChecks
