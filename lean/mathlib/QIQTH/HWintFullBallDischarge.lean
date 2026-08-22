/-
  HWintFullBallDischarge — discharging `hWint`, the LAST generic hypothesis of J4-879's
  `terminalVelAt_chartReplace_sliver_bound` (the near-carry `nb` sliver rate), by exploiting a
  DON'T-UNDERCREDIT fact: J4-1015's own honesty note flagged `hWint` as needing measurability of
  `terminalVelAt` on a FULL BALL, while regularity was "banked only AT `0`
  (`terminalVelAt_contDiffAt_two`)" — but the underlying facts that lemma is built from
  (`terminalVelAt_apply_eq_fderiv_diag`, `uniformFlowExp_contDiffAt_four`) already hold at EVERY point
  of an open ball, not just `0`.  The `C²`-at-`0` packaging was a needless specialization.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `terminalVelAt_chartReplace_sliver_bound` (J4-879) carries two generic hypotheses,
  `hWint` (base-Gaussian-difference integrability on `ball 0 R`) and `hmom` (a pure 1-D moment bound).
  `hmom` was discharged unconditionally by J4-1015 (`GaussianAbsMomentGeneral.terminalVel_sliver_hmom`).
  This file discharges `hWint` unconditionally too, closing BOTH remaining generic hypotheses of that
  lemma and producing a fully UNCONDITIONAL version of the near-sliver rate (mod only the standing
  geometry `(g, gi, hC, hK, x₀ ∈ K)`).

  Route:
    • (§1) Generalize `terminalVelAt_contDiffAt_two`'s proof (which specializes at `v₀ = 0`) to an
      ARBITRARY basepoint `v₀` in the open ball `ball 0 ρ0`, `ρ0 := min (expRho x₀) (uniformFlowRadius)`
      — the diagonal identity `terminalVelAt_apply_eq_fderiv_diag` and the position-endpoint regularity
      `uniformFlowExp_contDiffAt_four` are BOTH already stated `∀ v` in that ball, so the SAME
      `fderiv_right`/`clm_apply`/`congr_of_eventuallyEq` argument transfers verbatim to any `v₀` there.
    • (§2) Package via Mathlib's `IsOpen.contDiffOn_iff` into `ContDiffOn ℝ 2 (terminalVelAt … x₀)
      (ball 0 ρ0)`, hence `ContinuousOn` there.
    • (§3) For the (uncontrolled) radius `R` produced by `terminalVelAt_nearIsometry_data` /
      `terminalVelAt_chartReplace_sliver_bound`, shrink it to `R' := min R ρ0` — `herr`/`hmin` restrict
      to `ball 0 R'` for FREE (they are literally `∀ z ∈ ball 0 R, …`, so `.mono` via
      `Metric.ball_subset_ball` with UNCHANGED constants `L'`).  This makes `R' ≤ ρ0` true BY
      CONSTRUCTION, so §2's `ContinuousOn` applies on `ball 0 R'`.
    • (§4) On `ball 0 R'`: the integrand `‖z‖^k · |G_τ(T_{x₀} z) − G_τ(z)|` is `ContinuousOn` (§3's
      continuity of `T_{x₀}`, composed with the banked `gaussDdim_cont`), hence `AEStronglyMeasurable`
      (`ContinuousOn.aestronglyMeasurable measurableSet_ball`), and pointwise DOMINATED by the CONSTANT
      `R'^k · gaussDdim τ 0` — via the banked peak bound `gaussDdim_le_diagonal` (BOTH `G_τ(T_{x₀}z)` and
      `G_τ(z)` are `≤ gaussDdim τ 0`, so their difference's abs is `≤ gaussDdim τ 0`) and `‖z‖ < R'`.
      `IntegrableOn` then follows via `Integrable.mono'` against `integrableOn_const` on the
      finite-measure ball — the SAME recipe as the banked `BoundaryAssembly.integrableOn_gauss_mul_
      bddOn_ball`.
    • (§5) Feed the discharged `hWint` (§4) together with the ALREADY-BANKED `hmom`
      (`terminalVel_sliver_hmom`) into the fully generic template
      `HCompNearCarryAssembly.chartReplace_sliver_integral_le` at the shrunk `R'`, giving an
      UNCONDITIONAL closed-form bound with NO remaining hypotheses beyond the standing geometry.

  This composition was pre-reviewed by `gpt-5.6-sol` (high): the radius-shrink step is a genuine
  `.mono` restriction (no constant re-derivation needed since `herr`/`hmin`/`hmom` are radius- or
  τ-only quantified, not radius-VALUED), and `ContinuousOn.aestronglyMeasurable measurableSet_ball`
  is the correct API for the measurability half.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  discharges `hWint`/`hmom` for ONE lemma (`terminalVelAt_chartReplace_sliver_bound`, J4-879) — the
  analytic near-sliver rate for the chart-replacement CANCELLATION integrand with `W := terminalVelAt`
  as the CONCRETE near-isometry.  It does **NOT**:
    • identify this integrand with `hcomp`'s actual `nb` component (the `kPrime`→envelope plumbing
      flagged in `HCompNearCarryAssembly`'s own firewall is separate, un-built work);
    • touch the eval-slot change-of-variables / Jacobian-weight-domination gap flagged by J4-1015
      (`ChartEvalSlotRadiusMerge`) — that is an INDEPENDENT obstruction in a DIFFERENT sub-problem
      (the CoV route to `nb`, not this direct-integrand route);
    • compose into any bound on `nb`, `hcomp`, or the capstone.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GeodesicReversalRouteAtPoint
import QIQTH.ChartThirdJet
import QIQTH.BoundaryAssembly
import QIQTH.FlowJointRegularity
import QIQTH.HCompNearCarryConcreteDischarge
import QIQTH.GaussianAbsMomentGeneral
import QIQTH.HCompNearCarryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.FlatHeatEquation
open QIQTH.ExpMap QIQTH.ChartThirdJet QIQTH.RadialDistance
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.HCompNearCarryConcreteDischarge
open QIQTH.GaussianAbsMomentGeneral
open QIQTH.HCompNearCarryAssembly
open scoped Topology Interval

namespace QIQTH.HWintFullBallDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — `terminalVelAt` is `C²` at EVERY point of the diagonal-identity ball, not just `0`.
    ############################################################################### -/

/-- **★★ `terminalVelAt_contDiffAt_two_at` — the generic-basepoint upgrade of
    `terminalVelAt_contDiffAt_two`.**  For ANY `v₀` with `‖v₀‖ < expRho g gi hC x₀` and
    `‖v₀‖ < uniformFlowRadius g gi hC hK` (not just `v₀ = 0`), `terminalVelAt g gi hC hK x₀` is
    `ContDiffAt ℝ 2` at `v₀`.  SAME proof as `terminalVelAt_contDiffAt_two`, since the diagonal
    identity and the position-endpoint `C⁴` regularity it is built from are both already stated for
    every point of the ball, not just `0`.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_contDiffAt_two_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (v₀ : Point n) (hv₀exp : ‖v₀‖ < expRho g gi hC x₀)
    (hv₀uf : ‖v₀‖ < uniformFlowRadius g gi hC hK) :
    ContDiffAt ℝ 2 (terminalVelAt g gi hC hK x₀) v₀ := by
  have hcd4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK x₀) v₀ :=
    uniformFlowExp_contDiffAt_four g gi hC hK x₀ hx₀K v₀ hv₀exp hv₀uf
  have hfd3 : ContDiffAt ℝ 3 (fderiv ℝ (uniformFlowExp g gi hC hK x₀)) v₀ :=
    hcd4.fderiv_right (m := 3) (by norm_num)
  have hF3 : ContDiffAt ℝ 3
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) v₀ :=
    hfd3.clm_apply contDiffAt_id
  have hF2 : ContDiffAt ℝ 2
      (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) v₀ :=
    hF3.of_le (by norm_num)
  have hball : Metric.ball (0 : Point n)
      (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK)) ∈ 𝓝 v₀ := by
    refine Metric.isOpen_ball.mem_nhds ?_
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_min hv₀exp hv₀uf
  have hEq : terminalVelAt g gi hC hK x₀
      =ᶠ[𝓝 v₀] (fun v => fderiv ℝ (uniformFlowExp g gi hC hK x₀) v v) := by
    filter_upwards [hball] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact terminalVelAt_apply_eq_fderiv_diag g gi hC hK hx₀K v
      (lt_of_lt_of_le hv (min_le_left _ _)) (lt_of_lt_of_le hv (min_le_right _ _))
  exact hF2.congr_of_eventuallyEq hEq

/-- **★★ `terminalVelAt_contDiffOn_two_ball`.**  `terminalVelAt g gi hC hK x₀` is `ContDiffOn ℝ 2` on
    the WHOLE open ball `ball 0 (min (expRho x₀) (uniformFlowRadius))` — the ball-wide upgrade of
    `terminalVelAt_contDiffAt_two`'s single-point fact, via `IsOpen.contDiffOn_iff`.  NOT
    `a₁ = R/6`. -/
theorem terminalVelAt_contDiffOn_two_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ContDiffOn ℝ 2 (terminalVelAt g gi hC hK x₀)
      (Metric.ball (0 : Point n) (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK))) := by
  rw [Metric.isOpen_ball.contDiffOn_iff]
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact terminalVelAt_contDiffAt_two_at g gi hC hK hx₀K v
    (lt_of_lt_of_le hv (min_le_left _ _)) (lt_of_lt_of_le hv (min_le_right _ _))

/-- `terminalVelAt g gi hC hK x₀` is `ContinuousOn` on that same ball.  NOT `a₁ = R/6`. -/
theorem terminalVelAt_continuousOn_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K) :
    ContinuousOn (terminalVelAt g gi hC hK x₀)
      (Metric.ball (0 : Point n) (min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK))) :=
  (terminalVelAt_contDiffOn_two_ball g gi hC hK hx₀K).continuousOn

/-! ###############################################################################
    ### §2 — `hWint`, discharged on a radius shrunk to lie inside the regularity ball.
    ############################################################################### -/

/-- **★★★ `terminalVelAt_hWint_on_shrunk_ball` — `hWint` DISCHARGED.**  For ANY `R > 0` and `ε`, there
    is a radius `R' > 0` with `R' ≤ R` such that the base-Gaussian-difference integrand is
    `IntegrableOn (ball 0 R')` for EVERY `τ ∈ (0, ε]` — UNCONDITIONALLY, no carried hypothesis.  Built
    by shrinking to `R' := min R ρ0` (`ρ0` from §1), giving `ContinuousOn` of `terminalVelAt` on
    `ball 0 R'` for free, then a constant pointwise domination via `gaussDdim_le_diagonal`.  NOT
    `a₁ = R/6`. -/
theorem terminalVelAt_hWint_on_shrunk_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (R : ℝ) (hR : 0 < R) (ε : ℝ) :
    ∃ R' > (0 : ℝ), R' ≤ R ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ε →
        IntegrableOn (fun z : Point n =>
            ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
          (Metric.ball (0 : Point n) R') volume := by
  set ρ0 : ℝ := min (expRho g gi hC x₀) (uniformFlowRadius g gi hC hK) with hρ0def
  have hρ0pos : 0 < ρ0 := lt_min (expRho_pos g gi hC x₀) (uniformFlowRadius_pos g gi hC hK)
  refine ⟨min R ρ0, lt_min hR hρ0pos, min_le_left _ _, ?_⟩
  set R' : ℝ := min R ρ0 with hR'def
  have hsubρ0 : Metric.ball (0 : Point n) R' ⊆ Metric.ball (0 : Point n) ρ0 :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hcontOn : ContinuousOn (terminalVelAt g gi hC hK x₀) (Metric.ball (0 : Point n) R') :=
    (terminalVelAt_continuousOn_ball g gi hC hK hx₀K).mono hsubρ0
  intro τ hτ0 _hτε
  have hcont1 : ContinuousOn (fun z => gaussDdim τ (terminalVelAt g gi hC hK x₀ z))
      (Metric.ball (0 : Point n) R') := (gaussDdim_cont τ).comp_continuousOn hcontOn
  have hcont2 : ContinuousOn (fun z : Point n => gaussDdim τ z) (Metric.ball (0 : Point n) R') :=
    (gaussDdim_cont τ).continuousOn
  have hcontI : ContinuousOn
      (fun z : Point n =>
        ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
      (Metric.ball (0 : Point n) R') :=
    (continuous_norm.pow k).continuousOn.mul
      (_root_.continuous_abs.comp_continuousOn (hcont1.sub hcont2))
  have hmeas : AEStronglyMeasurable
      (fun z : Point n =>
        ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
      (volume.restrict (Metric.ball (0 : Point n) R')) :=
    hcontI.aestronglyMeasurable measurableSet_ball
  set M : ℝ := gaussDdim τ (0 : Point n) with hMdef
  have hM0 : 0 ≤ M := gaussDdim_nonneg τ 0
  have hR'pos : 0 < R' := lt_min hR hρ0pos
  have hCbound : IntegrableOn (fun _ : Point n => R' ^ k * M)
      (Metric.ball (0 : Point n) R') volume :=
    integrableOn_const (by finiteness)
  refine Integrable.mono' hCbound hmeas ?_
  rw [ae_restrict_iff' measurableSet_ball]
  refine ae_of_all _ (fun z hz => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hz
  have ha : 0 ≤ gaussDdim τ (terminalVelAt g gi hC hK x₀ z) := gaussDdim_nonneg τ _
  have hb : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
  have haM : gaussDdim τ (terminalVelAt g gi hC hK x₀ z) ≤ M := gaussDdim_le_diagonal hτ0 _
  have hbM : gaussDdim τ z ≤ M := gaussDdim_le_diagonal hτ0 z
  have habs : |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z| ≤ M := by
    rw [abs_le]; constructor <;> linarith
  have hzk : ‖z‖ ^ k ≤ R' ^ k := by
    apply pow_le_pow_left₀ (norm_nonneg z) hz.le
  have hval : ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|
      ≤ R' ^ k * M :=
    mul_le_mul hzk habs (abs_nonneg _) (by positivity)
  calc ‖‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|‖
      = ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z| := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ R' ^ k * M := hval

/-! ###############################################################################
    ### §3 — the FULLY UNCONDITIONAL near-sliver rate: BOTH `hWint` and `hmom` discharged.
    ############################################################################### -/

/-- **★★★ `terminalVelAt_chartReplace_sliver_bound_unconditional` — THE PAYOFF.**  J4-879's near-sliver
    rate, with BOTH generic hypotheses (`hWint`, `hmom`) and the `ck3` side-condition discharged: for
    ANY `k, ε > 0, t`, there is `R' > 0`, `L' ≥ 0` with
        `‖∫ s in (t−ε)..t, ∫_{ball 0 R'} ‖z‖^k · |G_{t−s}(T_{x₀} z) − G_{t−s}(z)|‖
          ≤ (L'/4·√2ⁿ·(n·ck3·√2^{k+3}))·(√ε)^{k+3}`,
    `ck3 := absMomentConst (k+3)` — UNCONDITIONALLY, no remaining carried hypothesis.  Built by taking
    `terminalVelAt_nearIsometry_data`'s `(R, L', herr, hmin)`, shrinking to `R' := min R ρ0`
    (`herr`/`hmin` restrict for free via `.mono`), and feeding `R'`, the restricted `herr'`/`hmin'`,
    §2's discharged `hWint`, and the banked `terminalVel_sliver_hmom` into
    `HCompNearCarryAssembly.chartReplace_sliver_integral_le`.  NOT `a₁ = R/6` — a fully closed PIECE of
    `nb`'s plumbing, not `nb`/`hcomp` itself (see file header). -/
theorem terminalVelAt_chartReplace_sliver_bound_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    ∃ R' > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      ‖∫ s in (t - ε)..t,
          ∫ z in Metric.ball (0 : Point n) R',
            ‖z‖ ^ k * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z) - gaussDdim (t - s) z|‖
        ≤ (L' / 4 * (Real.sqrt 2) ^ n
              * ((n : ℝ) * absMomentConst (k + 3) * (Real.sqrt 2) ^ (k + 3)))
            * (Real.sqrt ε) ^ (k + 3) := by
  obtain ⟨R, hR, L', hL', herr, hmin⟩ := terminalVelAt_nearIsometry_data g gi hC hK hx₀K
  obtain ⟨R', hR'pos, hR'leR, hWint⟩ :=
    terminalVelAt_hWint_on_shrunk_ball g gi hC hK hx₀K k R hR ε
  have hsub : Metric.ball (0 : Point n) R' ⊆ Metric.ball (0 : Point n) R :=
    Metric.ball_subset_ball hR'leR
  have herr' : ∀ z ∈ Metric.ball (0 : Point n) R', |rncRadialSq (terminalVelAt g gi hC hK x₀ z) -
      rncRadialSq z| ≤ L' * ‖z‖ ^ 3 := fun z hz => herr z (hsub hz)
  have hmin' : ∀ z ∈ Metric.ball (0 : Point n) R',
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (terminalVelAt g gi hC hK x₀ z) :=
    fun z hz => hmin z (hsub hz)
  refine ⟨R', hR'pos, L', hL', ?_⟩
  exact QIQTH.HCompNearCarryAssembly.chartReplace_sliver_integral_le k R' ε hε
    (terminalVelAt g gi hC hK x₀) L' hL' herr' hmin'
    (absMomentConst (k + 3)) (absMomentConst_nonneg (k + 3)) hWint
    (terminalVel_sliver_hmom k ε) t

end QIQTH.HWintFullBallDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HWintFullBallDischarge
#print axioms terminalVelAt_contDiffAt_two_at
#print axioms terminalVelAt_contDiffOn_two_ball
#print axioms terminalVelAt_continuousOn_ball
#print axioms terminalVelAt_hWint_on_shrunk_ball
#print axioms terminalVelAt_chartReplace_sliver_bound_unconditional
end AxiomChecks
