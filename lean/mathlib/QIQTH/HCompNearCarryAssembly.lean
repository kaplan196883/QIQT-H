/-
  HCompNearCarryAssembly — Plan v9 (`tranquil-stargazing-fox.md`, Task B STEP 4c, part (i)):
  the SLIVER-INTEGRATED chart-replacement cancellation bound — the NEAR analogue of J4-860's
  discharged FAR half (`HCompNearFarSplit.tailMoment_sliver_integral_le`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE — the near half of the near/far split of `VanVleckGatedSpatialSymmetry.hcomp`.

  `hcomp` bounds the per-direction √ε sliver integral `|∫ s ∫ z (kPrime … x z)(eⱼ)| ≤ bb j`.  J4-860
  (`HCompNearFarSplit.kPrime_sliver_near_far`) reduced it to `nb + fb` where:
    • `fb` (FAR, `z ∉ ball x ρ`) is DISCHARGED — exponentially suppressed in `1/ε`
      (`tailMoment_sliver_integral_le`).
    • `nb` (NEAR, `z ∈ ball x ρ`) is the reversal-CANCELLATION √ε bound — the STEP-4c deliverable.

  The generic-base reversal identity (J4-858, `baseSlot_eventuallyEq_neg_terminalVel_at`) plus the
  cubic-remainder Taylor bound (J4-859, `terminalVelAt_cubic_remainder`) turn the base↔eval chart swap
  into a NEAR-ISOMETRY `W` of the radial normal coordinate — `r²_{Wz} = r²_z + O(‖z‖³)` — for which the
  banked `weighted_chart_replace_bound` (S5c) gives, at a fixed heat-time `τ`,
      `∫_{ball 0 R} ‖z‖^k · |G_τ(Wz) − G_τ(z)| ≤ Cshape · (√τ)^{k+1}`.
  THIS FILE integrates that fixed-`τ` cancellation over the sliver `τ = t − s ∈ (0, ε]`, exactly as the
  FAR half integrated its exponentially-suppressed tail moment, delivering the matched near rate
      `‖∫ s in (t−ε)..t, ∫_{ball 0 R} ‖z‖^k · |G_{t−s}(Wz) − G_{t−s}(z)|‖ ≤ Cshape · (√ε)^{k+3}`,
  i.e. `O(ε^{(k+3)/2})` — for `k = 0` this is `O(ε^{3/2})`, superpolynomially BELOW the `O(√ε)` target,
  well inside `bb j`.  Route: `weighted_chart_replace_bound` at `τ = t−s`, then the sliver-uniform
  monotone bound `(√(t−s))^{k+1} ≤ (√ε)^{k+1}` (`chartReplace_sliver_uniform_bound`), then the
  constant-bound interval integral `intervalIntegral.norm_integral_le_of_norm_le_const_ae` (the `s = t`,
  `τ = 0` endpoint is null) — mirroring `tailMoment_sliver_integral_le` PRECISELY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It also
  does NOT, by itself, discharge `hcomp`: it delivers the ANALYTIC near rate on the chart-replacement
  CANCELLATION integrand `‖z‖^k · |G_τ(Wz) − G_τ(z)|`, the near companion of the banked far-half rate.
  What remains for a full `hcomp` discharge (honestly NOT built here) is the CONCRETE identification of
  the `kPrime` component `∫_{ball x ρ} (kPrime … x z)(eⱼ)` with a chart-replacement cancellation of this
  shape (via the reversal identity applied to the gated van-Vleck field-Hessian), plus the concrete FAR
  domination of the mixed field-Hessian by the tail-moment envelope — both genuine, un-banked
  `kPrime`→envelope plumbing (the far side hits the mixed-Hessian-envelope wall flagged at cp704).
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GaussianMomentEnvelope

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.RadialDistance
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the sliver-UNIFORM bound on the chart-replacement cancellation integral.
    ############################################################################### -/

/-- **`chartReplace_sliver_uniform_bound`.**  For a near-isometry `W` (with the pointwise ℓ²-error
    `herr` and coercivity `hmin` on `ball 0 R`), a sliver width `ε > 0`, and — supplied UNIFORMLY over
    the sliver `τ ∈ (0, ε]` — the base integrability `hWint` and the 1-D `(k+3)`-moment bound `hmom`,
    the weighted chart-replacement cancellation integral is bounded UNIFORMLY over the sliver by a
    constant `∝ (√ε)^{k+1}`:
        `∫_{ball 0 R} ‖z‖^k · |G_τ(Wz) − G_τ(z)| ≤ Cshape · (√ε)^{k+1}`   for every `τ ∈ (0, ε]`,
    where `Cshape := (L'/4)·(√2)^n·(n·ck3·(√2)^{k+3})`.  Route: `weighted_chart_replace_bound` at `τ`
    gives `≤ Cshape·(√τ)^{k+1}`, then `(√τ)^{k+1} ≤ (√ε)^{k+1}` (monotone, `τ ≤ ε`).  NOT `a₁ = R/6`. -/
theorem chartReplace_sliver_uniform_bound (k : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (W : Point n → Point n) (L' : ℝ) (hL' : 0 ≤ L')
    (herr : ∀ z ∈ Metric.ball (0 : Point n) R, |rncRadialSq (W z) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z ∈ Metric.ball (0 : Point n) R, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z))
    (ck3 : ℝ) (hck3 : 0 ≤ ck3)
    (hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      IntegrableOn (fun z : Point n => ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|)
        (Metric.ball 0 R) volume)
    (hmom : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
        ≤ ck3 * (Real.sqrt (2 * τ)) ^ (k + 3))
    {τ : ℝ} (hτ : 0 < τ) (hτε : τ ≤ ε) :
    ∫ z in Metric.ball (0 : Point n) R, ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3)))
          * (Real.sqrt ε) ^ (k + 1) := by
  set Cshape : ℝ := L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))
    with hCshape
  have hCshape_nn : 0 ≤ Cshape := by rw [hCshape]; positivity
  have hbase := weighted_chart_replace_bound k τ hτ W R L' hL' herr hmin
    (hWint τ hτ hτε) ck3 hck3 (hmom τ hτ hτε)
  refine hbase.trans ?_
  -- `(√τ)^{k+1} ≤ (√ε)^{k+1}` and `Cshape ≥ 0`.
  have hmono : (Real.sqrt τ) ^ (k + 1) ≤ (Real.sqrt ε) ^ (k + 1) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg τ) (Real.sqrt_le_sqrt hτε) (k + 1)
  exact mul_le_mul_of_nonneg_left hmono hCshape_nn

/-! ###############################################################################
    ### §2 — the DISCHARGED near sliver integral bound (the matched near rate).
    ############################################################################### -/

/-- **★★ `chartReplace_sliver_integral_le`.**  THE NEAR ANALOGUE of `tailMoment_sliver_integral_le`.
    Under the same uniform sliver hypotheses, the sliver integral of the (nonnegative) chart-replacement
    cancellation integral `Φ(s) := ∫_{ball 0 R} ‖z‖^k · |G_{t−s}(Wz) − G_{t−s}(z)|` is bounded by the
    matched near rate:
        `‖∫ s in (t−ε)..t, Φ(s)‖ ≤ Cshape · (√ε)^{k+3}`,
    i.e. `O(ε^{(k+3)/2})` — for `k = 0`, `O(ε^{3/2})`, superpolynomially below `O(√ε)`.
    Route: `chartReplace_sliver_uniform_bound` bounds `Φ(s)` (which is `≥ 0`, so `‖Φ(s)‖ = Φ(s)`) a.e.
    on the sliver by the constant `M := Cshape · (√ε)^{k+1}` (the single `s = t` / `τ = 0` endpoint is
    null), then `intervalIntegral.norm_integral_le_of_norm_le_const_ae`, and `M · ε = Cshape · (√ε)^{k+3}`
    since `ε = (√ε)²`.  NO integrability side-condition.  NOT `a₁ = R/6`. -/
theorem chartReplace_sliver_integral_le (k : ℕ) (R ε : ℝ) (hε : 0 < ε)
    (W : Point n → Point n) (L' : ℝ) (hL' : 0 ≤ L')
    (herr : ∀ z ∈ Metric.ball (0 : Point n) R, |rncRadialSq (W z) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hmin : ∀ z ∈ Metric.ball (0 : Point n) R, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z))
    (ck3 : ℝ) (hck3 : 0 ≤ ck3)
    (hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      IntegrableOn (fun z : Point n => ‖z‖ ^ k * |gaussDdim τ (W z) - gaussDdim τ z|)
        (Metric.ball 0 R) volume)
    (hmom : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
      ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
        ≤ ck3 * (Real.sqrt (2 * τ)) ^ (k + 3))
    (t : ℝ) :
    ‖∫ s in (t - ε)..t,
        ∫ z in Metric.ball (0 : Point n) R,
          ‖z‖ ^ k * |gaussDdim (t - s) (W z) - gaussDdim (t - s) z|‖
      ≤ (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3)))
          * (Real.sqrt ε) ^ (k + 3) := by
  set Cshape : ℝ := L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))
    with hCshape
  set M : ℝ := Cshape * (Real.sqrt ε) ^ (k + 1) with hM
  have hle : t - ε ≤ t := by linarith
  -- a.e. norm bound by the constant `M` on the sliver (`s = t` is null).
  have hae : ∀ᵐ s : ℝ ∂volume, s ∈ Set.uIoc (t - ε) t →
      ‖∫ z in Metric.ball (0 : Point n) R,
          ‖z‖ ^ k * |gaussDdim (t - s) (W z) - gaussDdim (t - s) z|‖ ≤ M := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne] with s hsne hmem
    rw [Set.uIoc_of_le hle] at hmem
    obtain ⟨hs1, hs2⟩ := hmem
    have hs2' : s < t := lt_of_le_of_ne hs2 hsne
    have hτpos : 0 < t - s := by linarith
    have hτε : t - s ≤ ε := by linarith
    -- the inner integral is nonnegative, so its norm is itself.
    have hΦnn : 0 ≤ ∫ z in Metric.ball (0 : Point n) R,
        ‖z‖ ^ k * |gaussDdim (t - s) (W z) - gaussDdim (t - s) z| := by
      apply setIntegral_nonneg measurableSet_ball
      intro z _
      positivity
    rw [Real.norm_of_nonneg hΦnn, hM]
    exact chartReplace_sliver_uniform_bound k R ε hε W L' hL' herr hmin ck3 hck3
      hWint hmom hτpos hτε
  calc ‖∫ s in (t - ε)..t,
          ∫ z in Metric.ball (0 : Point n) R,
            ‖z‖ ^ k * |gaussDdim (t - s) (W z) - gaussDdim (t - s) z|‖
      ≤ M * |t - (t - ε)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    _ = M * ε := by rw [show t - (t - ε) = ε by ring, abs_of_pos hε]
    _ = Cshape * (Real.sqrt ε) ^ (k + 3) := by
        rw [hM]
        have hpow : (Real.sqrt ε) ^ (k + 3) = (Real.sqrt ε) ^ (k + 1) * ε := by
          rw [show k + 3 = (k + 1) + 2 from by ring, pow_add, Real.sq_sqrt hε.le]
        rw [hpow]; ring

end QIQTH.HCompNearCarryAssembly

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryAssembly
#print axioms chartReplace_sliver_uniform_bound
#print axioms chartReplace_sliver_integral_le
end AxiomChecks
