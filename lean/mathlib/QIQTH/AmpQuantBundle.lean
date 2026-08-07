/-
  QIQTH / HeatResidualBound — AmpQuantBundle.lean   (J4-399, Sol #17 E2: the amplitude QUANTITATIVE bundle)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It is the second (E2) of the three
  `dataAmp` bricks on the critical path (Sol consult #17): the QUANTITATIVE PAIR
  {L_{A_chart} + hcubic-sat} that sits alongside the geometry bundle E1 (J4-398, `AmpGeometryBundle`).
  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE TWO QUANTITATIVE CARRIES (exact shapes as they enter the matched-pair assembly).

  • **L_{A_chart}** — the ρ-scaled chart-amplitude Lipschitz constant on the collar.  Per Sol #17 it is
    the remaining named DATA carry `L_g` of `DisplacementDerivative.collar_product_lipschitz_increment`
    (`Lip(ρ·A_chart) ≤ M_ρ·L_{A_chart} + M_{A_chart}·L_ρ`): the Lipschitz constant of the base-varying
    chart amplitude `z ↦ chartAmp g gi hC hK a b τ z 0` on the compact gate ball.  We LAND its
    quantitative machinery: the mean-value inequality on the convex ball
    (`Convex.norm_image_sub_le_of_norm_fderiv_le`) fed by the compact first-derivative bound
    (`ContDiffAt ℝ 1 ⟹ fderiv locally bounded`), producing `∃ r L, 0 ≤ L ∧ ∀ z w ∈ ball, |A z − A w| ≤
    L·dist z w`.  The base-varying amplitude regularity `ContDiffAt ℝ 1 (fun z ↦ A z 0) 0` is the
    single honest carry (it is `Φ ∘ W_bv` with `Φ` the van-Vleck factor and `W_bv` the C²-at-0
    base-varying chart of `DisplacementDerivative` — satisfiable, exactly analogous to the banked
    FIELD-slot `AmplitudeFamilyDischarge.amp_contDiffAt_general`).

  • **hcubic-sat** — the cubic-contact Taylor side.  Per Sol #17: the uniform first-order Taylor
    remainder on the fixed collar from the E1 2-jets, `‖A z − A 0 − DA(0)z‖ ≤ K·‖z‖²`, plus the r ≤ 1
    absorption `‖z‖³ ≤ ‖z‖²`; the MOMENT side is the banked `cubic_gaussian_moment_witness` (re-exported
    here).  We LAND: the abstract quadratic first-order Taylor remainder from a C²-modulus
    (`DisplacementDerivative.contDiffAt_two_fderiv_sub_zero_bound` + the primed convex MVT
    `Convex.norm_image_sub_le_of_norm_fderiv_le'`), the `‖z‖³ ≤ ‖z‖²` collar absorption, and the moment
    re-export.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES.
    (Q1) `contDiffAt_one_fderiv_bounded_near_zero`  — ★ the compact/local first-derivative bound.
    (Q2) `contDiffAt_one_lipschitzOn_ball`          — ★ the abstract MVT-Lipschitz on a ball.
         `chartAmp_base_lipschitzOn_ball`           — ★★ L_{A_chart}: concrete chart-amplitude Lipschitz.
         `Aamp_times_F_lipschitz`                   — ★★ the assembled `hqLip`-field shape (Q4 feed).
    (Q3) `contDiffAt_two_taylor1_remainder_bound`   — ★ the quadratic first-order Taylor remainder.
         `cube_le_sq_of_norm_le_one`                — the r ≤ 1 collar cubic absorption `‖z‖³ ≤ ‖z‖²`.
         `cubic_gaussian_moment_reexport`           — the banked cubic Gaussian moment (moment side).
    census `L_A_chart_carries` / `hcubic_carries`   — the honest residual carries.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable; no existing file edited;
  not wired into QIQTH.lean / AxiomAudit.lean.  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmpGeometryBundle
import QIQTH.DisplacementDerivative
import QIQTH.SliverAssemblyMatched

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.AmpQuantBundle

open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar
open QIQTH.DisplacementDerivative

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    (Q1) — the compact / local first-derivative bound.
    ############################################################################### -/

/-- **★ (Q1) `contDiffAt_one_fderiv_bounded_near_zero`.**  THE COMPACT FIRST-DERIVATIVE BOUND.  For any
    `f : E → F` that is `ContDiffAt ℝ 1` at `0`, the Fréchet derivative `fderiv f` is continuous at `0`
    (`ContDiffAt.continuousAt_fderiv`), hence uniformly bounded on some ball:
      `∃ r > 0, ∃ M ≥ 0, ∀ z, ‖z‖ < r → ‖fderiv f z‖ ≤ M`   (`M = ‖fderiv f 0‖ + 1`).
    This is the compact derivative supremum the mean-value inequality (Q2) consumes — obtained from the
    banked smoothness (`ContDiffAt ℝ 1`), NOT from any continuity abstraction over the `.choose`-heavy
    chart.  ⚠ NOT `a₁ = R/6`. -/
theorem contDiffAt_one_fderiv_bounded_near_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiffAt ℝ 1 f 0) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖z‖ < r → ‖fderiv ℝ f z‖ ≤ M := by
  have hcont : ContinuousAt (fderiv ℝ f) 0 := hf.continuousAt_fderiv (by norm_num)
  have hmem : (fderiv ℝ f) ⁻¹' (Metric.ball (fderiv ℝ f 0) 1) ∈ 𝓝 (0 : E) :=
    hcont (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r, hr, ‖fderiv ℝ f 0‖ + 1, by positivity, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hz' : fderiv ℝ f z ∈ Metric.ball (fderiv ℝ f 0) 1 := hrsub hzball
  rw [Metric.mem_ball, dist_eq_norm] at hz'
  have htri : ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f z - fderiv ℝ f 0‖ + ‖fderiv ℝ f 0‖ := by
    have := norm_add_le (fderiv ℝ f z - fderiv ℝ f 0) (fderiv ℝ f 0)
    simpa using this
  linarith [htri, hz']

/-! ###############################################################################
    (Q2) — the abstract MVT-Lipschitz + the concrete L_{A_chart} + the hqLip feed.
    ############################################################################### -/

/-- **★ (Q2) `contDiffAt_one_lipschitzOn_ball`.**  THE MEAN-VALUE LIPSCHITZ BOUND ON A BALL.  For any
    `f : E → F` that is `ContDiffAt ℝ 1` at `0`, there is a ball on which `f` is Lipschitz:
      `∃ r > 0, ∃ L ≥ 0, ∀ z w, ‖z‖ < r → ‖w‖ < r → ‖f z − f w‖ ≤ L·‖z − w‖`.
    Route: the compact derivative bound (Q1) gives `‖fderiv f‖ ≤ M` on `ball 0 r₁`; `ContDiffAt.eventually`
    gives `f` differentiable on `ball 0 r₂`; the open ball is convex, so the mean-value inequality
    `Convex.norm_image_sub_le_of_norm_fderiv_le` closes with `L = M` on `ball 0 (min r₁ r₂)`.
    ⚠ NOT `a₁ = R/6`. -/
theorem contDiffAt_one_lipschitzOn_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiffAt ℝ 1 f 0) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : E, ‖z‖ < r → ‖w‖ < r →
      ‖f z - f w‖ ≤ L * ‖z - w‖ := by
  obtain ⟨r₁, hr₁, M, hM, hbound⟩ := contDiffAt_one_fderiv_bounded_near_zero f hf
  have hdiff_ev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.mem_nhds_iff.mp hdiff_ev
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, M, hM, ?_⟩
  intro z w hz hw
  have hconv : Convex ℝ (Metric.ball (0 : E) (min r₁ r₂)) := convex_ball _ _
  have hdiffball : ∀ x ∈ Metric.ball (0 : E) (min r₁ r₂), DifferentiableAt ℝ f x := by
    intro x hx
    exact hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hboundball : ∀ x ∈ Metric.ball (0 : E) (min r₁ r₂), ‖fderiv ℝ f x‖ ≤ M := by
    intro x hx
    have hx1 : x ∈ Metric.ball (0 : E) r₁ := Metric.ball_subset_ball (min_le_left _ _) hx
    exact hbound x (by simpa [Metric.mem_ball, dist_zero_right] using hx1)
  have hzmem : z ∈ Metric.ball (0 : E) (min r₁ r₂) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hwmem : w ∈ Metric.ball (0 : E) (min r₁ r₂) := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiffball hboundball hconv hwmem hzmem

/-- **★★ (Q2) `chartAmp_base_lipschitzOn_ball` — L_{A_chart}, LANDED.**  The base-varying chart amplitude
    `z ↦ chartAmp g gi hC hK a b τ z 0` is Lipschitz on a gate ball:
      `∃ r > 0, ∃ L ≥ 0, ∀ z w, ‖z‖ < r → ‖w‖ < r → |A z − A w| ≤ L·dist z w`.
    `L` is exactly the named DATA carry `L_g = L_{A_chart}` that
    `DisplacementDerivative.collar_product_lipschitz_increment` (and the brick-1/2 collar Lipschitz `hqLip`)
    demand.  Route: `contDiffAt_one_lipschitzOn_ball` (Q1+Q2) applied to the base-varying amplitude, the
    real-norm being the absolute value.  The single honest CARRY is the base-varying amplitude regularity
    `hA1 : ContDiffAt ℝ 1 (fun z ↦ A z 0) 0` — satisfiable (`A = Φ ∘ W_bv`, `Φ` van-Vleck-smooth,
    `W_bv` C²-at-0 by `DisplacementDerivative`; analogous to the banked field-slot
    `AmplitudeFamilyDischarge.amp_contDiffAt_general`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_lipschitzOn_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ)
    (hA1 : ContDiffAt ℝ 1 (fun z : Point n => chartAmp g gi hC hK a b τ z 0) 0) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
      |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L * dist z w := by
  obtain ⟨r, hr, L, hL, hlip⟩ := contDiffAt_one_lipschitzOn_ball _ hA1
  refine ⟨r, hr, L, hL, ?_⟩
  intro z w hz hw
  have hnorm := hlip z w hz hw
  rwa [Real.norm_eq_abs, ← dist_eq_norm] at hnorm

/-- **(Q2) `triple_product_lipschitz_increment`.**  The three-factor product-Lipschitz increment,
    generalising `DisplacementDerivative.collar_product_lipschitz_increment` from two factors to three
    (the roles `ρ · A_chart · F` at the sliver call site):
      `|f z·g z·h z − f w·g w·h w| ≤ (M_f·M_g·L_h + (M_f·L_g + M_g·L_f)·M_h)·dist z w`.
    Route: two nested applications of the banked two-factor increment (`f·g` as one factor, `h` as the
    other).  ⚠ NOT `a₁ = R/6`. -/
theorem triple_product_lipschitz_increment
    (f g h : Point n → ℝ) (M_f M_g M_h L_f L_g L_h : ℝ) (z w : Point n)
    (hMfnn : 0 ≤ M_f) (hMgnn : 0 ≤ M_g) (hMhnn : 0 ≤ M_h)
    (hMfz : |f z| ≤ M_f) (hMgz : |g z| ≤ M_g) (hMgw : |g w| ≤ M_g) (hMhw : |h w| ≤ M_h)
    (hLf : |f z - f w| ≤ L_f * dist z w)
    (hLg : |g z - g w| ≤ L_g * dist z w)
    (hLh : |h z - h w| ≤ L_h * dist z w) :
    |f z * g z * h z - f w * g w * h w|
      ≤ (M_f * M_g * L_h + (M_f * L_g + M_g * L_f) * M_h) * dist z w := by
  have hfg_bound : |f z * g z| ≤ M_f * M_g := by
    rw [abs_mul]; exact mul_le_mul hMfz hMgz (abs_nonneg _) hMfnn
  have hfg_incr : |f z * g z - f w * g w| ≤ (M_f * L_g + M_g * L_f) * dist z w :=
    collar_product_lipschitz_increment f g M_f M_g L_f L_g z w hMfnn hMgnn hMfz hMgw hLf hLg
  have key := collar_product_lipschitz_increment (fun p => f p * g p) h
    (M_f * M_g) M_h (M_f * L_g + M_g * L_f) L_h z w
    (mul_nonneg hMfnn hMgnn) hMhnn hfg_bound hMhw hfg_incr hLh
  calc |f z * g z * h z - f w * g w * h w|
      ≤ ((M_f * M_g) * L_h + M_h * (M_f * L_g + M_g * L_f)) * dist z w := key
    _ = (M_f * M_g * L_h + (M_f * L_g + M_g * L_f) * M_h) * dist z w := by ring

/-- **★★ (Q2/Q4) `Aamp_times_F_lipschitz` — the assembled `hqLip`-field shape.**  For the concrete
    corrected amplitude `Aamp τ z = rhoRatio g gi hC hK τ z · chartAmp g gi hC hK a b τ z 0`, the product
    with the Levi kernel `F s · 0` obeys the exact `hqLip` increment shape of `amplitudeDataOn_concrete`:
      `|Aamp τ z · F s z 0 − Aamp τ w · F s w 0| ≤ Lq·dist z w`,
      `Lq = M_ρ·M_A·L_F + (M_ρ·L_A + M_A·L_ρ)·M_F`,
    from the three factor carries `(ρ, chartAmp 0, F s·0)` — `M_ρ` bounded by `collarK`
    (`rhoRatio_le_collarK`), `L_A` the LANDED `chartAmp_base_lipschitzOn_ball` constant, and
    `L_ρ`/`M_A`/`M_F`/`L_F` the named Sol #13 carries.  Route: `triple_product_lipschitz_increment` with
    `f = ρ`, `g = chartAmp 0`, `h = F s·0`.  This is the E2 feed into the bundle's `hqLip` field.
    ⚠ NOT `a₁ = R/6`. -/
theorem Aamp_times_F_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (F0 : Point n → ℝ)
    (M_ρ M_A M_F L_ρ L_A L_F : ℝ) (z w : Point n)
    (hMρnn : 0 ≤ M_ρ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hMρz : |rhoRatio g gi hC hK τ z| ≤ M_ρ)
    (hMAz : |chartAmp g gi hC hK a b τ z 0| ≤ M_A)
    (hMAw : |chartAmp g gi hC hK a b τ w 0| ≤ M_A)
    (hMFw : |F0 w| ≤ M_F)
    (hLρ : |rhoRatio g gi hC hK τ z - rhoRatio g gi hC hK τ w| ≤ L_ρ * dist z w)
    (hLA : |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : |F0 z - F0 w| ≤ L_F * dist z w) :
    |(rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) * F0 z
        - (rhoRatio g gi hC hK τ w * chartAmp g gi hC hK a b τ w 0) * F0 w|
      ≤ (M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F) * dist z w :=
  triple_product_lipschitz_increment
    (fun p => rhoRatio g gi hC hK τ p) (fun p => chartAmp g gi hC hK a b τ p 0) F0
    M_ρ M_A M_F L_ρ L_A L_F z w hMρnn hMAnn hMFnn hMρz hMAz hMAw hMFw hLρ hLA hLF

/-! ###############################################################################
    (Q3) — the cubic Taylor remainder, the r ≤ 1 absorption, the moment re-export.
    ############################################################################### -/

/-- **★ (Q3) `contDiffAt_two_taylor1_remainder_bound`.**  THE QUADRATIC FIRST-ORDER TAYLOR REMAINDER.
    For any `f : E → F` that is `ContDiffAt ℝ 2` at `0`, the first-order Taylor remainder is
    quadratically small on a ball:
      `∃ r > 0, ∃ K ≥ 0, ∀ z, ‖z‖ < r → ‖f z − f 0 − fderiv f 0 z‖ ≤ K·‖z‖²`.
    Route: the C²-modulus (`DisplacementDerivative.contDiffAt_two_fderiv_sub_zero_bound`,
    `‖fderiv f x − fderiv f 0‖ ≤ K·‖x‖`) feeds the primed convex mean-value inequality
    `Convex.norm_image_sub_le_of_norm_fderiv_le'` on the closed ball `closedBall 0 ‖z‖` (bound `K·‖z‖`,
    endpoints `0` and `z`), giving remainder `≤ K·‖z‖·‖z‖ = K·‖z‖²`.  This is the second-jet (cubic-contact)
    data — the uniform Taylor remainder on the fixed collar demanded by Sol #17's hcubic-sat.
    ⚠ NOT `a₁ = R/6`. -/
theorem contDiffAt_two_taylor1_remainder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ r > (0 : ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖z‖ < r →
      ‖f z - f 0 - (fderiv ℝ f 0) z‖ ≤ K * ‖z‖ ^ 2 := by
  obtain ⟨r₁, hr₁, K, hK, hmod⟩ := contDiffAt_two_fderiv_sub_zero_bound f hf
  have hdiff_ev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.mem_nhds_iff.mp hdiff_ev
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, K, hK, ?_⟩
  intro z hz
  have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hzr₂ : ‖z‖ < r₂ := lt_of_lt_of_le hz (min_le_right _ _)
  have hconv : Convex ℝ (Metric.closedBall (0 : E) ‖z‖) := convex_closedBall _ _
  have hsub1 : Metric.closedBall (0 : E) ‖z‖ ⊆ Metric.ball (0 : E) r₁ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hx hzr₁
  have hsub2 : Metric.closedBall (0 : E) ‖z‖ ⊆ Metric.ball (0 : E) r₂ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hx hzr₂
  have hdiffs : ∀ x ∈ Metric.closedBall (0 : E) ‖z‖, DifferentiableAt ℝ f x :=
    fun x hx => hr₂sub (hsub2 hx)
  have hbounds : ∀ x ∈ Metric.closedBall (0 : E) ‖z‖, ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ K * ‖z‖ := by
    intro x hx
    have hx1 : ‖x‖ < r₁ := by
      have := hsub1 hx; rwa [Metric.mem_ball, dist_zero_right] at this
    have hxz : ‖x‖ ≤ ‖z‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx
    calc ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ K * ‖x‖ := hmod x hx1
      _ ≤ K * ‖z‖ := by gcongr
  have h0s : (0 : E) ∈ Metric.closedBall (0 : E) ‖z‖ := by
    rw [Metric.mem_closedBall, dist_self]; exact norm_nonneg z
  have hzs : z ∈ Metric.closedBall (0 : E) ‖z‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (s := Metric.closedBall (0 : E) ‖z‖) (C := K * ‖z‖) (φ := fderiv ℝ f 0)
    (x := (0 : E)) (y := z) hdiffs hbounds hconv h0s hzs
  calc ‖f z - f 0 - (fderiv ℝ f 0) z‖
      = ‖f z - f 0 - (fderiv ℝ f 0) (z - 0)‖ := by rw [sub_zero]
    _ ≤ K * ‖z‖ * ‖z - 0‖ := hmvt
    _ = K * ‖z‖ ^ 2 := by rw [sub_zero]; ring

/-- **(Q3) `cube_le_sq_of_norm_le_one`.**  THE r ≤ 1 COLLAR CUBIC ABSORPTION.  On the collar (radius
    ≤ 1) the cubic term is dominated by the quadratic one: `‖z‖ ≤ 1 → ‖z‖³ ≤ ‖z‖²`.  This is the
    higher-order absorption Sol #17 uses to fold the cubic-contact remainder into the fixed-collar
    estimate.  ⚠ NOT `a₁ = R/6`. -/
theorem cube_le_sq_of_norm_le_one {E : Type*} [NormedAddCommGroup E] (z : E) (hz : ‖z‖ ≤ 1) :
    ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 := by
  have hmul : ‖z‖ ^ 2 * ‖z‖ ≤ ‖z‖ ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hz (pow_nonneg (norm_nonneg z) 2)
  calc ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ := by ring
    _ ≤ ‖z‖ ^ 2 * 1 := hmul
    _ = ‖z‖ ^ 2 := by ring

/-- **(Q3) `cubic_gaussian_moment_reexport` — the MOMENT side of hcubic (banked).**  The width-generic
    cubic Gaussian moment `∫ ‖z‖³·G_{κτ} ≤ n·(64√2+1)·(√κ)³·(√τ)³`, re-exported from
    `SliverAssemblyMatched.cubic_gaussian_moment_witness`.  Together with the cubic-contact Taylor
    remainder (`contDiffAt_two_taylor1_remainder_bound`) + the r ≤ 1 absorption
    (`cube_le_sq_of_norm_le_one`), this is the complete E2 hcubic-sat side (the Taylor remainder is the
    integrand's cubic contact; this bounds its Gaussian moment).  ⚠ NOT `a₁ = R/6`. -/
theorem cubic_gaussian_moment_reexport (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) :
    ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (κ * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt κ) ^ 3 * (Real.sqrt τ) ^ 3 :=
  QIQTH.SliverAssemblyMatched.cubic_gaussian_moment_witness κ τ hκ hτ

/-! ###############################################################################
    The honest residual census (the named minimal carries of each half).
    ############################################################################### -/

/-- **`L_A_chart_carries`.**  The enumerated, satisfiable residual for the L_{A_chart} half at a GENERAL
    base — a genuine conjunction (non-vacuous), stated abstractly for machine-checkability.

    THE RESIDUAL (each SATISFIABLE, none the conclusion):
      1. `hAmpC1` — the base-varying chart-amplitude regularity `ContDiffAt ℝ 1 (fun z ↦ A z 0) 0`
         (`A = Φ ∘ W_bv`, analogous to the banked field-slot `amp_contDiffAt_general`);
      2. `hLρ`   — the ρ-ratio Lipschitz constant `L_ρ` (Sol's `K·C_r·c²/4`, from the D2 cubic-contact
         gradient via `ρ = e^{Δr/(4τ)}`);
      3. `hMA`   — the chart-amplitude sup-bound `M_{A_chart}` on the collar (the E1/census `hM·chart`);
      4. `hLevi` — the Levi-kernel sup/Lipschitz carries `(M_F, L_F)`.
    ⚠ NOT `a₁ = R/6`; the L_{A_chart} feed is CONDITIONAL on exactly this residual. -/
def L_A_chart_carries (hAmpC1 hLρ hMA hLevi : Prop) : Prop :=
  hAmpC1 ∧ hLρ ∧ hMA ∧ hLevi

/-- The L_{A_chart} residual census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem L_A_chart_carries_intro {hAmpC1 hLρ hMA hLevi : Prop}
    (h1 : hAmpC1) (h2 : hLρ) (h3 : hMA) (h4 : hLevi) :
    L_A_chart_carries hAmpC1 hLρ hMA hLevi :=
  ⟨h1, h2, h3, h4⟩

/-- **`hcubic_carries`.**  The enumerated, satisfiable residual for the hcubic-sat half — a genuine
    conjunction (non-vacuous), stated abstractly for machine-checkability.

    THE RESIDUAL (each SATISFIABLE, none the conclusion):
      1. `hAmpC2` — the base-varying chart-amplitude second-order regularity `ContDiffAt ℝ 2 (fun z ↦ A z 0) 0`
         (feeds the quadratic Taylor remainder `contDiffAt_two_taylor1_remainder_bound`);
      2. `hMoment` — the width-generic cubic Gaussian moment (LANDED, `cubic_gaussian_moment_reexport`);
      3. `hAbsorb` — the r ≤ 1 collar absorption `‖z‖³ ≤ ‖z‖²` (LANDED, `cube_le_sq_of_norm_le_one`).
    ⚠ NOT `a₁ = R/6`; the hcubic-sat side is CONDITIONAL on exactly this residual. -/
def hcubic_carries (hAmpC2 hMoment hAbsorb : Prop) : Prop :=
  hAmpC2 ∧ hMoment ∧ hAbsorb

/-- The hcubic-sat residual census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem hcubic_carries_intro {hAmpC2 hMoment hAbsorb : Prop}
    (h1 : hAmpC2) (h2 : hMoment) (h3 : hAbsorb) :
    hcubic_carries hAmpC2 hMoment hAbsorb :=
  ⟨h1, h2, h3⟩

end QIQTH.AmpQuantBundle

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AmpQuantBundle.contDiffAt_one_fderiv_bounded_near_zero
#print axioms QIQTH.AmpQuantBundle.contDiffAt_one_lipschitzOn_ball
#print axioms QIQTH.AmpQuantBundle.chartAmp_base_lipschitzOn_ball
#print axioms QIQTH.AmpQuantBundle.triple_product_lipschitz_increment
#print axioms QIQTH.AmpQuantBundle.Aamp_times_F_lipschitz
#print axioms QIQTH.AmpQuantBundle.contDiffAt_two_taylor1_remainder_bound
#print axioms QIQTH.AmpQuantBundle.cube_le_sq_of_norm_le_one
#print axioms QIQTH.AmpQuantBundle.cubic_gaussian_moment_reexport
#print axioms QIQTH.AmpQuantBundle.L_A_chart_carries_intro
#print axioms QIQTH.AmpQuantBundle.hcubic_carries_intro
