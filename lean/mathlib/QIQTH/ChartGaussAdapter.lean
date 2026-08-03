/-
  ChartGaussAdapter — J4-127: the L¹ chart-to-plain Gaussian kernel-replacement adapter.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GAP THIS BRICK CLOSES.

  `AmplitudePackage.vanVleckGatedWitness_zero_factor` (J4-126) found that the concrete `N = 1`
  van-Vleck gated witness, on the `x = 0` slice, is
      `H_G τ 0 z = gaussDdim τ (W z 0) · amp(τ,z)`,
  i.e. the Gaussian sits at the CHART IMAGE `W z 0 = uniformInverseChart … z 0`, whereas EVERY proven
  boundary/delta-family interface (`BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`,
  `DeltaFamilyBoundary.tendsto_integral_gaussDdim_smul`) is stated for the PLAIN kernel
  `A τ 0 z = gaussDdim τ z · (u₀ z + τ·u₁ z)` with the Gaussian at `z` itself.  Since `gaussDdim`
  depends on its argument only through `rncRadialSq = Σ (·ᵏ)²` (`gaussDdim_eq_exp`), the two kernels
  differ pointwise only through `rncRadialSq (W z)` vs `rncRadialSq z`.  This file proves the two
  kernels are L¹-close as `τ → 0⁺` and packages the difference — WITHOUT touching any proven
  interface (the plain interfaces stay verbatim; the concrete kernel is reconciled to them).

  ## THE BRICKS.

    * `Gk` / `gaussDdim_eq_Gk` / `Gk_anti` / `Gk_scaled` — the radial-profile calculus:
        `gaussDdim τ v = Gk τ (rncRadialSq v)`, `Gk` is antitone in the radius-square, and the
        SCALED-ARGUMENT identity `Gk τ (s·r²) = √s⁻ⁿ · gaussDdim (τ/s) v` (the workhorse: it turns a
        Gaussian at a scaled radius into a rescaled-width plain Gaussian with a bounded prefactor).
    * `tail_width_tendsto` / `tail_plain_tendsto` — the `𝓝[>] 0`-filter Gaussian tail limits.
    * `chartDiff_integrableOn` — the per-`τ` integrability of `z ↦ gaussDdim τ (W z) − gaussDdim τ z`
        on the active set `S` (dominated via the coarse chart bound `c·r² ≤ r²_W`).
    * `chartGauss_l1_sub_plain_tendsto` (B1, the foundation) — the L¹ kernel-replacement:
        `∫_S |gaussDdim τ (W z) − gaussDdim τ z| → 0`  as `τ → 0⁺`.
    * `chartGauss_l1_mul_bdd_tendsto` (B2) — the bounded-multiplier corollary: the same difference
        tested against any eventually-uniformly-bounded family `F τ` still vanishes in the limit.
    * `chartAmp0` / `chartAmp1` / `witness_amp_affine` / `witness_sub_plain` (B3) — the concrete
        repackage: the on-gate amplitude of `H_G` is affine in `τ` (`amp = ũ₀ + τ·ũ₁`), and the
        witness–plain DIFFERENCE reduces EXACTLY to `(gaussDdim τ (W z 0) − gaussDdim τ z)·(ũ₀+τũ₁)`
        — the shape B2 consumes.

  ## HYPOTHESES (all genuine chart facts, satisfiable, non-vacuous, never the conclusion).
    B1/B2 are PARAMETRIC in the chart `W : Point n → Point n` and the active set `S`, constrained by:
      • `hcoarse` — a UNIFORM coarse lower bound `∃ c>0, ∀ z∈S, c·r² ≤ r²_W` (a genuine
        non-degeneracy fact of the near-isometry `W`; supplied for the true chart by the quantitative
        near-identity layer `NearIsometryBudget.uniformFlowExp_fderiv_near_id_quant`).
      • `hasymp` — the ASYMPTOTIC squeeze `∀ δ∈(0,1) ∃ r>0, ∀ z∈S, r²_z < r² → (1−δ)r² ≤ r²_W ≤ (1+δ)r²`
        (the `‖W z‖² = ‖z‖² + O(‖z‖⁴)` chart near-isometry, also from `NearIsometryBudget`).
      • `hWmeas` — base measurability of the chart-pushed Gaussian on `S`.
    Both are genuine facts of the honest chart, NOT vacuous and NOT the goal.

  ⚠ HONEST FIREWALL / CARRY.
    B4 (`boundary_chart_wrapper` — extending `boundary_tendstoLocallyUniformlyOn` to the literal
    concrete chart kernel via the split `I_chart = I_plain + (I_chart − I_plain)`) is CARRIED, not
    landed: its second term vanishes by B2 (the difference-reduction lemma `witness_sub_plain`
    supplies the exact multiplier shape), but wiring the FIRST term needs the full concrete
    `hAdom`/`hBcont`/center-value (`ũ₀ 0 = 1`) inputs from `ConcreteDominations` /
    the `J4-105..108` center-value layer, which is a separate assembly.  What lands here (B1+B2+B3
    incl. the difference reduction) is the analytic heart of the adapter.
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  Reusable BRICK;
    NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.WidthMarginEngine
import QIQTH.GaussianTailBoundary
import QIQTH.DeltaFamilyBoundary
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The radial Gaussian profile `Gk` and its calculus. -/

/-- **The radial Gaussian profile.**  `gaussDdim` depends on its argument only through
    `rncRadialSq = Σ (·ᵏ)²`; `Gk n τ r²` isolates that dependence:
      `Gk n τ r² = (√(4πτ))⁻ⁿ · exp(−r²/(4τ))`,   so `gaussDdim τ v = Gk n τ (rncRadialSq v)`. -/
noncomputable def Gk (n : ℕ) (τ r2 : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n * Real.exp (-r2 / (4 * τ))

theorem gaussDdim_eq_Gk (τ : ℝ) (v : Point n) : gaussDdim τ v = Gk n τ (rncRadialSq v) := by
  rw [gaussDdim_eq_exp]; rfl

theorem Gk_nonneg (τ r2 : ℝ) : 0 ≤ Gk n τ r2 := by
  unfold Gk; positivity

/-- **`Gk` is antitone in the radius-square** (larger radius ⟹ smaller Gaussian), for `τ > 0`. -/
theorem Gk_anti (τ : ℝ) (hτ : 0 < τ) {p q : ℝ} (h : q ≤ p) : Gk n τ p ≤ Gk n τ q := by
  unfold Gk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [div_le_div_iff_of_pos_right (show (0:ℝ) < 4 * τ by positivity)]
  linarith

/-- **★ THE SCALED-ARGUMENT IDENTITY.**  A Gaussian evaluated at a scaled radius-square `s·r²`
    equals a rescaled-width plain Gaussian with a bounded prefactor:
      `Gk n τ (s · rncRadialSq z) = (√s)⁻ⁿ · gaussDdim (τ/s) z`   (`s, τ > 0`).
    The prefactor `(√s)⁻ⁿ` absorbs the width change `τ ↦ τ/s`, and the exponent matches since
    `−(s·r²)/(4τ) = −r²/(4(τ/s))`.  This is the workhorse for both the two-sided squeeze (B1 inner)
    and the coarse chart-tail domination (B1 outer / integrability). -/
theorem Gk_scaled (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ) (z : Point n) :
    Gk n τ (s * rncRadialSq z) = (Real.sqrt s)⁻¹ ^ n * gaussDdim (τ / s) z := by
  have hsne : s ≠ 0 := hs.ne'
  have hτne : τ ≠ 0 := hτ.ne'
  unfold Gk
  rw [gaussDdim_eq_exp]
  have hexp : -(rncRadialSq z) / (4 * (τ / s)) = -(s * rncRadialSq z) / (4 * τ) := by
    field_simp
  have hpre : (Real.sqrt s)⁻¹ * (Real.sqrt (4 * Real.pi * (τ / s)))⁻¹
      = (Real.sqrt (4 * Real.pi * τ))⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul hs.le]
    congr 2
    field_simp
  rw [hexp, ← mul_assoc, ← mul_pow, hpre]

/-! ### The `𝓝[>] 0`-filter Gaussian tail limits. -/

/-- **The width-scaled Gaussian tail limit.**  For a fixed ball radius `ρ > 0` and width factor
    `c > 0`, `∫_{(ball ρ)ᶜ} gaussDdim (τ/c) → 0` as `τ → 0⁺`.  Squeeze against
    `n·√2·exp(−ρ²/(8(τ/c)))` (`gaussDdim_tail_le`), whose exponent `→ −∞`. -/
theorem tail_width_tendsto (ρ : ℝ) (hρ : 0 < ρ) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun τ : ℝ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hτcpos : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ / c := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact div_pos hτ hc
  have harg : Tendsto (fun τ : ℝ => -(ρ ^ 2) / (8 * (τ / c))) (𝓝[>] (0:ℝ)) atBot := by
    have hinv : Tendsto (fun τ : ℝ => τ⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have hmain : Tendsto (fun τ : ℝ => (-(ρ ^ 2 * c) / 8) * τ⁻¹) (𝓝[>] (0:ℝ)) atBot := by
      refine Tendsto.const_mul_atTop_of_neg ?_ hinv
      have : 0 < ρ ^ 2 * c := by positivity
      linarith
    refine (tendsto_congr' ?_).mpr hmain
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : τ ≠ 0 := (Set.mem_Ioi.mp hτ).ne'
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
  have hgtend : Tendsto
      (fun τ : ℝ => (n : ℝ) * (Real.sqrt 2 * Real.exp (-(ρ ^ 2) / (8 * (τ / c)))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hexp0 : Tendsto (fun τ : ℝ => Real.exp (-(ρ ^ 2) / (8 * (τ / c)))) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have : Tendsto (fun τ : ℝ => (n : ℝ) * (Real.sqrt 2 * Real.exp (-(ρ ^ 2) / (8 * (τ / c)))))
        (𝓝[>] (0:ℝ)) (𝓝 ((n : ℝ) * (Real.sqrt 2 * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul hexp0)
    simpa using this
  refine squeeze_zero' ?_ ?_ hgtend
  · filter_upwards [hτcpos] with τ hτc
    exact setIntegral_nonneg measurableSet_ball.compl (fun z _ => gaussDdim_nonneg _ z)
  · filter_upwards [hτcpos] with τ hτc
    exact gaussDdim_tail_le ρ (τ / c) hρ hτc

/-- **The plain Gaussian tail limit** `∫_{(ball ρ)ᶜ} gaussDdim τ → 0` as `τ → 0⁺` (the `c = 1`
    specialization of `tail_width_tendsto`). -/
theorem tail_plain_tendsto (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun τ : ℝ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have heq : (fun τ : ℝ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z)
      = (fun τ : ℝ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / 1) z) := by
    funext τ; rw [div_one]
  rw [heq]; exact tail_width_tendsto ρ hρ 1 one_pos

/-! ### Per-`τ` integrability of the chart Gaussian difference on `S`. -/

/-- **The chart-difference is integrable on the active set.**  For each `τ > 0`,
    `z ↦ gaussDdim τ (W z) − gaussDdim τ z` is integrable over `S`: the chart-pushed Gaussian is
    dominated on `S` by the coarse bound `gaussDdim τ (W z) ≤ (√c)⁻ⁿ · gaussDdim (τ/c) z`
    (`hcoarseP` + `Gk_anti` + `Gk_scaled`), and the plain Gaussian is integrable outright. -/
theorem chartDiff_integrableOn (S : Set (Point n)) (hS : MeasurableSet S) (W : Point n → Point n)
    (τ : ℝ) (hτ : 0 < τ) (c : ℝ) (hc0 : 0 < c)
    (hWmeas : AEStronglyMeasurable (fun z : Point n => gaussDdim τ (W z)) (volume.restrict S))
    (hcoarseP : ∀ z ∈ S, c * rncRadialSq z ≤ rncRadialSq (W z)) :
    IntegrableOn (fun z : Point n => gaussDdim τ (W z) - gaussDdim τ z) S volume := by
  have hWint : IntegrableOn (fun z : Point n => gaussDdim τ (W z)) S volume := by
    have hdom : Integrable (fun z : Point n => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z) volume :=
      (gaussDdim_integrable (τ / c) (div_pos hτ hc0)).const_mul _
    refine Integrable.mono' hdom.integrableOn hWmeas ?_
    rw [ae_restrict_iff' hS]
    refine ae_of_all _ (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussDdim_nonneg _ _)]
    calc gaussDdim τ (W z) = Gk n τ (rncRadialSq (W z)) := gaussDdim_eq_Gk τ (W z)
      _ ≤ Gk n τ (c * rncRadialSq z) := Gk_anti τ hτ (hcoarseP z hz)
      _ = (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z := Gk_scaled c τ hc0 hτ z
  exact hWint.sub ((gaussDdim_integrable τ hτ).integrableOn)

/-! ### B1 — the L¹ chart-to-plain Gaussian kernel replacement. -/

/-- **★★★ B1 — THE L¹ KERNEL-REPLACEMENT ADAPTER.**  Under the chart near-isometry hypotheses
    (`hcoarse` coarse lower bound, `hasymp` asymptotic two-sided squeeze) and base measurability
    `hWmeas`, the chart-image Gaussian and the plain Gaussian are L¹-close as `τ → 0⁺`:
        `∫_S |gaussDdim τ (W z) − gaussDdim τ z|  →  0`.
    PROOF (two-stage `ε`, NO diagonal).  Given `η`: (1) pick `δ` with
    `(√(1−δ))⁻ⁿ − (√(1+δ))⁻ⁿ < η/2` (continuity at `0`); (2) get `r` from `hasymp`, set `ρ = r/√n`;
    (3) on the ball `ball ρ ⊆ {r² < r²}` both Gaussians lie in `[Lz, Uz]` with
    `∫(Uz − Lz) = (√(1−δ))⁻ⁿ − (√(1+δ))⁻ⁿ < η/2`; (4) off the ball the coarse tail terms
    `(√c)⁻ⁿ∫_{ballᶜ}gaussDdim(τ/c) + ∫_{ballᶜ}gaussDdim τ` are eventually `< η/4 + η/4`. -/
theorem chartGauss_l1_sub_plain_tendsto
    (S : Set (Point n)) (hS : MeasurableSet S) (W : Point n → Point n)
    (hWmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun z : Point n => gaussDdim τ (W z)) (volume.restrict S))
    (hcoarse : ∃ c > 0, ∀ z ∈ S, c * rncRadialSq z ≤ rncRadialSq (W z))
    (hasymp : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ r > 0, ∀ z ∈ S, rncRadialSq z < r ^ 2 →
        (1 - δ) * rncRadialSq z ≤ rncRadialSq (W z) ∧ rncRadialSq (W z) ≤ (1 + δ) * rncRadialSq z) :
    Tendsto (fun τ => ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: `gaussDdim ≡ 1`, difference vanishes identically.
    subst hn0
    have hg : ∀ (t : ℝ) (v : Point 0), gaussDdim t v = 1 := by intro t v; simp [gaussDdim]
    simp only [hg, sub_self, abs_zero, integral_zero]
    exact tendsto_const_nhds
  obtain ⟨c, hc0, hcoarseP⟩ := hcoarse
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  refine NormedAddCommGroup.tendsto_nhds_zero.mpr ?_
  intro η hη
  -- STAGE 1: choose δ small.
  have hφ : Tendsto (fun δ : ℝ => (Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n)
      (𝓝 (0:ℝ)) (𝓝 0) := by
    have hc1 : ContinuousAt (fun δ : ℝ => (Real.sqrt (1 - δ))⁻¹ ^ n) 0 := by
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt
      · simp
    have hc2 : ContinuousAt (fun δ : ℝ => (Real.sqrt (1 + δ))⁻¹ ^ n) 0 := by
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt
      · simp
    have := (hc1.sub hc2).tendsto
    simpa using this
  have hφW : Tendsto (fun δ : ℝ => (Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n)
      (𝓝[>] (0:ℝ)) (𝓝 0) := hφ.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ),
      (Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n < η / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hφW (η / 2) (by linarith)] with δ hδ
    rw [Real.dist_eq, sub_zero] at hδ
    exact lt_of_le_of_lt (le_abs_self _) hδ
  have hev1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
  obtain ⟨δ, ⟨hδsmall, hδ1⟩, hδpos⟩ :
      ∃ δ, ((Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n < η / 2 ∧ δ < 1)
        ∧ δ ∈ Set.Ioi (0:ℝ) :=
    ((hev.and hev1).and self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδpos
  -- STAGE 2: get `r` and set `ρ = r/√n`.
  obtain ⟨r, hr0, hasympP⟩ := hasymp δ hδ0 hδ1
  set ρ : ℝ := r / Real.sqrt n with hρ_def
  have hρ0 : 0 < ρ := div_pos hr0 hsn
  have hsqn : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hnRne : (n : ℝ) ≠ 0 := hnR.ne'
  have hρ2 : (n : ℝ) * ρ ^ 2 = r ^ 2 := by
    rw [hρ_def, div_pow, hsqn]; field_simp
  -- `ball ρ ⊆ {r² < r²}`.
  have hrnsq_lt : ∀ z ∈ Metric.ball (0 : Point n) ρ, rncRadialSq z < r ^ 2 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hbound : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := by
      rw [rncRadialSq]
      calc ∑ k, (z k) ^ 2 ≤ ∑ _k : Fin n, ‖z‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro k _
            have hzk : |z k| ≤ ‖z‖ := by
              have := norm_le_pi_norm z k; rwa [Real.norm_eq_abs] at this
            nlinarith [abs_nonneg (z k), sq_abs (z k), norm_nonneg z]
        _ = (n : ℝ) * ‖z‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hzsq : ‖z‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg z, hρ0]
    calc rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := hbound
      _ < (n : ℝ) * ρ ^ 2 := by nlinarith [hnR]
      _ = r ^ 2 := hρ2
  -- the two tail limits, eventually `< η/4`.
  have hfC : Tendsto (fun τ : ℝ => (Real.sqrt c)⁻¹ ^ n
      * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (tail_width_tendsto ρ hρ0 c hc0).const_mul ((Real.sqrt c)⁻¹ ^ n)
  have hf1 : Tendsto (fun τ : ℝ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := tail_plain_tendsto ρ hρ0
  have eC := Metric.tendsto_nhds.mp hfC (η / 4) (by linarith)
  have e1 := Metric.tendsto_nhds.mp hf1 (η / 4) (by linarith)
  -- assemble on the eventual filter.
  filter_upwards [eC, e1, self_mem_nhdsWithin] with τ hτeC hτe1 hτmem
  have hτ0 : (0:ℝ) < τ := Set.mem_Ioi.mp hτmem
  -- the two interval helpers.
  have hUpper : ∀ (z v : Point n), (1 - δ) * rncRadialSq z ≤ rncRadialSq v →
      gaussDdim τ v ≤ (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z := by
    intro z v hv
    rw [gaussDdim_eq_Gk τ v]
    calc Gk n τ (rncRadialSq v) ≤ Gk n τ ((1 - δ) * rncRadialSq z) := Gk_anti τ hτ0 hv
      _ = (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z :=
          Gk_scaled (1 - δ) τ (by linarith) hτ0 z
  have hLower : ∀ (z v : Point n), rncRadialSq v ≤ (1 + δ) * rncRadialSq z →
      (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z ≤ gaussDdim τ v := by
    intro z v hv
    rw [gaussDdim_eq_Gk τ v, ← Gk_scaled (1 + δ) τ (by linarith) hτ0 z]
    exact Gk_anti τ hτ0 hv
  have hULnn : ∀ z : Point n,
      0 ≤ (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
          - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z := by
    intro z
    have hzz : rncRadialSq z ≤ (1 + δ) * rncRadialSq z := by
      nlinarith [rncRadialSq_nonneg z, hδ0]
    have hU := hUpper z z (by nlinarith [rncRadialSq_nonneg z, hδ0])
    have hL := hLower z z hzz
    linarith
  -- integrability of the majorant and the difference.
  have hUint : Integrable (fun z : Point n =>
      (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z) volume :=
    (gaussDdim_integrable (τ / (1 - δ)) (div_pos hτ0 (by linarith))).const_mul _
  have hLint : Integrable (fun z : Point n =>
      (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z) volume :=
    (gaussDdim_integrable (τ / (1 + δ)) (div_pos hτ0 (by linarith))).const_mul _
  have hUmLint : Integrable (fun z : Point n =>
      (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
        - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z) volume := hUint.sub hLint
  have hfar_base_int : Integrable (fun z : Point n =>
      (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) volume :=
    ((gaussDdim_integrable (τ / c) (div_pos hτ0 hc0)).const_mul _).add (gaussDdim_integrable τ hτ0)
  set bnd : Point n → ℝ := fun z =>
    ((Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
        - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z)
      + (Metric.ball (0 : Point n) ρ)ᶜ.indicator
          (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) z with hbnd_def
  have hfar_int : Integrable
      ((Metric.ball (0 : Point n) ρ)ᶜ.indicator
        (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z)) volume :=
    hfar_base_int.indicator measurableSet_ball.compl
  have hbnd_int : Integrable bnd volume := by rw [hbnd_def]; exact hUmLint.add hfar_int
  have hdiffabs_int : IntegrableOn (fun z => |gaussDdim τ (W z) - gaussDdim τ z|) S volume :=
    (chartDiff_integrableOn S hS W τ hτ0 c hc0 (hWmeas τ) hcoarseP).abs
  -- POINTWISE BOUND on `S`.
  have hpt : ∀ z ∈ S, |gaussDdim τ (W z) - gaussDdim τ z| ≤ bnd z := by
    intro z hz
    simp only [hbnd_def]
    by_cases hzb : z ∈ Metric.ball (0 : Point n) ρ
    · -- inner: indicator `= 0`, use the two-sided squeeze.
      have hrz : rncRadialSq z < r ^ 2 := hrnsq_lt z hzb
      obtain ⟨hlo, hhi⟩ := hasympP z hz hrz
      have hzzu : (1 - δ) * rncRadialSq z ≤ rncRadialSq z := by
        nlinarith [rncRadialSq_nonneg z, hδ0]
      have hzzl : rncRadialSq z ≤ (1 + δ) * rncRadialSq z := by
        nlinarith [rncRadialSq_nonneg z, hδ0]
      have hd1 : |gaussDdim τ (W z) - gaussDdim τ z|
          ≤ (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
              - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith [hLower z (W z) hhi, hUpper z z hzzu]
        · linarith [hUpper z (W z) hlo, hLower z z hzzl]
      rw [Set.indicator_of_notMem (by simpa using hzb), add_zero]
      exact hd1
    · -- outer: indicator `= (√c)⁻ⁿgaussDdim(τ/c) + gaussDdim τ`, use the coarse bound.
      have hd2 : |gaussDdim τ (W z) - gaussDdim τ z|
          ≤ (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z := by
        have hWc : gaussDdim τ (W z) ≤ (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z := by
          rw [gaussDdim_eq_Gk τ (W z)]
          calc Gk n τ (rncRadialSq (W z)) ≤ Gk n τ (c * rncRadialSq z) :=
                Gk_anti τ hτ0 (hcoarseP z hz)
            _ = (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z := Gk_scaled c τ hc0 hτ0 z
        calc |gaussDdim τ (W z) - gaussDdim τ z|
            = |gaussDdim τ (W z) + (- gaussDdim τ z)| := by rw [sub_eq_add_neg]
          _ ≤ |gaussDdim τ (W z)| + |(- gaussDdim τ z)| := abs_add_le _ _
          _ = gaussDdim τ (W z) + gaussDdim τ z := by
              rw [abs_neg, abs_of_nonneg (gaussDdim_nonneg _ _), abs_of_nonneg (gaussDdim_nonneg _ _)]
          _ ≤ (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z := by linarith
      rw [Set.indicator_of_mem (by simpa using hzb)]
      have := hULnn z
      linarith
  -- the final estimate.
  have hFbound : ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z| ≤ ∫ z in S, bnd z :=
    setIntegral_mono_on hdiffabs_int hbnd_int.integrableOn hS hpt
  have hsplit : ∫ z in S, bnd z
      = (∫ z in S, ((Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
              - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z))
        + ∫ z in S, (Metric.ball (0 : Point n) ρ)ᶜ.indicator
            (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) z := by
    rw [hbnd_def]
    exact integral_add hUmLint.integrableOn hfar_int.integrableOn
  have hb1 : (∫ z in S, ((Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
          - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z))
      ≤ (Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n := by
    calc (∫ z in S, ((Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
              - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z))
        ≤ ∫ z, ((Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z
              - (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z) :=
          setIntegral_le_integral hUmLint (ae_of_all _ hULnn)
      _ = (∫ z, (Real.sqrt (1 - δ))⁻¹ ^ n * gaussDdim (τ / (1 - δ)) z)
            - ∫ z, (Real.sqrt (1 + δ))⁻¹ ^ n * gaussDdim (τ / (1 + δ)) z :=
          integral_sub hUint hLint
      _ = (Real.sqrt (1 - δ))⁻¹ ^ n * 1 - (Real.sqrt (1 + δ))⁻¹ ^ n * 1 := by
          rw [integral_const_mul, integral_const_mul,
            gaussDdim_integral_eq_one _ (div_pos hτ0 (by linarith)),
            gaussDdim_integral_eq_one _ (div_pos hτ0 (by linarith))]
      _ = (Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n := by ring
  have hb2 : (∫ z in S, (Metric.ball (0 : Point n) ρ)ᶜ.indicator
          (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) z)
      ≤ (Real.sqrt c)⁻¹ ^ n * (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z)
        + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z := by
    calc (∫ z in S, (Metric.ball (0 : Point n) ρ)ᶜ.indicator
              (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) z)
        ≤ ∫ z, (Metric.ball (0 : Point n) ρ)ᶜ.indicator
              (fun z => (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) z :=
          setIntegral_le_integral hfar_int
            (ae_of_all _ (fun z => Set.indicator_nonneg
              (fun z _ => add_nonneg (mul_nonneg (by positivity) (gaussDdim_nonneg _ _))
                (gaussDdim_nonneg _ _)) z))
      _ = ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ,
              ((Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z + gaussDdim τ z) :=
          integral_indicator measurableSet_ball.compl
      _ = (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, (Real.sqrt c)⁻¹ ^ n * gaussDdim (τ / c) z)
            + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z :=
          integral_add ((gaussDdim_integrable (τ / c) (div_pos hτ0 hc0)).const_mul _).integrableOn
            (gaussDdim_integrable τ hτ0).integrableOn
      _ = (Real.sqrt c)⁻¹ ^ n * (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z)
            + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z := by
          rw [integral_const_mul]
  have hFnn : 0 ≤ ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z| :=
    setIntegral_nonneg hS (fun z _ => abs_nonneg _)
  have hscaled_nn : 0 ≤ (Real.sqrt c)⁻¹ ^ n
      * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z :=
    mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_ball.compl (fun z _ => gaussDdim_nonneg _ z))
  have hplain_nn : 0 ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z :=
    setIntegral_nonneg measurableSet_ball.compl (fun z _ => gaussDdim_nonneg _ z)
  have hCbd : (Real.sqrt c)⁻¹ ^ n
      * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z < η / 4 := by
    have := hτeC; rw [Real.dist_eq, sub_zero, abs_of_nonneg hscaled_nn] at this; exact this
  have h1bd : (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z) < η / 4 := by
    have := hτe1; rw [Real.dist_eq, sub_zero, abs_of_nonneg hplain_nn] at this; exact this
  rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
  calc ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z|
      ≤ ∫ z in S, bnd z := hFbound
    _ = _ := hsplit
    _ ≤ ((Real.sqrt (1 - δ))⁻¹ ^ n - (Real.sqrt (1 + δ))⁻¹ ^ n)
          + ((Real.sqrt c)⁻¹ ^ n * (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (τ / c) z)
            + ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim τ z) := add_le_add hb1 hb2
    _ < η := by linarith

/-! ### B2 — the bounded-multiplier corollary. -/

/-- **★★ B2 — THE BOUNDED-MULTIPLIER ADAPTER.**  The L¹ kernel difference tested against any family
    `F τ` that is EVENTUALLY uniformly bounded on `S` (`hFbd`) still vanishes as `τ → 0⁺`:
        `∫_S (gaussDdim τ (W z) − gaussDdim τ z)·F τ z  →  0`.
    Via `‖∫_S diff·F‖ ≤ M · ∫_S |diff|` (norm-of-integral + the sup bound) and `M · (B1) → 0`. -/
theorem chartGauss_l1_mul_bdd_tendsto
    (S : Set (Point n)) (hS : MeasurableSet S) (W : Point n → Point n)
    (hWmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun z : Point n => gaussDdim τ (W z)) (volume.restrict S))
    (hcoarse : ∃ c > 0, ∀ z ∈ S, c * rncRadialSq z ≤ rncRadialSq (W z))
    (hasymp : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ r > 0, ∀ z ∈ S, rncRadialSq z < r ^ 2 →
        (1 - δ) * rncRadialSq z ≤ rncRadialSq (W z) ∧ rncRadialSq (W z) ≤ (1 + δ) * rncRadialSq z)
    (F : ℝ → Point n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hFmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun z : Point n => F τ z) (volume.restrict S))
    (hFbd : ∀ᶠ τ in 𝓝[>] (0:ℝ), ∀ z ∈ S, |F τ z| ≤ M) :
    Tendsto (fun τ => ∫ z in S, (gaussDdim τ (W z) - gaussDdim τ z) * F τ z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨c, hc0, hcoarseP⟩ := hcoarse
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun τ => M * ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z|)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hB1 := chartGauss_l1_sub_plain_tendsto S hS W hWmeas ⟨c, hc0, hcoarseP⟩ hasymp
    simpa using hB1.const_mul M
  refine squeeze_zero' (Filter.Eventually.of_forall (fun τ => norm_nonneg _)) ?_ hg
  filter_upwards [hFbd, self_mem_nhdsWithin] with τ hFbdτ hτmem
  have hτ0 : (0:ℝ) < τ := Set.mem_Ioi.mp hτmem
  have hdiff_int := chartDiff_integrableOn S hS W τ hτ0 c hc0 (hWmeas τ) hcoarseP
  have hprodint : IntegrableOn
      (fun z => (gaussDdim τ (W z) - gaussDdim τ z) * F τ z) S volume := by
    refine Integrable.mono' (hdiff_int.norm.const_mul M)
      (hdiff_int.aestronglyMeasurable.mul (hFmeas τ)) ?_
    rw [ae_restrict_iff' hS]
    refine ae_of_all _ (fun z hz => ?_)
    rw [norm_mul]
    calc ‖gaussDdim τ (W z) - gaussDdim τ z‖ * ‖F τ z‖
        ≤ ‖gaussDdim τ (W z) - gaussDdim τ z‖ * M :=
          mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hFbdτ z hz) (norm_nonneg _)
      _ = M * ‖gaussDdim τ (W z) - gaussDdim τ z‖ := by ring
  calc ‖∫ z in S, (gaussDdim τ (W z) - gaussDdim τ z) * F τ z‖
      ≤ ∫ z in S, ‖(gaussDdim τ (W z) - gaussDdim τ z) * F τ z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in S, M * ‖gaussDdim τ (W z) - gaussDdim τ z‖ := by
        refine setIntegral_mono_on hprodint.norm (hdiff_int.norm.const_mul M) hS (fun z hz => ?_)
        rw [norm_mul]
        calc ‖gaussDdim τ (W z) - gaussDdim τ z‖ * ‖F τ z‖
            ≤ ‖gaussDdim τ (W z) - gaussDdim τ z‖ * M :=
              mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hFbdτ z hz) (norm_nonneg _)
          _ = M * ‖gaussDdim τ (W z) - gaussDdim τ z‖ := by ring
    _ = M * ∫ z in S, ‖gaussDdim τ (W z) - gaussDdim τ z‖ := by rw [integral_const_mul]
    _ = M * ∫ z in S, |gaussDdim τ (W z) - gaussDdim τ z| := by simp only [Real.norm_eq_abs]

/-! ### B3 — the concrete repackage of the `N = 1` van-Vleck witness. -/

/-- The `τ`-free part of the on-gate amplitude of the concrete witness:
    `ũ₀ z = radialCutoff a b (W z 0) · Θ(W z 0)^{−1/2} · u₀(W z 0)`. -/
noncomputable def chartAmp0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z : Point n) : ℝ :=
  radialCutoff a b (uniformInverseChart g gi hC hK z 0)
    * vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2)
    * transportCoeff (transportOp (vanVleck g) g gi) 0 (uniformInverseChart g gi hC hK z 0)

/-- The `τ`-linear part of the on-gate amplitude of the concrete witness:
    `ũ₁ z = radialCutoff a b (W z 0) · Θ(W z 0)^{−1/2} · u₁(W z 0)`. -/
noncomputable def chartAmp1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z : Point n) : ℝ :=
  radialCutoff a b (uniformInverseChart g gi hC hK z 0)
    * vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2)
    * transportCoeff (transportOp (vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK z 0)

/-- **B3(i) — the affine-in-`τ` split of the on-gate amplitude.**  On the gate the concrete witness
    factors as `H_G τ 0 z = gaussDdim τ (W z 0) · (ũ₀ z + τ · ũ₁ z)`, the amplitude affine in `τ`. -/
theorem witness_amp_affine (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z) := by
  rw [vanVleckGatedWitness_zero_factor g gi hC hK S a b τ hz h0]
  simp only [chartAmp0, chartAmp1]
  ring

/-- **★ B3(iv) — THE DIFFERENCE-REDUCTION LEMMA.**  The gap between the concrete witness and the
    PLAIN synthetic kernel `gaussDdim τ z · (ũ₀ z + τ·ũ₁ z)` (which has the literal `hAnear` shape
    with `u₀ := ũ₀`) reduces EXACTLY to the chart Gaussian difference times the amplitude:
      `H_G τ 0 z − gaussDdim τ z·(ũ₀+τũ₁) = (gaussDdim τ (W z 0) − gaussDdim τ z)·(ũ₀+τũ₁)`.
    This is the multiplier shape consumed by `chartGauss_l1_mul_bdd_tendsto` (B2) — the bridge that
    reconciles the concrete chart-image Gaussian with the proven plain-`z` boundary interface. -/
theorem witness_sub_plain (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
        - gaussDdim τ z * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z)
      = (gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z)
        * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z) := by
  rw [witness_amp_affine g gi hC hK S a b τ hz h0]
  ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.Gk_scaled
#print axioms QIQTH.HeatResidualBound.chartDiff_integrableOn
#print axioms QIQTH.HeatResidualBound.chartGauss_l1_sub_plain_tendsto
#print axioms QIQTH.HeatResidualBound.chartGauss_l1_mul_bdd_tendsto
#print axioms QIQTH.HeatResidualBound.witness_amp_affine
#print axioms QIQTH.HeatResidualBound.witness_sub_plain
