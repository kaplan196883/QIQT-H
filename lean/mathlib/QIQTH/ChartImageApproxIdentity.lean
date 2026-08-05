/-
  ChartImageApproxIdentity — J4-268: the moving approximate identity (Layer C of the
  chart-image approximate-identity plan).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  The remaining analytic obstruction on the W1
  side is the *chart-image approximate identity*: after pushing the heat integrand through a
  normal chart, one must show that a Gaussian family sampled against a *moving* (τ-dependent)
  integrand `g τ`, defined only on the chart image `Ω`, still concentrates at the origin as the
  width `τ ↓ 0`.  An external architecture consult split this into three layers:

    • LAYER A — a *set-integral rewrite* of the concrete boundary witness onto the gate `S`, with
      the factorization `Wit τ 0 z = gaussDdim τ (W₀ z) · A τ z` on-gate and vanishing off-gate.
    • LAYER B — the *change of variables* `w = W₀ z` turning the gate integral into a genuine
      `∫ w in Ω, gaussDdim τ w · (…)` over the chart image `Ω` (a LATER brick — NOT here).
    • LAYER C — a *self-contained, chart-free* generic lemma: the set-valued MOVING approximate
      identity for the flat `d`-dim Gaussian.  ★ THIS FILE = LAYER C. ★

  WHAT LANDS (Layer C, chart-free pure Gaussian analysis).
    `gaussDdim_set_approx_identity_moving` — for `Ω` a measurable neighbourhood of `0` and a moving
    family `g : ℝ → Point n → ℝ` that is (eventually) a.e.-measurable and a.e.-bounded on `Ω` and
    approaches a common value `L` *jointly* near the origin (`hlocal`), the Gaussian sampling
    converges:
        `∫ w in Ω, gaussDdim τ w · g τ w  →  L`   as `τ ↓ 0`.
    Plus the two independently-reusable sub-lemmas it rests on:
      - `gaussDdim_set_mass_tendsto_one`         — MASS NORMALIZATION: `∫ w in Ω, G_τ → 1`;
      - `gaussDdim_ballCompl_mass_tendsto_zero`  — TAIL: `∫ w in (ball 0 r)ᶜ, G_τ → 0`;
      - `gaussDdim_setIntegral_le_one`           — set mass ≤ 1;
      - `gaussDdim_set_moving_dist_bound`        — the fixed-`τ` 3-term `dist`-estimate.

  ⚠ WHY THIS IS A 3ε / CONCENTRATION ARGUMENT, NOT DOMINATED CONVERGENCE.  The Gaussian family has
  NO fixed integrable dominator as `τ ↓ 0` (mass 1 concentrating at a point), and pointwise
  convergence + a uniform bound would NOT suffice (the `h(w/√τ)` spike counterexample).  The proof
  splits `Ω = (Ω ∩ ball 0 r) ⊍ (Ω \ ball 0 r)`, controls the near part by `hlocal` against mass ≤ 1
  and the far part by the boundedness against the vanishing Gaussian tail, and normalizes with the
  mass → 1 fact.  The JOINT form of `hlocal` (a.e.-on-`w`, eventually-in-`τ`) is essential and is
  NOT weakened.

  Both `gaussDdim_set_mass_tendsto_one` and `gaussDdim_ballCompl_mass_tendsto_zero` are obtained by
  feeding an *indicator of a fixed set* to the banked plain approximate identity
  `QIQTH.GaussianApproxIdentity.gaussDdim_approx_identity` (J4-208): `Ω.indicator 1` is eventually
  `1` near `0` (so continuous at `0` with value `1`), and `(ball 0 r)ᶜ.indicator 1` is eventually
  `0` near `0` (value `0`).

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`.  This is ONE analytic brick (Layer C).  No `sorry`, no new
  axioms, no `:= True`, no vacuous/conclusion-in-disguise hypotheses (`hmeas`/`hbound`/`hlocal` are
  genuinely weaker than the conclusion — they are a.e./eventual, not the limit itself).  RESIDUAL
  toward the concrete `hBoundaryLim`: Layer B (the `w = W₀ z` change of variables) and the concrete
  instantiation of `g τ` from the witness amplitude are SEPARATE, later bricks.
-/
import Mathlib
import QIQTH.GaussianApproxIdentity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open scoped Topology

namespace QIQTH.ChartImageApproxIdentity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Sub-lemma 0. The set mass of the Gaussian is `≤ 1`. -/

/-- **SET MASS ≤ 1.**  For `τ > 0` and any set `s`, the flat Gaussian mass over `s` is at most the
    total mass `1`: `∫ w in s, gaussDdim τ w ≤ 1`.  (Nonneg integrand, monotone in the set.) -/
theorem gaussDdim_setIntegral_le_one (τ : ℝ) (hτ : 0 < τ) (s : Set (Point n)) :
    (∫ w in s, gaussDdim τ w) ≤ 1 := by
  calc (∫ w in s, gaussDdim τ w)
      ≤ ∫ w : Point n, gaussDdim τ w :=
        setIntegral_le_integral (QIQTH.HeatResidualBound.gaussDdim_integrable τ hτ)
          (ae_of_all _ (fun w => QIQTH.ResidueBound.gaussDdim_nonneg τ w))
    _ = 1 := QIQTH.HeatResidualBound.gaussDdim_integral_eq_one τ hτ

/-! ### Sub-lemma A. Mass normalization: `∫ w in Ω, G_τ → 1`. -/

/-- **MASS NORMALIZATION (`𝓝[>] 0` form).**  For `Ω` a measurable neighbourhood of `0`, the
    Gaussian mass over `Ω` tends to the total mass `1` as `τ ↓ 0`.  ROUTE: apply the banked plain
    approximate identity to `f := Ω.indicator 1`, which is bounded by `1`, `volume`-measurable, and
    continuous at `0` with value `1` (it is eventually `1` on the neighbourhood `Ω`); the sampled
    integral `∫ z, G_τ z · (Ω.indicator 1) z` equals `∫ w in Ω, G_τ w`. -/
theorem gaussDdim_set_mass_tendsto_one {Ω : Set (Point n)}
    (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n)) :
    Tendsto (fun τ => ∫ w in Ω, gaussDdim τ w) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h0mem : (0 : Point n) ∈ Ω := mem_of_mem_nhds hΩnhds
  have hcont : ContinuousAt (Ω.indicator (fun _ => (1 : ℝ))) 0 := by
    have heq : (fun _ : Point n => (1 : ℝ)) =ᶠ[𝓝 (0 : Point n)] Ω.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hΩnhds] with w hw
      rw [Set.indicator_of_mem hw]
    exact continuousAt_const.congr heq
  have hbd : ∀ z : Point n, |Ω.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z; by_cases hz : z ∈ Ω
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hmeas' : AEStronglyMeasurable (Ω.indicator (fun _ => (1 : ℝ))) volume :=
    aestronglyMeasurable_const.indicator hΩmeas
  have key := QIQTH.GaussianApproxIdentity.gaussDdim_approx_identity
    (Ω.indicator (fun _ => (1 : ℝ))) 1 hbd hcont hmeas'
  rw [show (Ω.indicator (fun _ => (1 : ℝ))) 0 = 1 from Set.indicator_of_mem h0mem _] at key
  have hEq : ∀ τ : ℝ,
      (∫ z : Point n, gaussDdim τ z * Ω.indicator (fun _ => (1 : ℝ)) z)
        = ∫ w in Ω, gaussDdim τ w := by
    intro τ
    rw [← integral_indicator hΩmeas]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Ω
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  exact key.congr' (Filter.Eventually.of_forall hEq)

/-! ### Sub-lemma B. Gaussian tail off a fixed ball: `∫ w in (ball 0 r)ᶜ, G_τ → 0`. -/

/-- **TAIL VANISHES OFF A FIXED BALL (`𝓝[>] 0` form).**  For `r > 0`, the Gaussian mass outside the
    ball of radius `r` tends to `0` as `τ ↓ 0`.  ROUTE: apply the banked plain approximate identity
    to `h := (ball 0 r)ᶜ.indicator 1`, which is bounded by `1`, `volume`-measurable, and continuous
    at `0` with value `0` (it is eventually `0` on the neighbourhood `ball 0 r`); the sampled
    integral equals `∫ w in (ball 0 r)ᶜ, G_τ w`. -/
theorem gaussDdim_ballCompl_mass_tendsto_zero (r : ℝ) (rpos : 0 < r) :
    Tendsto (fun τ => ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsmeas : MeasurableSet ((Metric.ball (0 : Point n) r)ᶜ) := measurableSet_ball.compl
  have h0notmem : (0 : Point n) ∉ (Metric.ball (0 : Point n) r)ᶜ := by
    simp only [Set.mem_compl_iff, not_not]; exact Metric.mem_ball_self rpos
  have hcont : ContinuousAt ((Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ))) 0 := by
    have hball : Metric.ball (0 : Point n) r ∈ 𝓝 (0 : Point n) := Metric.ball_mem_nhds 0 rpos
    have heq : (fun _ : Point n => (0 : ℝ))
        =ᶠ[𝓝 (0 : Point n)] (Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hball] with w hw
      have hwc : w ∉ (Metric.ball (0 : Point n) r)ᶜ := by
        simp only [Set.mem_compl_iff, not_not]; exact hw
      rw [Set.indicator_of_notMem hwc]
    exact continuousAt_const.congr heq
  have hbd : ∀ z : Point n,
      |(Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z; by_cases hz : z ∈ (Metric.ball (0 : Point n) r)ᶜ
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hmeas' : AEStronglyMeasurable
      ((Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ))) volume :=
    aestronglyMeasurable_const.indicator hsmeas
  have key := QIQTH.GaussianApproxIdentity.gaussDdim_approx_identity
    ((Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ))) 1 hbd hcont hmeas'
  rw [show ((Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ))) 0 = 0
      from Set.indicator_of_notMem h0notmem _] at key
  have hEq : ∀ τ : ℝ,
      (∫ z : Point n, gaussDdim τ z * (Metric.ball (0 : Point n) r)ᶜ.indicator (fun _ => (1 : ℝ)) z)
        = ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w := by
    intro τ
    rw [← integral_indicator hsmeas]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ (Metric.ball (0 : Point n) r)ᶜ
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  exact key.congr' (Filter.Eventually.of_forall hEq)

/-! ### The fixed-`τ` three-term distance estimate. -/

/-- **FIXED-`τ` `dist` ESTIMATE (the core near/far split).**  For a single width `τ > 0` and a
    single-time integrand `g` on `Ω`, a.e.-measurable, a.e.-bounded by `C`, and a.e. `ε'`-close to
    `L` on the ball of radius `r`, the Gaussian sampling deviates from `L` by at most three explicit
    pieces:
        `dist (∫ w in Ω, G_τ w · g w) L`
          `≤ (ε' + (|C|+|L|)·∫_{(ball 0 r)ᶜ} G_τ) + |L|·|∫_Ω G_τ − 1|`.
    Decompose `∫_Ω G_τ g − L = ∫_Ω G_τ (g − L) + L·(∫_Ω G_τ − 1)`; bound `|∫_Ω G_τ (g − L)|` by
    `∫_Ω G_τ |g − L|`, split at `ball 0 r` into a near part (`≤ ε'` via `hgl` against set-mass ≤ 1)
    and a far part (`≤ (|C|+|L|)·` tail via `hgb`).  Pure fixed-`τ` inequalities — no limits.  NOT
    `a₁ = R/6`. -/
theorem gaussDdim_set_moving_dist_bound
    {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω)
    (τ : ℝ) (hτ : 0 < τ) {g : Point n → ℝ} {L C ε' r : ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict Ω))
    (hgb : ∀ᵐ w ∂(volume.restrict Ω), ‖g w‖ ≤ C)
    (hgl : ∀ᵐ w ∂(volume.restrict Ω), ‖w‖ < r → ‖g w - L‖ < ε')
    (hε'0 : 0 ≤ ε') :
    dist (∫ w in Ω, gaussDdim τ w * g w) L
      ≤ (ε' + (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w)
        + |L| * |(∫ w in Ω, gaussDdim τ w) - 1| := by
  classical
  -- base integrabilities
  have hGμ : IntegrableOn (fun w : Point n => gaussDdim τ w) Ω volume :=
    (QIQTH.HeatResidualBound.gaussDdim_integrable τ hτ).integrableOn
  have hgmL : ∀ᵐ w ∂(volume.restrict Ω), ‖g w - L‖ ≤ |C| + |L| := by
    filter_upwards [hgb] with w hw
    calc ‖g w - L‖ ≤ ‖g w‖ + ‖L‖ := norm_sub_le _ _
      _ ≤ |C| + |L| := by
          have h1 : ‖g w‖ ≤ |C| := le_trans hw (le_abs_self C)
          have h2 : ‖L‖ ≤ |L| := le_of_eq (Real.norm_eq_abs L)
          linarith
  have hGgLμ : IntegrableOn (fun w : Point n => gaussDdim τ w * (g w - L)) Ω volume :=
    Integrable.mul_bdd hGμ (hgm.sub aestronglyMeasurable_const) hgmL
  have hGLμ : IntegrableOn (fun w : Point n => gaussDdim τ w * L) Ω volume :=
    Integrable.mul_const hGμ L
  have hnormbd : ∀ᵐ w ∂(volume.restrict Ω), ‖‖g w - L‖‖ ≤ |C| + |L| := by
    filter_upwards [hgmL] with w hw
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hFabsμ : IntegrableOn (fun w : Point n => gaussDdim τ w * ‖g w - L‖) Ω volume :=
    Integrable.mul_bdd hGμ ((hgm.sub aestronglyMeasurable_const).norm) hnormbd
  -- decomposition `∫_Ω G g = ∫_Ω G (g−L) + ∫_Ω G L`
  have hsplit : (∫ w in Ω, gaussDdim τ w * g w)
      = (∫ w in Ω, gaussDdim τ w * (g w - L)) + (∫ w in Ω, gaussDdim τ w * L) := by
    have hadd : (∫ w in Ω, gaussDdim τ w * (g w - L)) + (∫ w in Ω, gaussDdim τ w * L)
        = ∫ w in Ω, (gaussDdim τ w * (g w - L) + gaussDdim τ w * L) :=
      (integral_add hGgLμ hGLμ).symm
    rw [hadd]
    apply integral_congr_ae
    filter_upwards with w
    ring
  have hGL : (∫ w in Ω, gaussDdim τ w * L) = L * (∫ w in Ω, gaussDdim τ w) := by
    rw [integral_mul_const]; ring
  -- `|∫_Ω G (g−L)| ≤ ∫_Ω G |g−L|`
  have hJabs : |∫ w in Ω, gaussDdim τ w * (g w - L)|
      ≤ ∫ w in Ω, gaussDdim τ w * ‖g w - L‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ w in Ω, gaussDdim τ w * (g w - L)‖
        ≤ ∫ w in Ω, ‖gaussDdim τ w * (g w - L)‖ := norm_integral_le_integral_norm _
      _ = ∫ w in Ω, gaussDdim τ w * ‖g w - L‖ := by
          apply integral_congr_ae
          filter_upwards with w
          rw [norm_mul, Real.norm_of_nonneg (QIQTH.ResidueBound.gaussDdim_nonneg τ w)]
  -- near/far split of `∫_Ω G |g−L|`
  have hFsplit : (∫ w in Ω, gaussDdim τ w * ‖g w - L‖)
      = (∫ w in Ω ∩ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖)
        + (∫ w in Ω \ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖) :=
    (integral_inter_add_diff measurableSet_ball hFabsμ).symm
  -- near part ≤ ε'
  have hnear : (∫ w in Ω ∩ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖) ≤ ε' := by
    have hae : (fun w => gaussDdim τ w * ‖g w - L‖)
        ≤ᵐ[volume.restrict (Ω ∩ Metric.ball (0 : Point n) r)] (fun w => gaussDdim τ w * ε') := by
      have h1 := ae_restrict_of_ae_restrict_of_subset
        (Set.inter_subset_left : Ω ∩ Metric.ball (0 : Point n) r ⊆ Ω) hgl
      have h2 := ae_restrict_mem (μ := volume)
        (hΩmeas.inter (measurableSet_ball : MeasurableSet (Metric.ball (0 : Point n) r)))
      filter_upwards [h1, h2] with w hw1 hw2
      have hwr : ‖w‖ < r := mem_ball_zero_iff.1 hw2.2
      exact mul_le_mul_of_nonneg_left (hw1 hwr).le (QIQTH.ResidueBound.gaussDdim_nonneg τ w)
    calc (∫ w in Ω ∩ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖)
        ≤ ∫ w in Ω ∩ Metric.ball (0 : Point n) r, gaussDdim τ w * ε' :=
          setIntegral_mono_ae_restrict
            (hFabsμ.mono_set (Set.inter_subset_left))
            (Integrable.mul_const (hGμ.mono_set (Set.inter_subset_left)) ε') hae
      _ = (∫ w in Ω ∩ Metric.ball (0 : Point n) r, gaussDdim τ w) * ε' := integral_mul_const _ _
      _ ≤ 1 * ε' :=
          mul_le_mul_of_nonneg_right (gaussDdim_setIntegral_le_one τ hτ _) hε'0
      _ = ε' := one_mul _
  -- far part ≤ (|C|+|L|)·tail
  have hfar : (∫ w in Ω \ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖)
      ≤ (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w := by
    have hae : (fun w => gaussDdim τ w * ‖g w - L‖)
        ≤ᵐ[volume.restrict (Ω \ Metric.ball (0 : Point n) r)]
          (fun w => gaussDdim τ w * (|C| + |L|)) := by
      have h1 := ae_restrict_of_ae_restrict_of_subset
        (Set.diff_subset : Ω \ Metric.ball (0 : Point n) r ⊆ Ω) hgmL
      filter_upwards [h1] with w hw
      exact mul_le_mul_of_nonneg_left hw (QIQTH.ResidueBound.gaussDdim_nonneg τ w)
    have hsub : Ω \ Metric.ball (0 : Point n) r ⊆ (Metric.ball (0 : Point n) r)ᶜ :=
      fun w hw => hw.2
    calc (∫ w in Ω \ Metric.ball (0 : Point n) r, gaussDdim τ w * ‖g w - L‖)
        ≤ ∫ w in Ω \ Metric.ball (0 : Point n) r, gaussDdim τ w * (|C| + |L|) :=
          setIntegral_mono_ae_restrict (hFabsμ.mono_set (Set.diff_subset))
            (Integrable.mul_const (hGμ.mono_set (Set.diff_subset)) _) hae
      _ = (∫ w in Ω \ Metric.ball (0 : Point n) r, gaussDdim τ w) * (|C| + |L|) :=
          integral_mul_const _ _
      _ ≤ (∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w) * (|C| + |L|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact setIntegral_mono_set
            ((QIQTH.HeatResidualBound.gaussDdim_integrable τ hτ).integrableOn :
              IntegrableOn (fun w : Point n => gaussDdim τ w)
                ((Metric.ball (0 : Point n) r)ᶜ) volume)
            (ae_of_all _ (fun w => QIQTH.ResidueBound.gaussDdim_nonneg τ w))
            hsub.eventuallyLE
      _ = (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w := by ring
  -- assemble the `∫_Ω G (g−L)` bound
  have hJbound : |∫ w in Ω, gaussDdim τ w * (g w - L)|
      ≤ ε' + (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w := by
    calc |∫ w in Ω, gaussDdim τ w * (g w - L)|
        ≤ ∫ w in Ω, gaussDdim τ w * ‖g w - L‖ := hJabs
      _ = _ := hFsplit
      _ ≤ ε' + (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w :=
          add_le_add hnear hfar
  -- the algebraic identity `I − L = J + L·(mass − 1)`
  have hIL : (∫ w in Ω, gaussDdim τ w * g w) - L
      = (∫ w in Ω, gaussDdim τ w * (g w - L)) + L * ((∫ w in Ω, gaussDdim τ w) - 1) := by
    rw [hsplit, hGL]; ring
  calc dist (∫ w in Ω, gaussDdim τ w * g w) L
      = |(∫ w in Ω, gaussDdim τ w * g w) - L| := Real.dist_eq _ _
    _ = |(∫ w in Ω, gaussDdim τ w * (g w - L)) + L * ((∫ w in Ω, gaussDdim τ w) - 1)| := by rw [hIL]
    _ ≤ |∫ w in Ω, gaussDdim τ w * (g w - L)| + |L * ((∫ w in Ω, gaussDdim τ w) - 1)| :=
        abs_add_le _ _
    _ = |∫ w in Ω, gaussDdim τ w * (g w - L)| + |L| * |(∫ w in Ω, gaussDdim τ w) - 1| := by
        rw [abs_mul]
    _ ≤ (ε' + (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w)
          + |L| * |(∫ w in Ω, gaussDdim τ w) - 1| := by linarith [hJbound]

/-! ### Layer C. The set-valued MOVING approximate identity. -/

/-- **★★ J4-268 (LAYER C) — THE SET-VALUED MOVING GAUSSIAN APPROXIMATE IDENTITY.**  Let `Ω` be a
    measurable neighbourhood of the origin and `g : ℝ → Point n → ℝ` a moving integrand such that,
    eventually as `τ ↓ 0`:  `g τ` is a.e.-measurable on `Ω` (`hmeas`), a.e.-bounded on `Ω` by a
    fixed `C` (`hbound`), and approaches a common value `L` JOINTLY near the origin — for every
    `ε > 0` there is a radius `r` on which, eventually in `τ`, `‖g τ w − L‖ < ε` for a.e. `w`
    (`hlocal`).  Then the flat `d`-dim Gaussian samples the common value:
        `∫ w in Ω, gaussDdim τ w · g τ w  →  L`   in `𝓝[>] (0 : ℝ)`.

    PROOF (3ε / concentration, via `Metric.tendsto_nhds`).  For `ε > 0` set `ε' := ε/3` and take the
    `hlocal` radius `r`.  The fixed-`τ` estimate `gaussDdim_set_moving_dist_bound` gives, for every
    `τ` in the eventual set,
        `dist (∫_Ω G_τ g τ) L ≤ (ε' + (|C|+|L|)·tail_r τ) + |L|·|mass_Ω τ − 1|`.
    The tail `(|C|+|L|)·tail_r τ` is eventually `< ε'` (`gaussDdim_ballCompl_mass_tendsto_zero`), and
    the mass-defect `|L|·|mass_Ω τ − 1|` is eventually `< ε'` (`gaussDdim_set_mass_tendsto_one`), so
    the three pieces sum to `< 3ε' = ε`.

    ⚠ NOT `a₁ = R/6`.  This is the chart-FREE generic lemma (Layer C).  The JOINT `hlocal` is
    essential and unweakened; `hmeas`/`hbound` are genuine a.e./eventual inputs, not the conclusion. -/
theorem gaussDdim_set_approx_identity_moving
    {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n))
    {g : ℝ → Point n → ℝ} {L : ℝ}
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (g τ) (volume.restrict Ω))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ᵐ w ∂(volume.restrict Ω), ‖g τ w‖ ≤ C)
    (hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict Ω), ‖w‖ < r → ‖g τ w - L‖ < ε) :
    Tendsto (fun τ => ∫ w in Ω, gaussDdim τ w * g τ w) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨C, hCbound⟩ := hbound
  rw [Metric.tendsto_nhds]
  intro ε εpos
  set ε' : ℝ := ε / 3 with hε'
  have ε'pos : 0 < ε' := by rw [hε']; positivity
  obtain ⟨r, rpos, hlocalr⟩ := hlocal ε' ε'pos
  -- eventual smallness of the mass defect
  have hmassClose : ∀ᶠ τ in 𝓝[>] (0 : ℝ), |L| * |(∫ w in Ω, gaussDdim τ w) - 1| < ε' := by
    have hlim : Tendsto (fun τ => |L| * |(∫ w in Ω, gaussDdim τ w) - 1|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun τ => (∫ w in Ω, gaussDdim τ w) - 1) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (gaussDdim_set_mass_tendsto_one hΩmeas hΩnhds).sub_const 1
      have h2 : Tendsto (fun τ => |(∫ w in Ω, gaussDdim τ w) - 1|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using h1.abs
      simpa using tendsto_const_nhds.mul h2
    filter_upwards [hlim.eventually (Iio_mem_nhds ε'pos)] with τ hτ
    exact hτ
  -- eventual smallness of the tail
  have htailClose : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      (|C| + |L|) * (∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w) < ε' := by
    have hlim : Tendsto
        (fun τ => (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (gaussDdim_ballCompl_mass_tendsto_zero (n := n) r rpos).const_mul (|C| + |L|)
    filter_upwards [hlim.eventually (Iio_mem_nhds ε'pos)] with τ hτ
    exact hτ
  have hτpos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), (0 : ℝ) < τ :=
    eventually_mem_nhdsWithin.mono (fun τ h => h)
  filter_upwards [hmeas, hCbound, hlocalr, hmassClose, htailClose, hτpos]
    with τ hgm hgb hgl hmc htc hτ
  have hb := gaussDdim_set_moving_dist_bound hΩmeas τ hτ hgm hgb hgl ε'pos.le
  have hsum : ε' + ε' + ε' = ε := by rw [hε']; ring
  calc dist (∫ w in Ω, gaussDdim τ w * g τ w) L
      ≤ (ε' + (|C| + |L|) * ∫ w in (Metric.ball (0 : Point n) r)ᶜ, gaussDdim τ w)
        + |L| * |(∫ w in Ω, gaussDdim τ w) - 1| := hb
    _ < ε := by linarith [htc, hmc, hsum]

end QIQTH.ChartImageApproxIdentity

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.ChartImageApproxIdentity

#print axioms gaussDdim_setIntegral_le_one
#print axioms gaussDdim_set_mass_tendsto_one
#print axioms gaussDdim_ballCompl_mass_tendsto_zero
#print axioms gaussDdim_set_moving_dist_bound
#print axioms gaussDdim_set_approx_identity_moving

end AxiomChecks
