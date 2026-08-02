/-
  BoundaryAssembly — J4-120: the Brick-2 `hBoundary` DISCHARGE (4-way-split assembly).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `DeltaFamilyBoundary` (J4-118) reduced the singular `hDelta` carry of the diagonal
  Duhamel `hDConv` chain to the approximate-identity core plus TWO deferred inputs; `GaussianTailBoundary`
  (J4-119) discharged the Gaussian TAIL outright and built the parameter-uniform approximate-identity
  engine `tendstoUniformlyOn_integral_gaussDdim_smul_family` (T2u).  The remaining open frontier was
  Brick 2 (`hBoundary`): the moving-peak concentration
      `∫ z, A(ε_m) 0 z · B(u−ε_m) z 0  →  B(u) 0 0`   LOCALLY UNIFORMLY in `u`.
  This file DISCHARGES it (T3) by the 4-way split (MAIN / EPS / OFF-BALL / mass-defect handled by T2u).

  WHAT LANDS.
    (H0)  `heatKernel1D_le_diagonal` / `gaussDdim_le_diagonal` — the pointwise peak bound
          `gaussDdim t v ≤ gaussDdim t 0` (`exp(−x²/4t) ≤ 1`, `t>0`).  Combined with the width-antitone
          diagonal peak (`gaussDdim_zero_antitone`) this gives the `s`-uniform B-sup on a time strip.
    (H1)  `gaussDdim_zero_sub` — evenness at the origin: `gaussDdim t (0−z) = gaussDdim t z`.
    (H2)  `B_le_MB` — the `s`-UNIFORM B-SUP: for `a/2 ≤ s ≤ T`, `|B s z 0| ≤ C_L·gaussDdim a 0` (∀ z),
          from `hBdom` + the two peak monotonicities.
    (H3)  `integrableOn_gauss_mul_bddOn_ball` — `gaussDdim t · f` is integrable over `ball 0 r` when `f`
          is a.e.-measurable and bounded on the ball; the workhorse for the MAIN/EPS ball integrals.
    (T3)  `boundary_tendstoLocallyUniformlyOn` — ★ THE `hBoundary` DISCHARGE.  Reduce to compacts
          (`tendstoLocallyUniformlyOn_iff_forall_isCompact`, `U` open); on a compact `K` get a time floor
          `a>0` (`IsCompact.exists_isMinOn`); split `F = MAIN + EPS + OFF`; MAIN → `B u 0 0` uniformly via
          T2u with a clamped indicator family `h` and a Heine–Cantor equicontinuity witness
          (`IsCompact.uniformContinuousOn_of_continuous` on the strip `Icc (a/2) T ×ˢ closedBall 0 r₀`);
          `|EPS| ≤ ε·C₁·M_B → 0`; `|OFF| ≤ (A₀+A₁)·√(3/2)ⁿ·M_B·Tail_m → 0` (`gaussDdim_tail_tendsto_zero`).
    (CAP) `hDelta_gatedWitnessN1_final` — T3 plugged into `hDelta_gatedWitnessN1_of_boundary`: the full
          concrete `hDelta` with `hBoundary` GONE (conditional only on the carried geometric near-diagonal
          parametrix family + dominations + base measurability + `hDaLim`).

  ⚠ HONEST FIREWALL.
    LANDED (this file): the 4-way split assembly (T3) and its concrete corollary — the `hBoundary`
      brick is DISCHARGED given the inputs below.  The MAIN/EPS/OFF estimates, the Heine–Cantor
      equicontinuity, the compact reduction, and the time floor are all genuine landed content.
    CARRIED (labelled deferred inputs of T3, each a genuine fact, NONE the conclusion, none vacuous):
      • `hAnear` — the near-diagonal parametrix form `A τ 0 z = gaussDdim τ z·(u₀ z + τ·u₁ z)` on the ball
        (the geometric van-Vleck 2-jet fact; satisfiable by the concrete witness);
      • `hu₀cont`/`hu₀one`/`hu₀bdd`/`hu₁bdd` — leading-coefficient regularity (`u₀ 0 = 1`, continuity, ball
        bounds), the parametrix normalization;
      • `hAdom`/`hAzero`/`hBdom` — the D1/Levi Gaussian dominations (landed bounds carried parametrically);
      • `hBcont` — joint continuity of `B` on the time strip (the Levi-kernel regularity);
      • `hAmeas`/`hBmeas`/`hu₀meas`/`hu₁meas` — BASE measurability of the factors (deferred measurability
        family, consistent with J4-117/118/119).
    NO `sorry`, no new axioms, no `expRho` in statements.  NOT `a₁ = R/6` — this discharges ONE brick
    (Brick 2 / `hBoundary`) of the campaign.
-/
import Mathlib
import QIQTH.GaussianTailBoundary

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.ParametrixFunction QIQTH.TrueHeatKernel QIQTH.VanVleck
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### H0/H1. Pointwise peak bound and origin evenness. -/

/-- **(H0) 1-D peak bound.**  `heatKernel1D t x ≤ heatKernel1D t 0` for `t > 0`
    (`exp(−x²/4t) ≤ exp 0 = 1`, positive prefactor). -/
theorem heatKernel1D_le_diagonal (t x : ℝ) (ht : 0 < t) :
    heatKernel1D t x ≤ heatKernel1D t 0 := by
  rw [heatKernel1D, heatKernel1D]
  have hpre : 0 ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpre
  have h0 : Real.exp (-(0:ℝ) ^ 2 / (4 * t)) = 1 := by norm_num
  rw [h0]
  refine Real.exp_le_one_iff.mpr ?_
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg x]
  · positivity

/-- **(H0) d-dim peak bound.**  `gaussDdim t v ≤ gaussDdim t 0` for `t > 0`. -/
theorem gaussDdim_le_diagonal {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdim t v ≤ gaussDdim t (0 : Point n) := by
  simp only [gaussDdim, Pi.zero_apply]
  refine Finset.prod_le_prod (fun i _ => (heatKernel1D_pos t (v i) ht).le) (fun i _ => ?_)
  exact heatKernel1D_le_diagonal t (v i) ht

/-- **(H1) Origin evenness.**  `gaussDdim t (0−z) = gaussDdim t z`. -/
theorem gaussDdim_zero_sub (t : ℝ) (z : Point n) :
    gaussDdim t (0 - z) = gaussDdim t z := by
  simp only [gaussDdim]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have : (0 - z) i = -(z i) := by simp
  rw [this, heatKernel1D, heatKernel1D, neg_pow, neg_one_sq, one_mul]

/-! ### H2. The `s`-uniform B-sup on a time strip. -/

/-- **(H2) B-SUP ON A TIME STRIP.**  With the width-2 Gaussian domination `hBdom` and a time floor
    `a > 0`, for `a/2 ≤ s ≤ T` the boundary slice `|B s z 0|` is bounded, UNIFORMLY in `z`, by the
    `s`-free constant `C_L·gaussDdim a 0`: peak-bound `gaussDdim (2s) z ≤ gaussDdim (2s) 0` then
    width-antitone `gaussDdim (2s) 0 ≤ gaussDdim a 0` (since `a ≤ 2s`). -/
theorem B_le_MB (B : ℝ → Point n → Point n → ℝ) (C_L T a : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (ha : 0 < a) (s : ℝ) (hs : a / 2 ≤ s) (hsT : s ≤ T) (z : Point n) :
    |B s z 0| ≤ C_L * gaussDdim a (0 : Point n) := by
  have hs0 : 0 < s := by linarith
  have h2s : a ≤ 2 * s := by linarith
  calc |B s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0) := hBdom s hs0 hsT z 0
    _ = C_L * gaussDdim (2 * s) z := by rw [sub_zero]
    _ ≤ C_L * gaussDdim (2 * s) (0 : Point n) :=
        mul_le_mul_of_nonneg_left (gaussDdim_le_diagonal (by linarith) z) hC_L
    _ ≤ C_L * gaussDdim a (0 : Point n) :=
        mul_le_mul_of_nonneg_left (gaussDdim_zero_antitone ha h2s) hC_L

/-! ### H3. Integrability of `gaussDdim · (bounded-on-ball)` over the ball. -/

/-- **(H3) BALL INTEGRABILITY.**  For `t > 0`, `f` a.e.-measurable and `|f| ≤ M` on `ball 0 r`, the
    product `z ↦ gaussDdim t z · f z` is integrable over `ball 0 r` (dominated by the integrable
    `gaussDdim t · M`). -/
theorem integrableOn_gauss_mul_bddOn_ball (t : ℝ) (ht : 0 < t) (f : Point n → ℝ) (M r : ℝ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hfbd : ∀ z ∈ Metric.ball (0 : Point n) r, |f z| ≤ M) :
    IntegrableOn (fun z => gaussDdim t z * f z) (Metric.ball (0 : Point n) r) volume := by
  have hgint : Integrable (fun z : Point n => gaussDdim t z * M) volume :=
    (gaussDdim_integrable t ht).mul_const M
  refine Integrable.mono' hgint.integrableOn
    (((gaussDdim_integrable t ht).aestronglyMeasurable.mul hfmeas).restrict) ?_
  rw [ae_restrict_iff' measurableSet_ball]
  refine ae_of_all _ (fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg t z)]
  exact mul_le_mul_of_nonneg_left (hfbd z hz) (gaussDdim_nonneg t z)

/-! ### T3. The `hBoundary` discharge — the 4-way split assembly. -/

/-- **★★★ J4-120 (T3) — THE `hBoundary` DISCHARGE.**  The moving-peak concentration
      `∫ z, A(ε_m) 0 z · B(u−ε_m) z 0  →  B(u) 0 0`   LOCALLY UNIFORMLY on `U`,
    for the near-diagonal parametrix `A τ 0 z = gaussDdim τ z·(u₀ z + τ·u₁ z)` (`u₀ 0 = 1`) and the
    Gaussian-dominated Levi kernel `B`.  Reduce to compacts, get a time floor `a>0`, split
    `F = MAIN + EPS + OFF`; MAIN → `B u 0 0` uniformly by the parameter-uniform approximate identity
    (T2u) with a clamped indicator family and a Heine–Cantor equicontinuity witness on the strip
    `Icc (a/2) T ×ˢ closedBall 0 r₀`; `EPS`/`OFF` vanish uniformly (mass-one + Gaussian tail).
    ⚠ CONDITIONAL on the carried near-diagonal parametrix family (`hAnear`/`hu₀*`/`hu₁bdd`), the
    D1/Levi dominations (`hAdom`/`hBdom`), the Levi continuity `hBcont`, and base measurability
    (`hAmeas`/`hBmeas`/`hu₀meas`/`hu₁meas`).  NOT `a₁ = R/6` — this is ONE brick (Brick 2). -/
theorem boundary_tendstoLocallyUniformlyOn
    (A B : ℝ → Point n → Point n → ℝ) (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        A τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn (fun x : ℝ × Point n => B x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => B s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume)
    (hu₁meas : AEStronglyMeasurable u₁ volume) :
    TendstoLocallyUniformlyOn
      (fun m u => ∫ z, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
      (fun u => B u 0 0) atTop U := by
  classical
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen]
  intro K hKU hKcompact
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe; exact tendstoUniformlyOn_empty
  -- time floor
  obtain ⟨u_min, hu_minK, hu_minMin⟩ := hKcompact.exists_isMinOn hKne continuousOn_id
  set a : ℝ := u_min with ha_def
  have ha_pos : 0 < a := hUpos u_min (hKU hu_minK)
  have ha_floor : ∀ u ∈ K, a ≤ u := fun u hu => by simpa using isMinOn_iff.1 hu_minMin u hu
  have hKT : ∀ u ∈ K, u ≤ T := fun u hu => hUT u (hKU hu)
  -- constants
  have h0ball : (0 : Point n) ∈ Metric.ball (0 : Point n) r₀ := by
    simp [Metric.mem_ball, hr₀]
  have hC₀1 : (1 : ℝ) ≤ C₀ := by
    have := hu₀bdd 0 h0ball; rw [hu₀one] at this; simpa using this
  have hC₀0 : 0 ≤ C₀ := le_trans zero_le_one hC₀1
  have hC₁0 : 0 ≤ C₁ := le_trans (abs_nonneg _) (hu₁bdd 0 h0ball)
  set M_B : ℝ := C_L * gaussDdim a (0 : Point n) with hMB_def
  have hMB0 : 0 ≤ M_B := mul_nonneg hC_L (gaussDdim_nonneg _ _)
  have hBstrip : ∀ s, a / 2 ≤ s → s ≤ T → ∀ z : Point n, |B s z 0| ≤ M_B := by
    intro s hs hsT z; exact B_le_MB B C_L T a hC_L hBdom ha_pos s hs hsT z
  -- ε-sequences to `𝓝[>] 0`
  have hεpos_all : ∀ m, 0 < epsSeq m := epsSeq_pos
  have hεGT : Tendsto epsSeq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ epsSeq_tendsto
      (Filter.Eventually.of_forall (fun m => Set.mem_Ioi.2 (hεpos_all m)))
  have hε'tendsto : Tendsto (fun m => 3 / 2 * epsSeq m) atTop (𝓝 0) := by
    have := epsSeq_tendsto.const_mul (3 / 2 : ℝ); simpa using this
  have hε'GT : Tendsto (fun m => 3 / 2 * epsSeq m) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hε'tendsto
      (Filter.Eventually.of_forall (fun m => Set.mem_Ioi.2 (mul_pos (by norm_num) (hεpos_all m))))
  have hTail0 : Tendsto
      (fun m => ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z)
      atTop (𝓝 0) := gaussDdim_tail_tendsto_zero (fun m => 3 / 2 * epsSeq m) hε'GT r₀ hr₀
  -- the clamped indicator family
  set h : ℕ → ℝ → Point n → ℝ := fun m u z =>
    if (a / 2 ≤ u - epsSeq m ∧ u - epsSeq m ≤ T) then
      Set.indicator (Metric.ball (0 : Point n) r₀) (fun z => u₀ z * B (u - epsSeq m) z 0) z
    else 0
    with hh_def
  have hCbd : ∀ m (u : ℝ) (z : Point n), |h m u z| ≤ C₀ * M_B := by
    intro m u z
    by_cases hcond : (a / 2 ≤ u - epsSeq m ∧ u - epsSeq m ≤ T)
    · simp only [hh_def, if_pos hcond]
      by_cases hz : z ∈ Metric.ball (0 : Point n) r₀
      · rw [Set.indicator_of_mem hz, abs_mul]
        exact mul_le_mul (hu₀bdd z hz) (hBstrip (u - epsSeq m) hcond.1 hcond.2 z)
          (abs_nonneg _) hC₀0
      · rw [Set.indicator_of_notMem hz, abs_zero]; exact mul_nonneg hC₀0 hMB0
    · simp only [hh_def, if_neg hcond, abs_zero]; exact mul_nonneg hC₀0 hMB0
  have hmeas : ∀ m (u : ℝ), AEStronglyMeasurable (h m u) volume := by
    intro m u
    by_cases hcond : (a / 2 ≤ u - epsSeq m ∧ u - epsSeq m ≤ T)
    · simp only [hh_def, if_pos hcond]
      exact (hu₀meas.mul (hBmeas (u - epsSeq m))).indicator measurableSet_ball
    · simp only [hh_def, if_neg hcond]; exact aestronglyMeasurable_const
  have hφbd : ∀ u ∈ K, |B u 0 0| ≤ C₀ * M_B := by
    intro u hu
    have hstrip : |B u 0 0| ≤ M_B :=
      hBstrip u (by have := ha_floor u hu; linarith) (hKT u hu) 0
    calc |B u 0 0| ≤ M_B := hstrip
      _ = 1 * M_B := (one_mul _).symm
      _ ≤ C₀ * M_B := mul_le_mul_of_nonneg_right hC₀1 hMB0
  -- the Heine–Cantor equicontinuity witness
  have hEqui : ∀ η > 0, ∃ δ > 0, ∀ᶠ m in atTop,
      ∀ u ∈ K, ∀ z ∈ Metric.ball (0 : Point n) δ, |h m u z - B u 0 0| ≤ η := by
    intro η hη
    set S : Set (ℝ × Point n) :=
      Set.Icc (a / 2) T ×ˢ Metric.closedBall (0 : Point n) r₀ with hS_def
    have hScomp : IsCompact S := isCompact_Icc.prod (isCompact_closedBall (0 : Point n) r₀)
    have hS_sub : S ⊆ Set.Ioc 0 T ×ˢ Set.univ := by
      rintro ⟨s, z⟩ ⟨hs, _⟩
      exact ⟨⟨by have := hs.1; linarith, hs.2⟩, Set.mem_univ _⟩
    have hUC : UniformContinuousOn (fun x : ℝ × Point n => B x.1 x.2 0) S :=
      hScomp.uniformContinuousOn_of_continuous (hBcont.mono hS_sub)
    obtain ⟨δ', δ'pos, hδ'⟩ := (Metric.uniformContinuousOn_iff.1 hUC) (η / 2) (by linarith)
    obtain ⟨δ'', δ''pos, hδ''⟩ :=
      Metric.continuousAt_iff.1 hu₀cont (η / (2 * (M_B + 1))) (by positivity)
    set δ : ℝ := min r₀ (min δ'' (δ' / 2)) with hδ_def
    have hδ0 : 0 < δ := lt_min hr₀ (lt_min δ''pos (by linarith))
    have hδr₀ : δ ≤ r₀ := min_le_left _ _
    have hδδ'' : δ ≤ δ'' := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδδ' : δ < δ' :=
      lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
    refine ⟨δ, hδ0, ?_⟩
    have he1 : ∀ᶠ m in atTop, epsSeq m < δ' := epsSeq_tendsto.eventually (Iio_mem_nhds δ'pos)
    have he2 : ∀ᶠ m in atTop, epsSeq m < a / 2 :=
      epsSeq_tendsto.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [he1, he2] with m hm1 hm2
    intro u hu z hz
    have hafloor := ha_floor u hu
    have huT := hKT u hu
    have hεm := hεpos_all m
    have hs_lo : a / 2 ≤ u - epsSeq m := by linarith
    have hs_hi : u - epsSeq m ≤ T := by linarith
    have hcond : a / 2 ≤ u - epsSeq m ∧ u - epsSeq m ≤ T := ⟨hs_lo, hs_hi⟩
    have hz_r₀ : z ∈ Metric.ball (0 : Point n) r₀ := Metric.ball_subset_ball hδr₀ hz
    have hval : h m u z = u₀ z * B (u - epsSeq m) z 0 := by
      simp only [hh_def, if_pos hcond]; rw [Set.indicator_of_mem hz_r₀]
    rw [hval]
    have hBs_bd : |B (u - epsSeq m) z 0| ≤ M_B := hBstrip (u - epsSeq m) hs_lo hs_hi z
    have hu₀close : |u₀ z - 1| < η / (2 * (M_B + 1)) := by
      have hd : dist (u₀ z) (u₀ 0) < η / (2 * (M_B + 1)) :=
        hδ'' (lt_of_lt_of_le (Metric.mem_ball.1 hz) hδδ'')
      rw [Real.dist_eq, hu₀one] at hd; exact hd
    have hBclose : |B (u - epsSeq m) z 0 - B u 0 0| < η / 2 := by
      have hxS : ((u - epsSeq m, z) : ℝ × Point n) ∈ S :=
        ⟨⟨hs_lo, hs_hi⟩, Metric.ball_subset_closedBall hz_r₀⟩
      have hyS : ((u, (0 : Point n)) : ℝ × Point n) ∈ S :=
        ⟨⟨by linarith, huT⟩, by simp [Metric.mem_closedBall, hr₀.le]⟩
      have hdist : dist ((u - epsSeq m, z) : ℝ × Point n) (u, (0 : Point n)) < δ' := by
        rw [Prod.dist_eq]
        apply max_lt
        · rw [Real.dist_eq, show u - epsSeq m - u = -epsSeq m from by ring, abs_neg,
            abs_of_pos hεm]; exact hm1
        · exact lt_trans (Metric.mem_ball.1 hz) hδδ'
      have := hδ' _ hxS _ hyS hdist; rw [Real.dist_eq] at this; exact this
    calc |u₀ z * B (u - epsSeq m) z 0 - B u 0 0|
        ≤ |u₀ z * B (u - epsSeq m) z 0 - B (u - epsSeq m) z 0|
            + |B (u - epsSeq m) z 0 - B u 0 0| := by
          rw [show u₀ z * B (u - epsSeq m) z 0 - B u 0 0
              = (u₀ z * B (u - epsSeq m) z 0 - B (u - epsSeq m) z 0)
                + (B (u - epsSeq m) z 0 - B u 0 0) from by ring]
          exact abs_add_le _ _
      _ = |u₀ z - 1| * |B (u - epsSeq m) z 0| + |B (u - epsSeq m) z 0 - B u 0 0| := by
          rw [← abs_mul]; congr 2; ring
      _ ≤ η / (2 * (M_B + 1)) * M_B + η / 2 :=
          add_le_add (mul_le_mul hu₀close.le hBs_bd (abs_nonneg _) (by positivity)) hBclose.le
      _ ≤ η / 2 + η / 2 := by
          have hfrac : η / (2 * (M_B + 1)) * M_B ≤ η / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [hη.le, hMB0]
          linarith
      _ = η := by ring
  -- MAIN convergence via T2u
  have hmain : TendstoUniformlyOn
      (fun m u => ∫ z, gaussDdim (epsSeq m) z * h m u z) (fun u => B u 0 0) atTop K :=
    tendstoUniformlyOn_integral_gaussDdim_smul_family (n := n) K epsSeq hεGT h (C₀ * M_B)
      hCbd hmeas (fun u => B u 0 0) hφbd hEqui
  -- EPS / OFF decay
  set Coff : ℝ := (A₀ + A₁) * Real.sqrt (3 / 2) ^ n * M_B with hCoff_def
  have heps0 : Tendsto (fun m => epsSeq m * C₁ * M_B) atTop (𝓝 0) := by
    have := (epsSeq_tendsto.mul_const C₁).mul_const M_B; simpa using this
  have hoff0 : Tendsto
      (fun m => Coff * ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z)
      atTop (𝓝 0) := by have := hTail0.const_mul Coff; simpa using this
  -- assemble
  rw [Metric.tendstoUniformlyOn_iff]
  intro η ηpos
  rw [Metric.tendstoUniformlyOn_iff] at hmain
  have hm1ev := hmain (η / 3) (by linarith)
  have hepsev : ∀ᶠ m in atTop, epsSeq m * C₁ * M_B < η / 3 :=
    heps0.eventually (Iio_mem_nhds (by linarith))
  have hoffev : ∀ᶠ m in atTop,
      Coff * (∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z) < η / 3 :=
    hoff0.eventually (Iio_mem_nhds (by linarith))
  have hregev : ∀ᶠ m in atTop, epsSeq m < a / 2 ∧ epsSeq m < τ₀ := by
    have e1 : ∀ᶠ m in atTop, epsSeq m < a / 2 :=
      epsSeq_tendsto.eventually (Iio_mem_nhds (by linarith))
    have e2 : ∀ᶠ m in atTop, epsSeq m < τ₀ := epsSeq_tendsto.eventually (Iio_mem_nhds hτ₀)
    filter_upwards [e1, e2] with m h1 h2 using ⟨h1, h2⟩
  filter_upwards [hm1ev, hepsev, hoffev, hregev] with m hmm hepsm hoffm hregm
  intro u hu
  obtain ⟨hεa, hετ₀⟩ := hregm
  have hεm := hεpos_all m
  have hafloor := ha_floor u hu
  have huT := hKT u hu
  have hs_lo : a / 2 ≤ u - epsSeq m := by linarith
  have hs_hi : u - epsSeq m ≤ T := by linarith
  have hs_pos : 0 < u - epsSeq m := by linarith
  have hεIoo : epsSeq m ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hεm, hετ₀⟩
  -- integrability of the full integrand
  have hΦmeas : AEStronglyMeasurable
      (fun z : Point n => A (epsSeq m) 0 z * B (u - epsSeq m) z 0) volume :=
    (hAmeas (epsSeq m)).mul (hBmeas (u - epsSeq m))
  have hmaj_int : Integrable (fun z : Point n =>
      ((A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * C_L)
        * (gaussDdim (3 / 2 * epsSeq m) (0 - z) * gaussDdim (2 * (u - epsSeq m)) (z - 0)))
      volume :=
    (gaussDdim_mul_integrable (3 / 2 * epsSeq m) (2 * (u - epsSeq m)) 0 0).const_mul _
  have hΦint : Integrable
      (fun z : Point n => A (epsSeq m) 0 z * B (u - epsSeq m) z 0) volume := by
    refine Integrable.mono' hmaj_int hΦmeas (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have hA' := hAdom (epsSeq m) hεm 0 z
    have hB' := hBdom (u - epsSeq m) hs_pos hs_hi z 0
    calc |A (epsSeq m) 0 z| * |B (u - epsSeq m) z 0|
        ≤ ((A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * epsSeq m) (0 - z))
            * (C_L * gaussDdim (2 * (u - epsSeq m)) (z - 0)) :=
          mul_le_mul hA' hB' (abs_nonneg _)
            (mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hεm.le)) (by positivity))
              (gaussDdim_nonneg _ _))
      _ = ((A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * C_L)
            * (gaussDdim (3 / 2 * epsSeq m) (0 - z) * gaussDdim (2 * (u - epsSeq m)) (z - 0)) := by
          ring
  have hFsplit : (∫ z, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
      = (∫ z in Metric.ball (0 : Point n) r₀, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
        + ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0 :=
    (integral_add_compl measurableSet_ball hΦint).symm
  -- P/Q integrable on the ball
  have hPint : IntegrableOn
      (fun z => gaussDdim (epsSeq m) z * (u₀ z * B (u - epsSeq m) z 0))
      (Metric.ball (0 : Point n) r₀) volume :=
    integrableOn_gauss_mul_bddOn_ball (epsSeq m) hεm (fun z => u₀ z * B (u - epsSeq m) z 0)
      (C₀ * M_B) r₀ (hu₀meas.mul (hBmeas (u - epsSeq m)))
      (fun z hz => by
        rw [abs_mul]
        exact mul_le_mul (hu₀bdd z hz) (hBstrip (u - epsSeq m) hs_lo hs_hi z) (abs_nonneg _) hC₀0)
  have hQint : IntegrableOn
      (fun z => gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
      (Metric.ball (0 : Point n) r₀) volume :=
    integrableOn_gauss_mul_bddOn_ball (epsSeq m) hεm (fun z => u₁ z * B (u - epsSeq m) z 0)
      (C₁ * M_B) r₀ (hu₁meas.mul (hBmeas (u - epsSeq m)))
      (fun z hz => by
        rw [abs_mul]
        exact mul_le_mul (hu₁bdd z hz) (hBstrip (u - epsSeq m) hs_lo hs_hi z) (abs_nonneg _) hC₁0)
  have hball_eq : (∫ z in Metric.ball (0 : Point n) r₀, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
      = (∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z * (u₀ z * B (u - epsSeq m) z 0))
        + epsSeq m
          * ∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0) := by
    have hεQ : IntegrableOn
        (fun z => epsSeq m * (gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)))
        (Metric.ball (0 : Point n) r₀) volume := hQint.const_mul _
    rw [show epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
            gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)
          = ∫ z in Metric.ball (0 : Point n) r₀,
            epsSeq m * (gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)) from
        (integral_const_mul _ _).symm,
      ← integral_add hPint hεQ]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [hAnear (epsSeq m) hεIoo z hz]; ring
  have hMAIN_eq : (∫ z, gaussDdim (epsSeq m) z * h m u z)
      = ∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z * (u₀ z * B (u - epsSeq m) z 0) := by
    have hcond : a / 2 ≤ u - epsSeq m ∧ u - epsSeq m ≤ T := ⟨hs_lo, hs_hi⟩
    have hpt : ∀ z, gaussDdim (epsSeq m) z * h m u z
        = Set.indicator (Metric.ball (0 : Point n) r₀)
            (fun z => gaussDdim (epsSeq m) z * (u₀ z * B (u - epsSeq m) z 0)) z := by
      intro z
      simp only [hh_def, if_pos hcond]
      by_cases hz : z ∈ Metric.ball (0 : Point n) r₀
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator measurableSet_ball]
  -- EPS bound
  have hEPS_bd : |epsSeq m
        * ∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|
      ≤ epsSeq m * C₁ * M_B := by
    rw [abs_mul, abs_of_pos hεm]
    have hQabs : |∫ z in Metric.ball (0 : Point n) r₀,
          gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)| ≤ C₁ * M_B := by
      have hbd : ∀ z ∈ Metric.ball (0 : Point n) r₀,
          |gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|
            ≤ gaussDdim (epsSeq m) z * (C₁ * M_B) := by
        intro z hz
        rw [abs_mul, abs_of_nonneg (gaussDdim_nonneg _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (gaussDdim_nonneg _ _)
        rw [abs_mul]
        exact mul_le_mul (hu₁bdd z hz) (hBstrip (u - epsSeq m) hs_lo hs_hi z) (abs_nonneg _) hC₁0
      calc |∫ z in Metric.ball (0 : Point n) r₀,
              gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|
          ≤ ∫ z in Metric.ball (0 : Point n) r₀,
              |gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)| := by
            have := norm_integral_le_integral_norm
              (μ := volume.restrict (Metric.ball (0 : Point n) r₀))
              (f := fun z => gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
            simpa only [Real.norm_eq_abs] using this
        _ ≤ ∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z * (C₁ * M_B) :=
            setIntegral_mono_on hQint.abs
              ((gaussDdim_integrable (epsSeq m) hεm).mul_const _).integrableOn
              measurableSet_ball hbd
        _ = (∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z) * (C₁ * M_B) :=
            integral_mul_const _ _
        _ ≤ 1 * (C₁ * M_B) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC₁0 hMB0)
            calc ∫ z in Metric.ball (0 : Point n) r₀, gaussDdim (epsSeq m) z
                ≤ ∫ z, gaussDdim (epsSeq m) z :=
                  setIntegral_le_integral (gaussDdim_integrable _ hεm)
                    (Filter.Eventually.of_forall (fun z => gaussDdim_nonneg _ _))
              _ = 1 := gaussDdim_integral_eq_one _ hεm
        _ = C₁ * M_B := one_mul _
    calc epsSeq m * |∫ z in Metric.ball (0 : Point n) r₀,
            gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|
        ≤ epsSeq m * (C₁ * M_B) := mul_le_mul_of_nonneg_left hQabs hεm.le
      _ = epsSeq m * C₁ * M_B := by ring
  -- OFF bound
  have hOFF_bd : |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0|
      ≤ Coff * ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z := by
    have hΦbd2 : ∀ z, |A (epsSeq m) 0 z * B (u - epsSeq m) z 0|
        ≤ (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B * gaussDdim (3 / 2 * epsSeq m) (0 - z) := by
      intro z
      rw [abs_mul]
      have hA' := hAdom (epsSeq m) hεm 0 z
      have hB' := hBstrip (u - epsSeq m) hs_lo hs_hi z
      calc |A (epsSeq m) 0 z| * |B (u - epsSeq m) z 0|
          ≤ ((A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * epsSeq m) (0 - z))
              * M_B :=
            mul_le_mul hA' hB' (abs_nonneg _)
              (mul_nonneg (mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hεm.le)) (by positivity))
                (gaussDdim_nonneg _ _))
        _ = (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B * gaussDdim (3 / 2 * epsSeq m) (0 - z) := by
            ring
    have hmajint : IntegrableOn
        (fun z => (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B
          * gaussDdim (3 / 2 * epsSeq m) (0 - z))
        ((Metric.ball (0 : Point n) r₀)ᶜ) volume := by
      have hg : Integrable (fun z : Point n => gaussDdim (3 / 2 * epsSeq m) (0 - z)) volume :=
        (gaussDdim_integrable (3 / 2 * epsSeq m) (mul_pos (by norm_num) hεm)).congr
          (Filter.Eventually.of_forall (fun z => (gaussDdim_zero_sub _ z).symm))
      exact (hg.const_mul _).integrableOn
    calc |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0|
        ≤ ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, |A (epsSeq m) 0 z * B (u - epsSeq m) z 0| := by
          have := norm_integral_le_integral_norm
            (μ := volume.restrict (Metric.ball (0 : Point n) r₀)ᶜ)
            (f := fun z => A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ,
            (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B * gaussDdim (3 / 2 * epsSeq m) (0 - z) :=
          setIntegral_mono_on hΦint.integrableOn.abs hmajint measurableSet_ball.compl
            (fun z _ => hΦbd2 z)
      _ = (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B
            * ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) (0 - z) :=
          integral_const_mul _ _
      _ = (A₀ + A₁ * epsSeq m) * Real.sqrt (3 / 2) ^ n * M_B
            * ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z := by
          congr 1
          exact setIntegral_congr_fun measurableSet_ball.compl (fun z _ => gaussDdim_zero_sub _ z)
      _ ≤ Coff * ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, gaussDdim (3 / 2 * epsSeq m) z := by
          refine mul_le_mul_of_nonneg_right ?_
            (setIntegral_nonneg measurableSet_ball.compl (fun z _ => gaussDdim_nonneg _ _))
          rw [hCoff_def]
          refine mul_le_mul_of_nonneg_right ?_ hMB0
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hεle1 : epsSeq m ≤ 1 := by
            unfold epsSeq; rw [div_le_one (by positivity)]
            have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith
          nlinarith [mul_le_mul_of_nonneg_left hεle1 hA₁]
  -- final combination
  have hFval : (∫ z, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
      = (∫ z, gaussDdim (epsSeq m) z * h m u z)
        + (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
            gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
        + ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0 := by
    rw [hFsplit, hball_eq, hMAIN_eq]
  rw [Real.dist_eq, hFval]
  have hG : |B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z| < η / 3 := by
    rw [← Real.dist_eq]; exact hmm u hu
  have hE : |epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
        gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)| < η / 3 :=
    lt_of_le_of_lt hEPS_bd hepsm
  have hO : |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0|
      < η / 3 := lt_of_le_of_lt hOFF_bd hoffm
  calc |B u 0 0 - ((∫ z, gaussDdim (epsSeq m) z * h m u z)
          + (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
              gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
          + ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)|
      ≤ |B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z|
          + |epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
              gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|
          + |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0| := by
        rw [show B u 0 0 - ((∫ z, gaussDdim (epsSeq m) z * h m u z)
              + (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
                  gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
              + ∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0)
            = (B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z)
              - (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
                  gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
              - (∫ z in (Metric.ball (0 : Point n) r₀)ᶜ,
                  A (epsSeq m) 0 z * B (u - epsSeq m) z 0) from by ring]
        calc |(B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z)
              - (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
                  gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))
              - (∫ z in (Metric.ball (0 : Point n) r₀)ᶜ,
                  A (epsSeq m) 0 z * B (u - epsSeq m) z 0)|
            ≤ |(B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z)
                - (epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
                    gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0))|
              + |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ,
                    A (epsSeq m) 0 z * B (u - epsSeq m) z 0| := abs_sub _ _
          _ ≤ (|B u 0 0 - ∫ z, gaussDdim (epsSeq m) z * h m u z|
                + |epsSeq m * ∫ z in Metric.ball (0 : Point n) r₀,
                    gaussDdim (epsSeq m) z * (u₁ z * B (u - epsSeq m) z 0)|)
              + |∫ z in (Metric.ball (0 : Point n) r₀)ᶜ, A (epsSeq m) 0 z * B (u - epsSeq m) z 0| :=
                add_le_add (abs_sub _ _) (le_refl _)
    _ < η / 3 + η / 3 + η / 3 := add_lt_add (add_lt_add hG hE) hO
    _ = η := by ring

/-! ### CAP. The concrete `hDelta` with `hBoundary` GONE. -/

/-- **★★★★ J4-120 (CAP) — THE CONCRETE `hDelta`, `hBoundary` DISCHARGED.**  T3
    (`boundary_tendstoLocallyUniformlyOn`) plugged into `hDelta_gatedWitnessN1_of_boundary` for the gated
    van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S a b` and the Levi kernel
    `B := leviSeries (heatOp g gi A)`: the full `hDelta` local-uniform limit in the exact shape carried by
    `hDConv_gatedWitnessN1_of_delta_final`, with the `hBoundary` (Brick 2) carry GONE.  Its `D` is
    `fun u => DaLim u + B u 0 0`.  ⚠ CONDITIONAL only on the deferred `Da`-limit `hDaLim` PLUS the carried
    near-diagonal parametrix family (`hAnear`/`hu₀*`/`hu₁bdd`), the D1/Levi dominations (`hAdom`/`hBdom`),
    the Levi continuity `hBcont`, and base measurability (`hAmeas`/`hBmeas`/`hu₀meas`/`hu₁meas`) for the
    concrete kernels — each a genuine fact satisfiable by the concrete witness, none the conclusion.
    NOT `a₁ = R/6`. -/
theorem hDelta_gatedWitnessN1_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hC hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hC hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hC hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (Da : ℕ → ℝ → ℝ) (DaLim : ℝ → ℝ)
    (hDaLim : TendstoLocallyUniformlyOn Da DaLim atTop U) :
    TendstoLocallyUniformlyOn
      (fun m u => Da m u + ∫ z : Point n,
          vanVleckGatedWitness g gi hC hK S a b (u - (u - epsSeq m)) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
      (fun u => DaLim u
        + leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) u 0 0)
      atTop U :=
  hDelta_gatedWitnessN1_of_boundary g gi hC hK S a b U Da DaLim hDaLim
    (boundary_tendstoLocallyUniformlyOn
      (vanVleckGatedWitness g gi hC hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
      T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
      A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas)

end QIQTH.HeatResidualBound
