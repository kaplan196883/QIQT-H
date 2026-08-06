/-
  LocUnifDerivConv — J4-308: the loc-unif promotion toward `hDerivConv` (W1-free boundary side).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT — THE `hbdryLU` SLOT and WHY W1-free.

  `DerivConvDischarge.derivConv_of_data` (J4-243) builds its last carried limit `hDerivConv` from a
  loc-unif boundary member (its INTERNAL `hbdryLU`):

      `hbdryLU : TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u) (fun u => F u 0 0) atTop U`

  — the family `fun m u => BoundaryTrunc H F m u` (index `m : ℕ`, variable `u : ℝ`), limit
  `fun u => F u 0 0`, over the OPEN time set `U`, filter `atTop`.  In `derivConv_of_data` that slot is
  fed by `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, whose carry `hAnear` (the witness is
  Gaussian **at `z`**, `A τ 0 z = gaussDdim τ z · (u₀ z + τ·u₁ z)`) is the **W1 structural wall**: the
  concrete van-Vleck witness `H_G` is Gaussian at the CHART IMAGE, not at `z`, so `hAnear` is NOT
  satisfiable at a general gate (J4-267).  The W1-free replacement route (pointwise-in-`t`) is
  `EnvelopeWiringLocUnif.hBoundaryLim_DONE` ← `MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL` ←
  `MovingFBoundaryLim.hBoundaryLim_concrete` ← `GateAnnulusSplit.chartImage_approx_identity_final`.

  ## WHAT THIS FILE LANDS.

    • (L1) `movingCorr_tUniform` — ★ THE t-UNIFORM MOVING CORRECTION.  The `MovingCorrRecombination`
      3ε assembly (`movingCorr_tendsto_zero`) re-quantified UNIFORMLY over the time window `u ∈ [ta,tb]`:
      the moving-vs-frozen correction converges to `0` UNIFORMLY on `[ta,tb]`.  Kernel-agnostic.  Uses
      the t-UNIFORM sup hypothesis (satisfied by `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_-`
      `tUniform`), while the witness mass and the two Gaussian off-ball tails are `t`-free.

    • (L3) `hbdryLU_target` — the EXACT `derivConv_of_data` `hbdryLU` slot shape, named as an `abbrev`,
      for the shape-mismatch map (the slot recon is itself load-bearing).

  ## HONEST STATUS OF L2 / L4 (see file footer §REMAINING-GAP MAP):
    • (L2) the t-UNIFORM FROZEN limit — the frozen approximate identity uniform over `u ∈ [ta,tb]` — is
      the residual WALL.  `chartImage_approx_identity_final` produces a `𝓝[>]0` limit for ONE fixed `f`;
      promoting it uniformly over the `u`-family `f_u := F u · 0` needs the AI's ε-δ moduli uniform over
      `u` (a re-run of the AI assembly with the joint-continuity modulus), NOT done here.  CARRIED, named.
    • (L4) `hDerivConv` composition is blocked on L2 (and remains blocked on W1 at the untruncated-gate
      export per `DaLimLUConcreteDischarge` §"WHY THE PROVIDER-∃ EXPORT … IS NOT ATTEMPTED").

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.EnvelopeWiringLocUnif
import QIQTH.DerivConvDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.LocUnifDerivConv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (L1) — the t-UNIFORM moving correction (kernel-agnostic).
    ############################################################################### -/

/-- **★★★ (L1) `movingCorr_tUniform`.**  The `t`-UNIFORM promotion of
    `MovingCorrRecombination.movingCorr_tendsto_zero`: the moving-vs-frozen correction pairing
        `(∫ z, W(ε_m) z · fmov m u z) − ∫ z, W(ε_m) z · ffro u z`
    converges to `0` UNIFORMLY over the time window `u ∈ [ta, tb]`.  Here `fmov m u` / `ffro u` are the
    moving / frozen `F`-slices (both `u`-parametrised), `W(ε_m) = Wit(ε_m) 0 ·` the witness slice.

    Route: for fixed `m`, `u`, split each whole-space integral into `ball 0 ρ` + `(ball 0 ρ)ᶜ` via
    `integral_add_compl` (integrability from the zeroth wide domination `hDom` × the globally bounded
    slices).  The ON-ball difference `|∫_ball W(ε_m)·(fmov − ffro)| ≤ (∫_ball|W(ε_m)|)·sup ≤ CW·ε'`
    uses the `t`-UNIFORM sup `hsup` (uniform over `u ∈ [ta,tb]` AND `z ∈ ball 0 ρ`) and the eventual
    bounded witness mass `hmass` — BOTH bounds are then `u`-uniform.  The TWO OFF-ball tails
    `|∫_{ballᶜ} W(ε_m)·f| ≤ CW·Cf·∫_{ballᶜ} gaussDdim (lam·ε_m)` are `u`-free (they depend only on `m`),
    so a single eventual `< ε/3` closes them for all `u`.  3ε recombination gives `< ε` uniformly.

    Every hypothesis is satisfiable (`hsup` = `heine_timeShift_sup_tendsto_tUniform`; the bounds/mass
    are the window-uniform Levi envelope + witness domination); NONE is the conclusion.  ⚠ NOT
    `a₁ = R/6`. -/
theorem movingCorr_tUniform
    (W : ℝ → Point n → ℝ) (fmov : ℕ → ℝ → Point n → ℝ) (ffro : ℝ → Point n → ℝ)
    (ρ lam CW Cf τ₀ ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (W τ) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fmov m u) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (ffro u) volume)
    (hfmov_bdd : ∀ m u z, |fmov m u z| ≤ Cf) (hffro_bdd : ∀ u z, |ffro u z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |W (epsSeq m) z| ≤ CW)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ, |fmov m u z - ffro u z| < ε) :
    TendstoUniformlyOn
      (fun m u => (∫ z, W (epsSeq m) z * fmov m u z) - ∫ z, W (epsSeq m) z * ffro u z)
      (fun _ => (0 : ℝ)) atTop (Set.Icc ta tb) := by
  have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hffro_bdd ta 0)
  -- the (u-free) off-ball Gaussian tail along `ε_m`.
  have hc : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun τ : ℝ => lam * τ) (𝓝 (0 : ℝ)) (𝓝 (lam * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Set.mem_Ioi.mpr (mul_pos hlam (Set.mem_Ioi.mp hτ))
  have htailτ : Tendsto
      (fun τ => ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * τ) w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (QIQTH.ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero (n := n) ρ hρ).comp hscale
  have hGtail : Tendsto
      (fun m => ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) :=
    QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq htailτ
  have hub : Tendsto
      (fun m => CW * Cf * ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) := by
    have h := hGtail.const_mul (CW * Cf)
    simpa using h
  have hcap : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  have hCW1 : (0 : ℝ) < CW + 1 := by linarith
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have hε' : (0 : ℝ) < ε / (3 * (CW + 1)) := by positivity
  -- eventual: on-ball sup small, tails small, mass ≤ CW, ε_m ≤ τ₀.
  filter_upwards [hsup (ε / (3 * (CW + 1))) hε', hub.eventually (Iio_mem_nhds hε3), hmass, hcap]
    with m hsupm htailm hmassm hcapm
  -- `htailm : CW * Cf * (∫_{ballᶜ} gaussDdim (lam·ε_m)) < ε/3`
  have htailm' : CW * Cf * ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) w < ε / 3 :=
    Set.mem_Iio.mp htailm
  have hτp : 0 < epsSeq m := epsSeq_pos m
  intro u hu
  -- integrability of the two whole-space products at `(m,u)`.
  have hInt_mov : Integrable (fun z => W (epsSeq m) z * fmov m u z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hWmeas _).mul (hfmov_meas m u)) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    calc |W (epsSeq m) z| * |fmov m u z|
        ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 (hfmov_bdd m u z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  have hInt_fro : Integrable (fun z => W (epsSeq m) z * ffro u z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hWmeas _).mul (hffro_meas u)) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    calc |W (epsSeq m) z| * |ffro u z|
        ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 (hffro_bdd u z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  -- `W(ε_m)` globally integrable + `|W|` integrable.
  have hWint : Integrable (fun z => W (epsSeq m) z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul CW)
      (hWmeas _) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs]
    exact hDom (epsSeq m) hτp hcapm z
  have hWabsInt : Integrable (fun z => |W (epsSeq m) z|) volume := hWint.abs
  -- ON-ball difference bound (u-uniform via `hsupm`, mass ≤ CW).
  have honball : ‖(∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m u z)
        - ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro u z‖ < ε / 3 := by
    rw [← integral_sub hInt_mov.integrableOn hInt_fro.integrableOn]
    have hmaj : IntegrableOn (fun z => (ε / (3 * (CW + 1))) * |W (epsSeq m) z|)
        (Metric.ball (0 : Point n) ρ) volume :=
      (hWabsInt.const_mul (ε / (3 * (CW + 1)))).integrableOn
    have hbound :
        ‖∫ z in Metric.ball (0 : Point n) ρ,
              (W (epsSeq m) z * fmov m u z - W (epsSeq m) z * ffro u z)‖
          ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := by
      calc ‖∫ z in Metric.ball (0 : Point n) ρ,
                (W (epsSeq m) z * fmov m u z - W (epsSeq m) z * ffro u z)‖
          ≤ ∫ z in Metric.ball (0 : Point n) ρ,
              ‖W (epsSeq m) z * fmov m u z - W (epsSeq m) z * ffro u z‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z in Metric.ball (0 : Point n) ρ, (ε / (3 * (CW + 1))) * |W (epsSeq m) z| := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj ?_
            refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ (fun z hz => ?_))
            simp only [← mul_sub, Real.norm_eq_abs, abs_mul]
            have hzc : z ∈ Metric.closedBall (0 : Point n) ρ := Metric.ball_subset_closedBall hz
            have hlt := le_of_lt (hsupm u hu z hzc)
            calc |W (epsSeq m) z| * |fmov m u z - ffro u z|
                ≤ |W (epsSeq m) z| * (ε / (3 * (CW + 1))) :=
                  mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
              _ = (ε / (3 * (CW + 1))) * |W (epsSeq m) z| := by ring
        _ = (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := by
            rw [integral_const_mul]
    have hballmass : (∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z|) ≤ CW :=
      le_trans (setIntegral_le_integral hWabsInt (ae_of_all _ (fun z => abs_nonneg _))) hmassm
    have hfin : (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z|
        ≤ (ε / (3 * (CW + 1))) * CW :=
      mul_le_mul_of_nonneg_left hballmass (le_of_lt hε')
    have hlt' : (ε / (3 * (CW + 1))) * CW < ε / 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 3 * (CW + 1))]
      nlinarith [hε, hCW]
    calc ‖∫ z in Metric.ball (0 : Point n) ρ,
              (W (epsSeq m) z * fmov m u z - W (epsSeq m) z * ffro u z)‖
        ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := hbound
      _ ≤ (ε / (3 * (CW + 1))) * CW := hfin
      _ < ε / 3 := hlt'
  -- OFF-ball tail bounds (u-uniform: bounded by the u-free `CW·Cf·tail_m`).
  have hoffbound : ∀ f : Point n → ℝ, (∀ z, |f z| ≤ Cf) →
      AEStronglyMeasurable f volume →
      |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * f z|
        ≤ CW * Cf * ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) w := by
    intro f hfb hfm
    have hInt_f : Integrable (fun z => W (epsSeq m) z * f z) volume := by
      refine Integrable.mono'
        ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
        ((hWmeas _).mul hfm) (ae_of_all _ (fun z => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hDom (epsSeq m) hτp hcapm z
      calc |W (epsSeq m) z| * |f z|
          ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
            mul_le_mul h1 (hfb z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
        _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
    have hgint : IntegrableOn (fun z : Point n => CW * Cf * gaussDdim (lam * epsSeq m) z)
        (Metric.ball (0 : Point n) ρ)ᶜ volume :=
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf)).integrableOn
    calc |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * f z|
        ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, |W (epsSeq m) z * f z| := by
          have := norm_integral_le_integral_norm
            (μ := volume.restrict (Metric.ball (0 : Point n) ρ)ᶜ)
            (f := fun z => W (epsSeq m) z * f z)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, CW * Cf * gaussDdim (lam * epsSeq m) z := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun z => abs_nonneg _)) hgint ?_
          refine ae_of_all _ (fun z => ?_)
          dsimp only
          rw [abs_mul]
          have h1 := hDom (epsSeq m) hτp hcapm z
          have h2 := hfb z
          have hg0 := gaussDdim_nonneg (lam * epsSeq m) z
          calc |W (epsSeq m) z| * |f z| ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
                mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
            _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
      _ = CW * Cf * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) z := by
          rw [integral_const_mul]
  have hoff_mov : |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fmov m u z| < ε / 3 :=
    lt_of_le_of_lt (hoffbound (fmov m u) (fun z => hfmov_bdd m u z) (hfmov_meas m u)) htailm'
  have hoff_fro : |∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * ffro u z| < ε / 3 :=
    lt_of_le_of_lt (hoffbound (ffro u) (fun z => hffro_bdd u z) (hffro_meas u)) htailm'
  -- 3ε recombination through the two `integral_add_compl` splits.
  rw [Real.dist_eq, zero_sub, abs_neg,
      ← integral_add_compl measurableSet_ball hInt_mov,
      ← integral_add_compl measurableSet_ball hInt_fro]
  set Bm := ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m u z with hBm
  set Bf := ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro u z with hBf
  set Om := ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fmov m u z with hOm
  set Of := ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * ffro u z with hOf
  have honball' : |Bm - Bf| < ε / 3 := by rw [Real.norm_eq_abs] at honball; exact honball
  have hkey : |Bm + Om - (Bf + Of)| ≤ |Bm - Bf| + |Om| + |Of| := by
    calc |Bm + Om - (Bf + Of)| = |(Bm - Bf) + (Om - Of)| := by ring_nf
      _ ≤ |Bm - Bf| + |Om - Of| := abs_add_le _ _
      _ ≤ |Bm - Bf| + (|Om| + |Of|) := by
          have := abs_sub Om Of; linarith
      _ = |Bm - Bf| + |Om| + |Of| := by ring
  calc |Bm + Om - (Bf + Of)| ≤ |Bm - Bf| + |Om| + |Of| := hkey
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := hoff_mov; have := hoff_fro
        rw [hOm] at *; rw [hOf] at *
        linarith [honball', hoff_mov, hoff_fro]
    _ = ε := by ring

/-! ###############################################################################
    ### (L3) — THE `hbdryLU` SLOT: composition into the exact `derivConv_of_data` shape.
    ############################################################################### -/

/-- **THE EXACT `hbdryLU` SLOT SHAPE.**  `derivConv_of_data` (J4-243) constructs, internally, the
    loc-unif boundary member
        `TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u) (fun u => F u 0 0) atTop U`,
    over the OPEN time set `U`, in the time variable `u`, filter `atTop` over the truncation index `m`.
    (In `derivConv_of_data` it is named `hbdryLU`, obtained from
    `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn` — the W1 provider — after a `BoundaryTrunc`
    rewrite.)  This abbrev NAMES that target for the W1-free replacement map below.  NOT `a₁ = R/6`. -/
abbrev hbdryLUTarget (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u) (fun u => F u 0 0) atTop U

/-- **★★★ (L3) `hbdryLU_of_movingCorr_frozen`.**  THE W1-FREE `hbdryLU` COMPOSITION.  From the two
    loc-unif pieces of the boundary decomposition
        `BoundaryTrunc H F m u = (BoundaryTrunc H F m u − ∫ z, H(ε_m) 0 z · F u z 0)  +  ∫ z, H(ε_m) 0 z · F u z 0`:
      • `hmovLU` — the moving-correction term → `0` LOCALLY UNIFORMLY on `U` (the loc-unif promotion of
        (L1) `movingCorr_tUniform`, whose window-uniform engine is `t`-free in mass/tails and uses the
        `t`-uniform Heine sup `EnvelopeWiringLocUnif.heine_timeShift_sup_tendsto_tUniform`);
      • `hfroLU` — the FROZEN approximate-identity term → `F u 0 0` LOCALLY UNIFORMLY on `U` (the L2
        residual — see file footer),
    produces EXACTLY the `derivConv_of_data` slot `hbdryLUTarget H F U`.  Route: the real-valued
    loc-unif addition `HeatResidualBound.tendstoLocallyUniformlyOn_add`, then `.congr_right` (`0 + F u 0 0
    = F u 0 0`) and `.congr` (`(BT − fr) + fr = BT`).  NONE of the two hypotheses is the conclusion;
    both are genuine lower ingredients.  ⚠ NOT `a₁ = R/6`. -/
theorem hbdryLU_of_movingCorr_frozen
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (hmovLU : TendstoLocallyUniformlyOn
        (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) 0 z * F u z 0)
        (fun _ => (0 : ℝ)) atTop U)
    (hfroLU : TendstoLocallyUniformlyOn
        (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0)
        (fun u => F u 0 0) atTop U) :
    hbdryLUTarget H F U := by
  have hadd := QIQTH.HeatResidualBound.tendstoLocallyUniformlyOn_add hmovLU hfroLU
  -- fix the limit: `0 + F u 0 0 = F u 0 0`.
  have hstep := hadd.congr_right (g := fun u => F u 0 0) (fun u _ => by rw [zero_add])
  -- fix the family: `(BoundaryTrunc − frozen) + frozen = BoundaryTrunc`.
  exact hstep.congr (fun m u _ => by ring)

end QIQTH.LocUnifDerivConv

section AxiomChecks
open QIQTH.LocUnifDerivConv
#print axioms movingCorr_tUniform
#print axioms hbdryLU_of_movingCorr_frozen
end AxiomChecks
