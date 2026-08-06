/-
  MovingCorrRecombination — J4-306: the moving-correction recombination (B2).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

  The J4-305 `BoundaryLimAssembly.hBoundaryLim_ASSEMBLED` carries ONE opaque limit — the labelled
  moving-correction
      `hMovingCorr : Tendsto (fun m => BoundaryTrunc Wit F m t
                        − ∫ z, Wit (ε_m) 0 z · F t z 0) atTop (𝓝 0)`.
  This file DISCHARGES that carry into named, satisfiable sub-facts, recombining it from:

    • (R3) `offBall_seq_tendsto_zero` — the OFF-ball tail (along `ε_m`) vanishes for ANY uniformly
      bounded (possibly `m`-dependent) `fseq`, from the zeroth wide domination + Gaussian tail squeeze.
      Handles BOTH tails (moving `F(t−ε_m)` and frozen `F t`) with one lemma.

    • (R2) `onBallDiff_tendsto_zero` — the ON-ball difference vanishes:
      `|∫_ball Wit(ε_m)·(F(t−ε_m) − F t)| ≤ (∫|Wit(ε_m)|)·sup_ball|F(t−ε_m) − F t| ≤ CW·ε` eventually,
      from the eventual bounded mass (`MovingCorrAssembly.epsSeq_witnessSlice_mass_eventually_le`) and
      the eventual-uniform sup limit (`BoundaryLimAssembly.heine_timeShift_sup_tendsto`).

    • (R1+R4) `movingCorr_tendsto_zero` — the 3ε assembly: per-`m` `integral_add_compl` split
      (integrability from the zeroth domination × the bounded `F`-slices) recombines the two tails and
      the on-ball difference; `Tendsto.add`/`.sub` closes it to `→ 0`.  KERNEL-AGNOSTIC.

    • (R5) `hBoundaryLim_FULLY_INTERNAL` — `hBoundaryLim_ASSEMBLED` with `hMovingCorr` INTERNALISED
      (proven from the FINAL joint continuity via (R2)'s Heine sup, the banked witness mass, and the
      global window-uniform `F`-bound + moving-slice measurability which are the two truly-final
      satisfiable carries).  The truly-final input list is stated in its docstring.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.BoundaryLimAssembly
import QIQTH.GateAnnulusSplit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.ExpMap
open scoped Topology

namespace QIQTH.MovingCorrRecombination

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (R3) — the off-ball tail (sequence form, uniformly-bounded `m`-dependent `f`).
    ############################################################################### -/

/-- **★★ (R3) `offBall_seq_tendsto_zero`.**  Sequence-form off-ball vanishing limit for a zeroth-wide-
    dominated kernel slice `W` paired with a UNIFORMLY (over `m`) bounded, possibly `m`-dependent,
    family `fseq`:
        `Tendsto (fun m => ∫ z in (ball 0 ρ)ᶜ, W (ε_m) z · fseq m z) atTop (𝓝 0)`.
    Route: `‖∫_{ballᶜ} W(ε_m)·fseq m‖ ≤ CW·Cf·∫_{ballᶜ} gaussDdim (lam·ε_m)`, the last factor → 0 by the
    width-`(lam·ε_m)` Gaussian tail (`ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero`
    reparametrised through `τ↦lam·τ`, sequenced via `MovingFBoundaryLim.tendsto_comp_epsSeq`); squeeze.
    Kernel-agnostic; the `m`-dependence of `fseq` is why the fixed-`f` `GateAnnulusSplit` tail does not
    directly apply to the moving slice.  ⚠ NOT `a₁ = R/6`. -/
theorem offBall_seq_tendsto_zero
    (W : ℝ → Point n → ℝ) (fseq : ℕ → Point n → ℝ)
    (ρ lam CW Cf τ₀ : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hfb : ∀ m z, |fseq m z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto (fun m => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fseq m z)
      atTop (𝓝 0) := by
  have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hfb 0 0)
  -- Width reparametrisation `τ ↦ lam·τ` preserves `𝓝[>]0`.
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
  refine squeeze_zero_norm' ?_ hub
  filter_upwards [hcap] with m hττ₀
  have hτp : 0 < epsSeq m := epsSeq_pos m
  have hgint : IntegrableOn (fun z : Point n => CW * Cf * gaussDdim (lam * epsSeq m) z)
      (Metric.ball (0 : Point n) ρ)ᶜ volume :=
    ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf)).integrableOn
  calc ‖∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fseq m z‖
      ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, ‖W (epsSeq m) z * fseq m z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, CW * Cf * gaussDdim (lam * epsSeq m) z := by
        refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hgint ?_
        refine ae_of_all _ (fun z => ?_)
        simp only [Real.norm_eq_abs, abs_mul]
        have h1 := hDom (epsSeq m) hτp hττ₀ z
        have h2 := hfb m z
        have hg0 := gaussDdim_nonneg (lam * epsSeq m) z
        have hstep : |W (epsSeq m) z| * |fseq m z| ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
        calc |W (epsSeq m) z| * |fseq m z| ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf := hstep
          _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
    _ = CW * Cf * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * epsSeq m) z := by
        rw [integral_const_mul]

/-! ###############################################################################
    ### (R2) — the on-ball difference vanishes (bounded mass × uniform sup).
    ############################################################################### -/

/-- **★★ (R2) `onBallDiff_tendsto_zero`.**  The ON-ball moving-vs-frozen difference vanishes:
        `Tendsto (fun m => (∫ z in ball 0 ρ, W(ε_m) z · fmov m z)
                            − ∫ z in ball 0 ρ, W(ε_m) z · ffro z) atTop (𝓝 0)`.
    Estimate: `|∫_ball W(ε_m)·(fmov − ffro)| ≤ (∫|W(ε_m)|)·sup_ball|fmov − ffro| ≤ CW·ε'` eventually.
    Inputs: the eventual bounded witness mass `hmass` (`∫ z, |W(ε_m) z| ≤ CW`, from
    `MovingCorrAssembly.epsSeq_witnessSlice_mass_eventually_le`); the eventual-uniform sup limit `hsup`
    (from `BoundaryLimAssembly.heine_timeShift_sup_tendsto`); the zeroth wide domination `hDom`
    (for on-ball integrability) plus measurability + global boundedness of the `F`-slices.
    Kernel-agnostic.  ⚠ NOT `a₁ = R/6`. -/
theorem onBallDiff_tendsto_zero
    (W : ℝ → Point n → ℝ) (fmov : ℕ → Point n → ℝ) (ffro : Point n → ℝ)
    (ρ lam CW Cf τ₀ : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (W τ) volume)
    (hfmov_meas : ∀ m, AEStronglyMeasurable (fmov m) volume)
    (hffro_meas : AEStronglyMeasurable ffro volume)
    (hfmov_bdd : ∀ m z, |fmov m z| ≤ Cf) (hffro_bdd : ∀ z, |ffro z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |W (epsSeq m) z| ≤ CW)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
        |fmov m z - ffro z| < ε) :
    Tendsto (fun m => (∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m z)
        - ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro z)
      atTop (𝓝 0) := by
  have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hffro_bdd 0)
  have hcap : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  have hCW1 : (0 : ℝ) < CW + 1 := by linarith
  refine Metric.tendsto_atTop.2 (fun ε hε => ?_)
  have hε' : 0 < ε / (CW + 1) := div_pos hε hCW1
  have hev : ∀ᶠ m in atTop,
      dist ((∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m z)
        - ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro z) 0 < ε := by
    filter_upwards [hsup (ε / (CW + 1)) hε', hmass, hcap] with m hsupm hmassm hcapm
    have hτp : 0 < epsSeq m := epsSeq_pos m
    -- global integrability of `W(ε_m)` (from the domination).
    have hWint : Integrable (fun z => W (epsSeq m) z) volume := by
      refine Integrable.mono'
        ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul CW)
        (hWmeas _) (ae_of_all _ (fun z => ?_))
      rw [Real.norm_eq_abs]
      exact hDom (epsSeq m) hτp hcapm z
    have hWabsInt : Integrable (fun z => |W (epsSeq m) z|) volume := hWint.abs
    -- global integrability of the two products.
    have hInt_mov : Integrable (fun z => W (epsSeq m) z * fmov m z) volume := by
      refine Integrable.mono'
        ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
        ((hWmeas _).mul (hfmov_meas m)) (ae_of_all _ (fun z => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hDom (epsSeq m) hτp hcapm z
      calc |W (epsSeq m) z| * |fmov m z|
          ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
            mul_le_mul h1 (hfmov_bdd m z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
        _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
    have hInt_fro : Integrable (fun z => W (epsSeq m) z * ffro z) volume := by
      refine Integrable.mono'
        ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
        ((hWmeas _).mul hffro_meas) (ae_of_all _ (fun z => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hDom (epsSeq m) hτp hcapm z
      calc |W (epsSeq m) z| * |ffro z|
          ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
            mul_le_mul h1 (hffro_bdd z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
        _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
    -- combine the two on-ball integrals.
    rw [dist_zero_right, ← integral_sub hInt_mov.integrableOn hInt_fro.integrableOn]
    have hmaj : IntegrableOn (fun z => (ε / (CW + 1)) * |W (epsSeq m) z|)
        (Metric.ball (0 : Point n) ρ) volume :=
      (hWabsInt.const_mul (ε / (CW + 1))).integrableOn
    have hbound :
        ‖∫ z in Metric.ball (0 : Point n) ρ,
              (W (epsSeq m) z * fmov m z - W (epsSeq m) z * ffro z)‖
          ≤ (ε / (CW + 1)) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := by
      calc ‖∫ z in Metric.ball (0 : Point n) ρ,
                (W (epsSeq m) z * fmov m z - W (epsSeq m) z * ffro z)‖
          ≤ ∫ z in Metric.ball (0 : Point n) ρ,
              ‖W (epsSeq m) z * fmov m z - W (epsSeq m) z * ffro z‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z in Metric.ball (0 : Point n) ρ, (ε / (CW + 1)) * |W (epsSeq m) z| := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj ?_
            refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ (fun z hz => ?_))
            simp only [← mul_sub, Real.norm_eq_abs, abs_mul]
            have hzc : z ∈ Metric.closedBall (0 : Point n) ρ :=
              Metric.ball_subset_closedBall hz
            have hlt := le_of_lt (hsupm z hzc)
            calc |W (epsSeq m) z| * |fmov m z - ffro z|
                ≤ |W (epsSeq m) z| * (ε / (CW + 1)) :=
                  mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
              _ = (ε / (CW + 1)) * |W (epsSeq m) z| := by ring
        _ = (ε / (CW + 1)) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := by
            rw [integral_const_mul]
    -- `∫_ball |W| ≤ ∫ |W| ≤ CW`, then `ε'·CW < ε`.
    have hballmass : (∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z|) ≤ CW :=
      le_trans (setIntegral_le_integral hWabsInt (ae_of_all _ (fun z => abs_nonneg _))) hmassm
    have hfin : (ε / (CW + 1)) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z|
        ≤ (ε / (CW + 1)) * CW :=
      mul_le_mul_of_nonneg_left hballmass (le_of_lt hε')
    have hlt' : (ε / (CW + 1)) * CW < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hCW1]
      nlinarith [hε, hCW]
    calc ‖∫ z in Metric.ball (0 : Point n) ρ,
              (W (epsSeq m) z * fmov m z - W (epsSeq m) z * ffro z)‖
        ≤ (ε / (CW + 1)) * ∫ z in Metric.ball (0 : Point n) ρ, |W (epsSeq m) z| := hbound
      _ ≤ (ε / (CW + 1)) * CW := hfin
      _ < ε := hlt'
  exact eventually_atTop.mp hev

/-! ###############################################################################
    ### (R1+R4) — the 3ε recombination (kernel-agnostic).
    ############################################################################### -/

/-- **★★★ (R1+R4) `movingCorr_tendsto_zero`.**  The full moving-correction limit, kernel-agnostic:
        `Tendsto (fun m => (∫ z, W(ε_m) z · fmov m z) − ∫ z, W(ε_m) z · ffro z) atTop (𝓝 0)`.
    Route: per-`m` `integral_add_compl` splits each whole-space integral into `ball 0 ρ` + `(ball 0 ρ)ᶜ`
    (integrability from the zeroth wide domination × the globally bounded `F`-slices); the on-ball
    difference → 0 by (R2) `onBallDiff_tendsto_zero`, and both off-ball tails → 0 by (R3)
    `offBall_seq_tendsto_zero` (the moving tail uses the UNIFORM-in-`m` bound `hfmov_bdd`, the frozen tail
    the constant bound `hffro_bdd`).  `Tendsto.add`/`.sub` close it, transferred through the split
    identity by `Tendsto.congr'`.  ⚠ NOT `a₁ = R/6`. -/
theorem movingCorr_tendsto_zero
    (W : ℝ → Point n → ℝ) (fmov : ℕ → Point n → ℝ) (ffro : Point n → ℝ)
    (ρ lam CW Cf τ₀ : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (W τ) volume)
    (hfmov_meas : ∀ m, AEStronglyMeasurable (fmov m) volume)
    (hffro_meas : AEStronglyMeasurable ffro volume)
    (hfmov_bdd : ∀ m z, |fmov m z| ≤ Cf) (hffro_bdd : ∀ z, |ffro z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |W (epsSeq m) z| ≤ CW)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
        |fmov m z - ffro z| < ε) :
    Tendsto (fun m => (∫ z, W (epsSeq m) z * fmov m z) - ∫ z, W (epsSeq m) z * ffro z)
      atTop (𝓝 0) := by
  have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hffro_bdd 0)
  have hcap : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  -- the three pieces.
  have htail_mov : Tendsto
      (fun m => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fmov m z)
      atTop (𝓝 0) :=
    offBall_seq_tendsto_zero W fmov ρ lam CW Cf τ₀ hρ hlam hCW hτ₀ hfmov_bdd hDom
  have htail_fro : Tendsto
      (fun m => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * ffro z)
      atTop (𝓝 0) :=
    offBall_seq_tendsto_zero W (fun _ => ffro) ρ lam CW Cf τ₀ hρ hlam hCW hτ₀
      (fun m z => hffro_bdd z) hDom
  have honball : Tendsto
      (fun m => (∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m z)
        - ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro z)
      atTop (𝓝 0) :=
    onBallDiff_tendsto_zero W fmov ffro ρ lam CW Cf τ₀ hρ hlam hCW hτ₀ hWmeas hfmov_meas
      hffro_meas hfmov_bdd hffro_bdd hDom hmass hsup
  -- the combined tendsto (→ 0+0-0).
  have hg : Tendsto
      (fun m => ((∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * fmov m z)
            - ∫ z in Metric.ball (0 : Point n) ρ, W (epsSeq m) z * ffro z)
          + (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * fmov m z)
          - (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, W (epsSeq m) z * ffro z))
      atTop (𝓝 0) := by
    have h := (honball.add htail_mov).sub htail_fro
    simpa using h
  -- the split identity (eventually, via `integral_add_compl`).
  refine hg.congr' ?_
  filter_upwards [hcap] with m hcapm
  have hτp : 0 < epsSeq m := epsSeq_pos m
  have hInt_mov : Integrable (fun z => W (epsSeq m) z * fmov m z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hWmeas _).mul (hfmov_meas m)) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    calc |W (epsSeq m) z| * |fmov m z|
        ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 (hfmov_bdd m z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  have hInt_fro : Integrable (fun z => W (epsSeq m) z * ffro z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hWmeas _).mul hffro_meas) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    calc |W (epsSeq m) z| * |ffro z|
        ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 (hffro_bdd z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  rw [← integral_add_compl measurableSet_ball hInt_mov,
      ← integral_add_compl measurableSet_ball hInt_fro]
  ring

/-! ###############################################################################
    ### (R5) — `hBoundaryLim` with `hMovingCorr` INTERNALISED.
    ############################################################################### -/

/-- **★★★ (R5) `hBoundaryLim_FULLY_INTERNAL`.**  The boundary-limit member of the truncated-Duhamel
    pile at the concrete van-Vleck gate, with the J4-305 `hMovingCorr` carry now PROVEN internally (via
    (R1)–(R4) above), so it is no longer an assumed limit.  Concludes
        `Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
    `Wit := vanVleckGatedWitness g gi hC hK S a b`,  `F := leviSeries (heatOp g gi Wit)`.

    `hMovingCorr` is discharged from: the FINAL joint continuity (⟹ `hf_cont` via (B3) AND the Heine
    eventual-uniform sup `hsup` via (B1)); the banked eventual witness mass
    (`MovingCorrAssembly.epsSeq_witnessSlice_mass_eventually_le`, from `hDom`); and the two truly-final
    satisfiable data below.

    ── TRULY-FINAL HONEST INPUT LIST (none is the conclusion; all satisfiable, none `hMovingCorr`):
      • standing geometry / metric / gauge — `hC, hK, h0Kmem, hg, hgi, hgpos, hgdet0`;
      • gate data — `S, a, b, ha, hab`; strip `0 < t₁ < t < t₂`, `0 < R`;
      • the FINAL's continuity bundle — `κ, Cc, hκ, hCc0, hEbound, hInt, hEmeas, hbase, hgeoBundle,
        hfgBundle, env, hu, hbound` (⟹ joint `(s,z)`-continuity of the Levi `0`-slice);
      • the frozen-slice measurability `hf_meas` (banked via
        `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise`);
      • gate-activation carries `rS, hrS, hKball, hSact` + witness-slice measurability `hWslice`; the
        zeroth wide domination `lam, τ₀, CW, hlam, hτ₀, hCW, hDom`;
      • ★ THE TWO NEW SATISFIABLE CARRIES that discharge `hMovingCorr` (replacing the opaque limit):
          – `hFmov_bdd` / `hFfro_bdd` : a SINGLE window-uniform global bound
            `|F (t − ε_m) z 0| ≤ Cf` (∀ m, z) and `|F t z 0| ≤ Cf` (∀ z).  Banked provider: the Levi
            envelope `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated` (× the Gaussian diagonal),
            which bounds `|F s · 0|` uniformly for `s` in the time window `[t/2, t]`.
          – `hfmov_meas` : measurability of the moving Levi slice `z ↦ F (t − ε_m) z 0`.  Banked provider:
            `LeviSeriesLocalData.leviSeries_stronglyMeasurable_of_termwise` (same as `hf_meas`).
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem hBoundaryLim_FULLY_INTERNAL
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (κ Cc : ℝ) (hκ : 0 < κ) (hCc0 : 0 ≤ Cc)
    (t₁ t₂ R t : ℝ) (ht₁pos : 0 < t₁) (hlt₁ : t₁ < t) (hlt₂ : t < t₂) (hR : 0 < R)
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q| ≤ Cc * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ 0 Cc)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hgeoBundle : ∀ w ∈ K, ∃ ρc cw ρ₀w C_Dw : ℝ,
      0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) ∧
      S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
      0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
        ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
      closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
        ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
      cw + C_Dw * cw * cw < ρc)
    (hfgBundle : ∀ w ∈ K, ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∃ Rg cw ρ₀w C_Dw : ℝ,
        0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
        S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
        0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
        (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
          ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
        closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
          ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
        (∀ v : Point n, ‖v‖ ≤ cw →
          uniformInverseChart g gi hC hK w (uniformFlowExp g gi hC hK w v) = v) ∧
        b + C_Dw * b * b < Rg)
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k)
    (hf_meas : Measurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0))
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    -- ★ the two new satisfiable carries discharging `hMovingCorr`:
    (Cf : ℝ)
    (hFmov_bdd : ∀ m z,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (t - epsSeq m) z 0| ≤ Cf)
    (hFfro_bdd : ∀ z,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0| ≤ Cf)
    (hfmov_meas : ∀ m, AEStronglyMeasurable
      (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (t - epsSeq m) z 0)
      volume) :
    Tendsto
      (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) m t)
      atTop
      (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t 0 0)) := by
  -- joint continuity from the FINAL (computed once).
  have hjoint := QIQTH.GateGeometryResiduals.leviSlice_hf_cont_FINAL
    g gi hC hK S a b ha hab κ Cc hκ hCc0 t₁ t₂ R ht₁pos (le_of_lt (lt_trans hlt₁ hlt₂)) hR
    hEbound hInt hEmeas hbase hgeoBundle hfgBundle env hu hbound
  -- `hf_cont` via (B3).
  have hf_cont := QIQTH.BoundaryLimAssembly.frozenSlice_continuousAt_zero_of_jointContinuousOn
    (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
    t₁ t₂ R t hlt₁ hlt₂ hR hjoint
  -- the eventual witness mass (banked from `hDom`).
  have hmass := QIQTH.MovingCorrAssembly.epsSeq_witnessSlice_mass_eventually_le
    (fun τ z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z)
    lam CW τ₀ hlam hCW hτ₀ hDom
  -- the Heine eventual-uniform sup (B1) at radius `R`.
  have hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ z ∈ Metric.closedBall (0 : Point n) R,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (t - epsSeq m) z 0
          - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0| < ε :=
    fun ε hε => QIQTH.BoundaryLimAssembly.heine_timeShift_sup_tendsto
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      t₁ t₂ R R t (le_refl R) hlt₁ (le_of_lt hlt₂) hjoint ε hε
  -- the moving-correction limit (R1–R4).
  have hMC := movingCorr_tendsto_zero
    (fun τ z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z)
    (fun m z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (t - epsSeq m) z 0)
    (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0)
    R lam CW Cf τ₀ hR hlam hCW hτ₀ hWslice hfmov_meas hf_meas.aestronglyMeasurable
    hFmov_bdd hFfro_bdd hDom hmass hsup
  -- rewrite `BoundaryTrunc` into the moving-correction shape.
  have hMovingCorr : Tendsto
      (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) m t
          - ∫ z, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) (0 : Point n) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) t z 0)
      atTop (𝓝 0) := by
    refine hMC.congr' (Filter.Eventually.of_forall (fun m => ?_))
    simp only [BoundaryTrunc, sub_sub_cancel]
  -- feed the (HB) recombination.
  exact QIQTH.MovingFBoundaryLim.hBoundaryLim_concrete
    g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0 t
    hf_meas ⟨Cf, hFfro_bdd⟩ hf_cont rS hrS hKball hSact hWslice
    lam τ₀ CW hlam hτ₀ hCW hDom hMovingCorr

#check @offBall_seq_tendsto_zero
#check @onBallDiff_tendsto_zero
#check @movingCorr_tendsto_zero
#check @hBoundaryLim_FULLY_INTERNAL

end QIQTH.MovingCorrRecombination

section AxiomChecks
open QIQTH.MovingCorrRecombination
#print axioms offBall_seq_tendsto_zero
#print axioms onBallDiff_tendsto_zero
#print axioms movingCorr_tendsto_zero
#print axioms hBoundaryLim_FULLY_INTERNAL
end AxiomChecks
